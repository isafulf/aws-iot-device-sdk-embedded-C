import sys

def main():
    argList = sys.argv
    rd = open(argList[2], "r")
    
    out = [] 
    longDashedLine = "--------------------------------------------------------------------------------"
    startFunction = False
    secondDashLine = False
    function = "--- Properties of Function \'" + argList[1]
    while True:
        # Read next line
        line = rd.readline()
        # If line is blank, then you struck the EOF
        if not line :
            break
        
        if startFunction:
            if longDashedLine in line:
                if not secondDashLine:
                    secondDashLine = True
                    out.append(line.strip())
                else:
                    out.append(line.strip())
                    break
            else:
               out.append(line.strip()) 
        elif function in line:
            startFunction = True 
            out.append(longDashedLine)
            out.append(line.strip())

     
    rd.close()
    
    for line in out:
        print(line.strip())    


if __name__ == "__main__":
    main()
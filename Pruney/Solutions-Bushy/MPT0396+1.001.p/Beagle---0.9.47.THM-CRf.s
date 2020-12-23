%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0396+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:14 EST 2020

% Result     : Theorem 48.11s
% Output     : CNFRefutation 48.17s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  82 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k3_tarski > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(c_34,plain,(
    ~ r1_tarski(k3_tarski('#skF_8'),k3_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    r1_setfam_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_18,C_33] :
      ( r2_hidden('#skF_7'(A_18,k3_tarski(A_18),C_33),A_18)
      | ~ r2_hidden(C_33,k3_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_11,A_1,B_2] :
      ( r1_tarski(C_11,'#skF_2'(A_1,B_2,C_11))
      | ~ r2_hidden(C_11,A_1)
      | ~ r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [C_53,A_54] :
      ( r2_hidden(C_53,'#skF_7'(A_54,k3_tarski(A_54),C_53))
      | ~ r2_hidden(C_53,k3_tarski(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [C_17,B_14,A_13] :
      ( r2_hidden(C_17,B_14)
      | ~ r2_hidden(C_17,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_229,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r1_tarski('#skF_7'(A_89,k3_tarski(A_89),C_87),B_88)
      | ~ r2_hidden(C_87,k3_tarski(A_89)) ) ),
    inference(resolution,[status(thm)],[c_66,c_10])).

tff(c_46536,plain,(
    ! [C_1825,A_1826,B_1827,A_1828] :
      ( r2_hidden(C_1825,'#skF_2'(A_1826,B_1827,'#skF_7'(A_1828,k3_tarski(A_1828),C_1825)))
      | ~ r2_hidden(C_1825,k3_tarski(A_1828))
      | ~ r2_hidden('#skF_7'(A_1828,k3_tarski(A_1828),C_1825),A_1826)
      | ~ r1_setfam_1(A_1826,B_1827) ) ),
    inference(resolution,[status(thm)],[c_2,c_229])).

tff(c_105,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_2'(A_65,B_66,C_67),B_66)
      | ~ r2_hidden(C_67,A_65)
      | ~ r1_setfam_1(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [C_33,A_18,D_36] :
      ( r2_hidden(C_33,k3_tarski(A_18))
      | ~ r2_hidden(D_36,A_18)
      | ~ r2_hidden(C_33,D_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_110,plain,(
    ! [C_33,B_66,A_65,C_67] :
      ( r2_hidden(C_33,k3_tarski(B_66))
      | ~ r2_hidden(C_33,'#skF_2'(A_65,B_66,C_67))
      | ~ r2_hidden(C_67,A_65)
      | ~ r1_setfam_1(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_105,c_16])).

tff(c_79834,plain,(
    ! [C_2504,B_2505,A_2506,A_2507] :
      ( r2_hidden(C_2504,k3_tarski(B_2505))
      | ~ r2_hidden(C_2504,k3_tarski(A_2506))
      | ~ r2_hidden('#skF_7'(A_2506,k3_tarski(A_2506),C_2504),A_2507)
      | ~ r1_setfam_1(A_2507,B_2505) ) ),
    inference(resolution,[status(thm)],[c_46536,c_110])).

tff(c_79888,plain,(
    ! [C_2508,B_2509,A_2510] :
      ( r2_hidden(C_2508,k3_tarski(B_2509))
      | ~ r1_setfam_1(A_2510,B_2509)
      | ~ r2_hidden(C_2508,k3_tarski(A_2510)) ) ),
    inference(resolution,[status(thm)],[c_18,c_79834])).

tff(c_80498,plain,(
    ! [C_2511] :
      ( r2_hidden(C_2511,k3_tarski('#skF_9'))
      | ~ r2_hidden(C_2511,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_36,c_79888])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81308,plain,(
    ! [A_2515] :
      ( r1_tarski(A_2515,k3_tarski('#skF_9'))
      | ~ r2_hidden('#skF_3'(A_2515,k3_tarski('#skF_9')),k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_80498,c_12])).

tff(c_81372,plain,(
    r1_tarski(k3_tarski('#skF_8'),k3_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_14,c_81308])).

tff(c_81391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_81372])).

%------------------------------------------------------------------------------

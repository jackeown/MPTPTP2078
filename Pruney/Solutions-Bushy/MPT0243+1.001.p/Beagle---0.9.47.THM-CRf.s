%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0243+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:58 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 181 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 363 expanded)
%              Number of equality atoms :   19 (  46 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_tarski > #nlpp > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_30,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [C_24,B_25,A_26] :
      ( r2_hidden(C_24,B_25)
      | ~ r2_hidden(C_24,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_101,plain,(
    ! [D_31,B_32,B_33] :
      ( r2_hidden(D_31,B_32)
      | ~ r1_tarski(k2_tarski(D_31,B_33),B_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_108,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_39,c_101])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_108])).

tff(c_116,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_115,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_117,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    ! [D_38,B_39,A_40] :
      ( r2_hidden(D_38,B_39)
      | ~ r1_tarski(k2_tarski(A_40,D_38),B_39) ) ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_150,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_39,c_143])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_150])).

tff(c_158,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_26,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_233,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_158,c_26])).

tff(c_28,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_158,c_28])).

tff(c_157,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_49,plain,(
    ! [D_21,B_22,A_23] :
      ( D_21 = B_22
      | D_21 = A_23
      | ~ r2_hidden(D_21,k2_tarski(A_23,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1989,plain,(
    ! [A_1729,B_1730,B_1731] :
      ( '#skF_3'(k2_tarski(A_1729,B_1730),B_1731) = B_1730
      | '#skF_3'(k2_tarski(A_1729,B_1730),B_1731) = A_1729
      | r1_tarski(k2_tarski(A_1729,B_1730),B_1731) ) ),
    inference(resolution,[status(thm)],[c_24,c_49])).

tff(c_2209,plain,
    ( '#skF_3'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5'
    | '#skF_3'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1989,c_233])).

tff(c_2211,plain,(
    '#skF_3'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2209])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2224,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2211,c_22])).

tff(c_2324,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_2224])).

tff(c_2326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_2324])).

tff(c_2327,plain,(
    '#skF_3'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2209])).

tff(c_2341,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2327,c_22])).

tff(c_2441,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_2341])).

tff(c_2443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_2441])).

tff(c_2445,plain,(
    ~ r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_32,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2525,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2445,c_32])).

tff(c_34,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2446,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_2447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2445,c_2446])).

tff(c_2448,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2444,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2490,plain,(
    ! [D_1835,B_1836,A_1837] :
      ( D_1835 = B_1836
      | D_1835 = A_1837
      | ~ r2_hidden(D_1835,k2_tarski(A_1837,B_1836)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4030,plain,(
    ! [A_3088,B_3089,B_3090] :
      ( '#skF_3'(k2_tarski(A_3088,B_3089),B_3090) = B_3089
      | '#skF_3'(k2_tarski(A_3088,B_3089),B_3090) = A_3088
      | r1_tarski(k2_tarski(A_3088,B_3089),B_3090) ) ),
    inference(resolution,[status(thm)],[c_24,c_2490])).

tff(c_4243,plain,
    ( '#skF_3'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5'
    | '#skF_3'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4030,c_2525])).

tff(c_4247,plain,(
    '#skF_3'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4243])).

tff(c_4257,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4247,c_22])).

tff(c_4356,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_4257])).

tff(c_4358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2525,c_4356])).

tff(c_4359,plain,(
    '#skF_3'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4243])).

tff(c_4370,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4359,c_22])).

tff(c_4469,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_4370])).

tff(c_4471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2525,c_4469])).

%------------------------------------------------------------------------------

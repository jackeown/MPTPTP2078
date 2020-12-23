%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0077+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:40 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 273 expanded)
%              Number of leaves         :   19 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  160 ( 715 expanded)
%              Number of equality atoms :    3 (  35 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_140,plain,(
    ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_157,plain,(
    ! [D_35,B_36,A_37] :
      ( r2_hidden(D_35,B_36)
      | r2_hidden(D_35,A_37)
      | ~ r2_hidden(D_35,k2_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_250,plain,(
    ! [A_50,B_51,B_52] :
      ( r2_hidden('#skF_3'(k2_xboole_0(A_50,B_51),B_52),B_51)
      | r2_hidden('#skF_3'(k2_xboole_0(A_50,B_51),B_52),A_50)
      | r1_xboole_0(k2_xboole_0(A_50,B_51),B_52) ) ),
    inference(resolution,[status(thm)],[c_26,c_157])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_39,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5'))
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_84,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_94,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,B_27)
      | ~ r2_hidden(C_28,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    ! [C_30] :
      ( ~ r2_hidden(C_30,'#skF_8')
      | ~ r2_hidden(C_30,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_84,c_94])).

tff(c_122,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_3'(A_9,'#skF_7'),'#skF_8')
      | r1_xboole_0(A_9,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_24,c_112])).

tff(c_764,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_3'(k2_xboole_0(A_67,'#skF_8'),'#skF_7'),A_67)
      | r1_xboole_0(k2_xboole_0(A_67,'#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_250,c_122])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5'))
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_92,plain,(
    r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_101,plain,(
    ! [C_29] :
      ( ~ r2_hidden(C_29,'#skF_9')
      | ~ r2_hidden(C_29,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_92,c_94])).

tff(c_111,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_3'(A_9,'#skF_7'),'#skF_9')
      | r1_xboole_0(A_9,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_24,c_101])).

tff(c_792,plain,(
    r1_xboole_0(k2_xboole_0('#skF_9','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_764,c_111])).

tff(c_826,plain,(
    r1_xboole_0(k2_xboole_0('#skF_8','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_792])).

tff(c_22,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,B_10)
      | ~ r2_hidden(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_836,plain,(
    ! [C_68] :
      ( ~ r2_hidden(C_68,'#skF_7')
      | ~ r2_hidden(C_68,k2_xboole_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_826,c_22])).

tff(c_2459,plain,(
    ! [A_105] :
      ( ~ r2_hidden('#skF_3'(A_105,k2_xboole_0('#skF_8','#skF_9')),'#skF_7')
      | r1_xboole_0(A_105,k2_xboole_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_24,c_836])).

tff(c_2471,plain,(
    r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_26,c_2459])).

tff(c_2477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_140,c_2471])).

tff(c_2478,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2483,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2478])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( ~ r2_hidden(D_8,A_3)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2479,plain,(
    r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5'))
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_2515,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2479,c_41])).

tff(c_2519,plain,(
    ! [C_108] :
      ( ~ r2_hidden(C_108,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_108,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2515,c_22])).

tff(c_2551,plain,(
    ! [D_110] :
      ( ~ r2_hidden(D_110,'#skF_4')
      | ~ r2_hidden(D_110,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8,c_2519])).

tff(c_2569,plain,(
    ! [A_112] :
      ( ~ r2_hidden('#skF_3'(A_112,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_112,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_2551])).

tff(c_2573,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_2569])).

tff(c_2577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2483,c_2483,c_2573])).

tff(c_2578,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2478])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2616,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2479,c_41])).

tff(c_2620,plain,(
    ! [C_115] :
      ( ~ r2_hidden(C_115,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_115,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2616,c_22])).

tff(c_2641,plain,(
    ! [D_116] :
      ( ~ r2_hidden(D_116,'#skF_4')
      | ~ r2_hidden(D_116,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_2620])).

tff(c_2716,plain,(
    ! [A_125] :
      ( ~ r2_hidden('#skF_3'(A_125,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_125,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_2641])).

tff(c_2720,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_2716])).

tff(c_2724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2578,c_2578,c_2720])).

tff(c_2726,plain,(
    ~ r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2777,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2726,c_30])).

tff(c_2778,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2777])).

tff(c_2725,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2727,plain,(
    ! [A_126,B_127,C_128] :
      ( ~ r1_xboole_0(A_126,B_127)
      | ~ r2_hidden(C_128,B_127)
      | ~ r2_hidden(C_128,A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2745,plain,(
    ! [C_130] :
      ( ~ r2_hidden(C_130,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_130,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2725,c_2727])).

tff(c_2766,plain,(
    ! [D_131] :
      ( ~ r2_hidden(D_131,'#skF_4')
      | ~ r2_hidden(D_131,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_2745])).

tff(c_2816,plain,(
    ! [A_136] :
      ( ~ r2_hidden('#skF_3'(A_136,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_136,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_2766])).

tff(c_2820,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_2816])).

tff(c_2824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2778,c_2778,c_2820])).

tff(c_2825,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2777])).

tff(c_2831,plain,(
    ! [D_137] :
      ( ~ r2_hidden(D_137,'#skF_4')
      | ~ r2_hidden(D_137,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8,c_2745])).

tff(c_2870,plain,(
    ! [A_141] :
      ( ~ r2_hidden('#skF_3'(A_141,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_141,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_2831])).

tff(c_2874,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_2870])).

tff(c_2878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2825,c_2825,c_2874])).

tff(c_2880,plain,(
    ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_2889,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2879,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_2891,plain,(
    ! [A_145,B_146,C_147] :
      ( ~ r1_xboole_0(A_145,B_146)
      | ~ r2_hidden(C_147,B_146)
      | ~ r2_hidden(C_147,A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2895,plain,(
    ! [C_148] :
      ( ~ r2_hidden(C_148,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_148,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2879,c_2891])).

tff(c_2916,plain,(
    ! [D_149] :
      ( ~ r2_hidden(D_149,'#skF_4')
      | ~ r2_hidden(D_149,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_2895])).

tff(c_2966,plain,(
    ! [A_154] :
      ( ~ r2_hidden('#skF_3'(A_154,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_154,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_2916])).

tff(c_2970,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_2966])).

tff(c_2974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2889,c_2889,c_2970])).

tff(c_2976,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3060,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_34])).

tff(c_3061,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2880,c_3060])).

tff(c_2975,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2977,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2975])).

tff(c_2978,plain,(
    ! [A_155,B_156,C_157] :
      ( ~ r1_xboole_0(A_155,B_156)
      | ~ r2_hidden(C_157,B_156)
      | ~ r2_hidden(C_157,A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2999,plain,(
    ! [C_159] :
      ( ~ r2_hidden(C_159,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_159,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2879,c_2978])).

tff(c_3020,plain,(
    ! [D_160] :
      ( ~ r2_hidden(D_160,'#skF_4')
      | ~ r2_hidden(D_160,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8,c_2999])).

tff(c_3048,plain,(
    ! [A_163] :
      ( ~ r2_hidden('#skF_3'(A_163,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_163,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_3020])).

tff(c_3052,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_3048])).

tff(c_3056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2977,c_2977,c_3052])).

tff(c_3058,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2975])).

tff(c_3062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3061,c_3058])).

%------------------------------------------------------------------------------

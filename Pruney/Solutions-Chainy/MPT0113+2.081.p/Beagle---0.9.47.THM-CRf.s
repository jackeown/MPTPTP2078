%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:22 EST 2020

% Result     : Theorem 6.56s
% Output     : CNFRefutation 6.56s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 216 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :   81 ( 249 expanded)
%              Number of equality atoms :   55 ( 145 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_73,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_43,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_77,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_43])).

tff(c_24,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_23,B_24] : k3_xboole_0(k4_xboole_0(A_23,B_24),B_24) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_369,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k3_xboole_0(A_61,B_62),C_63) = k3_xboole_0(A_61,k4_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_425,plain,(
    ! [A_64,B_65,C_66] : r1_xboole_0(k3_xboole_0(A_64,k4_xboole_0(B_65,C_66)),C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_26])).

tff(c_467,plain,(
    ! [C_67] : r1_xboole_0(k1_xboole_0,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_425])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_471,plain,(
    ! [C_67] : k3_xboole_0(k1_xboole_0,C_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_467,c_2])).

tff(c_493,plain,(
    ! [C_69] : k3_xboole_0(k1_xboole_0,C_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_467,c_2])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_504,plain,(
    ! [C_69,C_18] : k3_xboole_0(k1_xboole_0,k4_xboole_0(C_69,C_18)) = k4_xboole_0(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_20])).

tff(c_566,plain,(
    ! [C_70] : k4_xboole_0(k1_xboole_0,C_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_504])).

tff(c_28,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_574,plain,(
    ! [C_70] : k5_xboole_0(C_70,k1_xboole_0) = k2_xboole_0(C_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_28])).

tff(c_773,plain,(
    ! [C_75] : k2_xboole_0(C_75,k1_xboole_0) = C_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_574])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_779,plain,(
    ! [C_75] : k4_xboole_0(C_75,C_75) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_18])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_115,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_123,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_788,plain,(
    ! [C_76] : k4_xboole_0(C_76,C_76) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_18])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k3_xboole_0(A_19,B_20),k3_xboole_0(A_19,C_21)) = k3_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_798,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k4_xboole_0(B_20,B_20)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_22])).

tff(c_833,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_798])).

tff(c_14,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2996,plain,(
    ! [A_126,B_127,C_128] : k3_xboole_0(A_126,k4_xboole_0(k2_xboole_0(A_126,B_127),C_128)) = k4_xboole_0(A_126,C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_369])).

tff(c_596,plain,(
    ! [A_71,B_72,C_73] : k4_xboole_0(k3_xboole_0(A_71,B_72),k3_xboole_0(A_71,C_73)) = k3_xboole_0(A_71,k4_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_614,plain,(
    ! [A_71,B_72,C_73] : r1_xboole_0(k3_xboole_0(A_71,k4_xboole_0(B_72,C_73)),k3_xboole_0(A_71,C_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_26])).

tff(c_3143,plain,(
    ! [A_129,C_130] : r1_xboole_0(k4_xboole_0(A_129,C_130),k3_xboole_0(A_129,C_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2996,c_614])).

tff(c_3583,plain,(
    ! [A_136,C_137] : k3_xboole_0(k4_xboole_0(A_136,C_137),k3_xboole_0(A_136,C_137)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3143,c_2])).

tff(c_215,plain,(
    ! [A_55,B_56,C_57] : k3_xboole_0(k3_xboole_0(A_55,B_56),C_57) = k3_xboole_0(A_55,k3_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_240,plain,(
    ! [C_57] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_57)) = k3_xboole_0('#skF_1',C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_215])).

tff(c_3613,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3583,c_240])).

tff(c_3739,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_3613])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_224,plain,(
    ! [A_55,B_56,C_57] : k5_xboole_0(k3_xboole_0(A_55,B_56),k3_xboole_0(A_55,k3_xboole_0(B_56,C_57))) = k4_xboole_0(k3_xboole_0(A_55,B_56),C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_10])).

tff(c_9803,plain,(
    ! [A_200,B_201,C_202] : k5_xboole_0(k3_xboole_0(A_200,B_201),k3_xboole_0(A_200,k3_xboole_0(B_201,C_202))) = k3_xboole_0(A_200,k4_xboole_0(B_201,C_202)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_224])).

tff(c_9962,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3739,c_9803])).

tff(c_10169,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_24,c_9962])).

tff(c_419,plain,(
    ! [A_10,B_11,C_63] : k3_xboole_0(A_10,k4_xboole_0(k2_xboole_0(A_10,B_11),C_63)) = k4_xboole_0(A_10,C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_369])).

tff(c_672,plain,(
    ! [A_10,B_11,C_73] : k3_xboole_0(A_10,k4_xboole_0(k2_xboole_0(A_10,B_11),C_73)) = k4_xboole_0(A_10,k3_xboole_0(A_10,C_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_596])).

tff(c_5139,plain,(
    ! [A_10,C_73] : k4_xboole_0(A_10,k3_xboole_0(A_10,C_73)) = k4_xboole_0(A_10,C_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_672])).

tff(c_10241,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10169,c_5139])).

tff(c_10284,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_10241])).

tff(c_10286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_10284])).

tff(c_10287,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_10397,plain,(
    ! [A_219,B_220] :
      ( k3_xboole_0(A_219,B_220) = A_219
      | ~ r1_tarski(A_219,B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10409,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_10397])).

tff(c_10652,plain,(
    ! [A_230,B_231,C_232] : k4_xboole_0(k3_xboole_0(A_230,B_231),C_232) = k3_xboole_0(A_230,k4_xboole_0(B_231,C_232)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10719,plain,(
    ! [A_233,B_234,C_235] : r1_xboole_0(k3_xboole_0(A_233,k4_xboole_0(B_234,C_235)),C_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_10652,c_26])).

tff(c_10740,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10409,c_10719])).

tff(c_10758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10287,c_10740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:08:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.56/2.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.56/2.47  
% 6.56/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.56/2.47  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.56/2.47  
% 6.56/2.47  %Foreground sorts:
% 6.56/2.47  
% 6.56/2.47  
% 6.56/2.47  %Background operators:
% 6.56/2.47  
% 6.56/2.47  
% 6.56/2.47  %Foreground operators:
% 6.56/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.56/2.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.56/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.56/2.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.56/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.56/2.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.56/2.47  tff('#skF_2', type, '#skF_2': $i).
% 6.56/2.47  tff('#skF_3', type, '#skF_3': $i).
% 6.56/2.47  tff('#skF_1', type, '#skF_1': $i).
% 6.56/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.56/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.56/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.56/2.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.56/2.47  
% 6.56/2.48  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.56/2.48  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.56/2.48  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.56/2.48  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.56/2.48  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.56/2.48  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.56/2.48  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.56/2.48  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.56/2.48  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.56/2.48  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 6.56/2.48  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 6.56/2.48  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.56/2.48  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.56/2.48  tff(c_73, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | k4_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.56/2.48  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.56/2.48  tff(c_43, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 6.56/2.48  tff(c_77, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_43])).
% 6.56/2.48  tff(c_24, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.56/2.48  tff(c_26, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.56/2.48  tff(c_64, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.56/2.48  tff(c_72, plain, (![A_23, B_24]: (k3_xboole_0(k4_xboole_0(A_23, B_24), B_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_64])).
% 6.56/2.48  tff(c_369, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k3_xboole_0(A_61, B_62), C_63)=k3_xboole_0(A_61, k4_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.56/2.48  tff(c_425, plain, (![A_64, B_65, C_66]: (r1_xboole_0(k3_xboole_0(A_64, k4_xboole_0(B_65, C_66)), C_66))), inference(superposition, [status(thm), theory('equality')], [c_369, c_26])).
% 6.56/2.48  tff(c_467, plain, (![C_67]: (r1_xboole_0(k1_xboole_0, C_67))), inference(superposition, [status(thm), theory('equality')], [c_72, c_425])).
% 6.56/2.48  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.56/2.48  tff(c_471, plain, (![C_67]: (k3_xboole_0(k1_xboole_0, C_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_467, c_2])).
% 6.56/2.48  tff(c_493, plain, (![C_69]: (k3_xboole_0(k1_xboole_0, C_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_467, c_2])).
% 6.56/2.48  tff(c_20, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.56/2.48  tff(c_504, plain, (![C_69, C_18]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(C_69, C_18))=k4_xboole_0(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_493, c_20])).
% 6.56/2.48  tff(c_566, plain, (![C_70]: (k4_xboole_0(k1_xboole_0, C_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_471, c_504])).
% 6.56/2.48  tff(c_28, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.56/2.48  tff(c_574, plain, (![C_70]: (k5_xboole_0(C_70, k1_xboole_0)=k2_xboole_0(C_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_566, c_28])).
% 6.56/2.48  tff(c_773, plain, (![C_75]: (k2_xboole_0(C_75, k1_xboole_0)=C_75)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_574])).
% 6.56/2.48  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.56/2.48  tff(c_779, plain, (![C_75]: (k4_xboole_0(C_75, C_75)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_773, c_18])).
% 6.56/2.48  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.56/2.48  tff(c_115, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.56/2.48  tff(c_123, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_115])).
% 6.56/2.48  tff(c_788, plain, (![C_76]: (k4_xboole_0(C_76, C_76)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_773, c_18])).
% 6.56/2.48  tff(c_22, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k3_xboole_0(A_19, B_20), k3_xboole_0(A_19, C_21))=k3_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.56/2.48  tff(c_798, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k4_xboole_0(B_20, B_20))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_788, c_22])).
% 6.56/2.48  tff(c_833, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_779, c_798])).
% 6.56/2.48  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.56/2.48  tff(c_2996, plain, (![A_126, B_127, C_128]: (k3_xboole_0(A_126, k4_xboole_0(k2_xboole_0(A_126, B_127), C_128))=k4_xboole_0(A_126, C_128))), inference(superposition, [status(thm), theory('equality')], [c_14, c_369])).
% 6.56/2.48  tff(c_596, plain, (![A_71, B_72, C_73]: (k4_xboole_0(k3_xboole_0(A_71, B_72), k3_xboole_0(A_71, C_73))=k3_xboole_0(A_71, k4_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.56/2.48  tff(c_614, plain, (![A_71, B_72, C_73]: (r1_xboole_0(k3_xboole_0(A_71, k4_xboole_0(B_72, C_73)), k3_xboole_0(A_71, C_73)))), inference(superposition, [status(thm), theory('equality')], [c_596, c_26])).
% 6.56/2.48  tff(c_3143, plain, (![A_129, C_130]: (r1_xboole_0(k4_xboole_0(A_129, C_130), k3_xboole_0(A_129, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_2996, c_614])).
% 6.56/2.48  tff(c_3583, plain, (![A_136, C_137]: (k3_xboole_0(k4_xboole_0(A_136, C_137), k3_xboole_0(A_136, C_137))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3143, c_2])).
% 6.56/2.48  tff(c_215, plain, (![A_55, B_56, C_57]: (k3_xboole_0(k3_xboole_0(A_55, B_56), C_57)=k3_xboole_0(A_55, k3_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.56/2.48  tff(c_240, plain, (![C_57]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_57))=k3_xboole_0('#skF_1', C_57))), inference(superposition, [status(thm), theory('equality')], [c_123, c_215])).
% 6.56/2.48  tff(c_3613, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3583, c_240])).
% 6.56/2.48  tff(c_3739, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_833, c_3613])).
% 6.56/2.48  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.56/2.48  tff(c_224, plain, (![A_55, B_56, C_57]: (k5_xboole_0(k3_xboole_0(A_55, B_56), k3_xboole_0(A_55, k3_xboole_0(B_56, C_57)))=k4_xboole_0(k3_xboole_0(A_55, B_56), C_57))), inference(superposition, [status(thm), theory('equality')], [c_215, c_10])).
% 6.56/2.48  tff(c_9803, plain, (![A_200, B_201, C_202]: (k5_xboole_0(k3_xboole_0(A_200, B_201), k3_xboole_0(A_200, k3_xboole_0(B_201, C_202)))=k3_xboole_0(A_200, k4_xboole_0(B_201, C_202)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_224])).
% 6.56/2.48  tff(c_9962, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3739, c_9803])).
% 6.56/2.48  tff(c_10169, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_24, c_9962])).
% 6.56/2.48  tff(c_419, plain, (![A_10, B_11, C_63]: (k3_xboole_0(A_10, k4_xboole_0(k2_xboole_0(A_10, B_11), C_63))=k4_xboole_0(A_10, C_63))), inference(superposition, [status(thm), theory('equality')], [c_14, c_369])).
% 6.56/2.48  tff(c_672, plain, (![A_10, B_11, C_73]: (k3_xboole_0(A_10, k4_xboole_0(k2_xboole_0(A_10, B_11), C_73))=k4_xboole_0(A_10, k3_xboole_0(A_10, C_73)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_596])).
% 6.56/2.48  tff(c_5139, plain, (![A_10, C_73]: (k4_xboole_0(A_10, k3_xboole_0(A_10, C_73))=k4_xboole_0(A_10, C_73))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_672])).
% 6.56/2.48  tff(c_10241, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10169, c_5139])).
% 6.56/2.48  tff(c_10284, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_779, c_10241])).
% 6.56/2.48  tff(c_10286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_10284])).
% 6.56/2.48  tff(c_10287, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 6.56/2.48  tff(c_10397, plain, (![A_219, B_220]: (k3_xboole_0(A_219, B_220)=A_219 | ~r1_tarski(A_219, B_220))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.56/2.48  tff(c_10409, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_10397])).
% 6.56/2.48  tff(c_10652, plain, (![A_230, B_231, C_232]: (k4_xboole_0(k3_xboole_0(A_230, B_231), C_232)=k3_xboole_0(A_230, k4_xboole_0(B_231, C_232)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.56/2.48  tff(c_10719, plain, (![A_233, B_234, C_235]: (r1_xboole_0(k3_xboole_0(A_233, k4_xboole_0(B_234, C_235)), C_235))), inference(superposition, [status(thm), theory('equality')], [c_10652, c_26])).
% 6.56/2.48  tff(c_10740, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10409, c_10719])).
% 6.56/2.48  tff(c_10758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10287, c_10740])).
% 6.56/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.56/2.48  
% 6.56/2.48  Inference rules
% 6.56/2.48  ----------------------
% 6.56/2.48  #Ref     : 0
% 6.56/2.48  #Sup     : 2705
% 6.56/2.48  #Fact    : 0
% 6.56/2.48  #Define  : 0
% 6.56/2.48  #Split   : 1
% 6.56/2.48  #Chain   : 0
% 6.56/2.48  #Close   : 0
% 6.56/2.48  
% 6.56/2.48  Ordering : KBO
% 6.56/2.48  
% 6.56/2.48  Simplification rules
% 6.56/2.48  ----------------------
% 6.56/2.48  #Subsume      : 0
% 6.56/2.48  #Demod        : 3008
% 6.56/2.48  #Tautology    : 1911
% 6.56/2.48  #SimpNegUnit  : 2
% 6.56/2.48  #BackRed      : 6
% 6.56/2.48  
% 6.56/2.48  #Partial instantiations: 0
% 6.56/2.48  #Strategies tried      : 1
% 6.56/2.48  
% 6.56/2.48  Timing (in seconds)
% 6.56/2.48  ----------------------
% 6.56/2.49  Preprocessing        : 0.32
% 6.56/2.49  Parsing              : 0.18
% 6.56/2.49  CNF conversion       : 0.02
% 6.56/2.49  Main loop            : 1.36
% 6.56/2.49  Inferencing          : 0.38
% 6.56/2.49  Reduction            : 0.67
% 6.56/2.49  Demodulation         : 0.56
% 6.56/2.49  BG Simplification    : 0.04
% 6.56/2.49  Subsumption          : 0.18
% 6.56/2.49  Abstraction          : 0.07
% 6.56/2.49  MUC search           : 0.00
% 6.56/2.49  Cooper               : 0.00
% 6.56/2.49  Total                : 1.72
% 6.56/2.49  Index Insertion      : 0.00
% 6.56/2.49  Index Deletion       : 0.00
% 6.56/2.49  Index Matching       : 0.00
% 6.56/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------

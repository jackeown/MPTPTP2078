%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:22 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 399 expanded)
%              Number of leaves         :   26 ( 142 expanded)
%              Depth                    :   18
%              Number of atoms          :   86 ( 456 expanded)
%              Number of equality atoms :   62 ( 294 expanded)
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

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_111,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_119,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_60])).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_70])).

tff(c_581,plain,(
    ! [A_68,B_69,C_70] : k4_xboole_0(k3_xboole_0(A_68,B_69),C_70) = k3_xboole_0(A_68,k4_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_632,plain,(
    ! [A_71,B_72,C_73] : r1_xboole_0(k3_xboole_0(A_71,k4_xboole_0(B_72,C_73)),C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_24])).

tff(c_677,plain,(
    ! [C_74] : r1_xboole_0(k1_xboole_0,C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_632])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_681,plain,(
    ! [C_74] : k3_xboole_0(k1_xboole_0,C_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_677,c_2])).

tff(c_694,plain,(
    ! [C_76] : k3_xboole_0(k1_xboole_0,C_76) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_677,c_2])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_705,plain,(
    ! [C_76,C_16] : k3_xboole_0(k1_xboole_0,k4_xboole_0(C_76,C_16)) = k4_xboole_0(k1_xboole_0,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_18])).

tff(c_740,plain,(
    ! [C_77] : k4_xboole_0(k1_xboole_0,C_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_705])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_757,plain,(
    ! [C_77] : k5_xboole_0(C_77,k1_xboole_0) = k2_xboole_0(C_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_28])).

tff(c_777,plain,(
    ! [C_77] : k2_xboole_0(C_77,k1_xboole_0) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_757])).

tff(c_874,plain,(
    ! [C_81] : k2_xboole_0(C_81,k1_xboole_0) = C_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_757])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_133,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k5_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_157,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_151])).

tff(c_210,plain,(
    ! [A_52,B_53] : k5_xboole_0(A_52,k4_xboole_0(B_53,A_52)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_222,plain,(
    ! [A_10,B_11] : k5_xboole_0(k2_xboole_0(A_10,B_11),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_210])).

tff(c_347,plain,(
    ! [A_60,B_61] : k2_xboole_0(k2_xboole_0(A_60,B_61),A_60) = k2_xboole_0(A_60,B_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_222])).

tff(c_362,plain,(
    ! [A_60,B_61] : k4_xboole_0(k2_xboole_0(A_60,B_61),k2_xboole_0(A_60,B_61)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_157])).

tff(c_883,plain,(
    ! [C_81] : k4_xboole_0(k2_xboole_0(C_81,k1_xboole_0),C_81) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_362])).

tff(c_906,plain,(
    ! [C_81] : k4_xboole_0(C_81,C_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_883])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_120,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_128,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_1100,plain,(
    ! [A_85,B_86,C_87] : k4_xboole_0(k3_xboole_0(A_85,B_86),k3_xboole_0(A_85,C_87)) = k3_xboole_0(A_85,k4_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1107,plain,(
    ! [A_85,C_87] : k3_xboole_0(A_85,k4_xboole_0(C_87,C_87)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1100,c_906])).

tff(c_1198,plain,(
    ! [A_85] : k3_xboole_0(A_85,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_1107])).

tff(c_628,plain,(
    ! [A_10,B_11,C_70] : k3_xboole_0(A_10,k4_xboole_0(k2_xboole_0(A_10,B_11),C_70)) = k4_xboole_0(A_10,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_581])).

tff(c_1193,plain,(
    ! [A_10,B_11,C_87] : k3_xboole_0(A_10,k4_xboole_0(k2_xboole_0(A_10,B_11),C_87)) = k4_xboole_0(A_10,k3_xboole_0(A_10,C_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1100])).

tff(c_2392,plain,(
    ! [A_115,C_116] : k4_xboole_0(A_115,k3_xboole_0(A_115,C_116)) = k4_xboole_0(A_115,C_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_1193])).

tff(c_2726,plain,(
    ! [A_124,C_125] : k3_xboole_0(k4_xboole_0(A_124,C_125),k3_xboole_0(A_124,C_125)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2392,c_74])).

tff(c_784,plain,(
    ! [A_78,B_79,C_80] : k3_xboole_0(k3_xboole_0(A_78,B_79),C_80) = k3_xboole_0(A_78,k3_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_823,plain,(
    ! [C_80] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_80)) = k3_xboole_0('#skF_1',C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_784])).

tff(c_2753,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2726,c_823])).

tff(c_2857,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_2753])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_804,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k3_xboole_0(A_78,B_79),k3_xboole_0(A_78,k3_xboole_0(B_79,C_80))) = k4_xboole_0(k3_xboole_0(A_78,B_79),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_10])).

tff(c_7364,plain,(
    ! [A_184,B_185,C_186] : k5_xboole_0(k3_xboole_0(A_184,B_185),k3_xboole_0(A_184,k3_xboole_0(B_185,C_186))) = k3_xboole_0(A_184,k4_xboole_0(B_185,C_186)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_804])).

tff(c_7494,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2857,c_7364])).

tff(c_7651,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_22,c_7494])).

tff(c_2390,plain,(
    ! [A_10,C_87] : k4_xboole_0(A_10,k3_xboole_0(A_10,C_87)) = k4_xboole_0(A_10,C_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_1193])).

tff(c_7716,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7651,c_2390])).

tff(c_7744,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_7716])).

tff(c_7746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_7744])).

tff(c_7747,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_7764,plain,(
    ! [A_193,B_194] :
      ( k3_xboole_0(A_193,B_194) = A_193
      | ~ r1_tarski(A_193,B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7776,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_7764])).

tff(c_8254,plain,(
    ! [A_219,B_220,C_221] : k4_xboole_0(k3_xboole_0(A_219,B_220),C_221) = k3_xboole_0(A_219,k4_xboole_0(B_220,C_221)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8311,plain,(
    ! [A_222,B_223,C_224] : r1_xboole_0(k3_xboole_0(A_222,k4_xboole_0(B_223,C_224)),C_224) ),
    inference(superposition,[status(thm),theory(equality)],[c_8254,c_24])).

tff(c_8350,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7776,c_8311])).

tff(c_8354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7747,c_8350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.21  
% 5.50/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.21  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.50/2.21  
% 5.50/2.21  %Foreground sorts:
% 5.50/2.21  
% 5.50/2.21  
% 5.50/2.21  %Background operators:
% 5.50/2.21  
% 5.50/2.21  
% 5.50/2.21  %Foreground operators:
% 5.50/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.50/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.50/2.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.50/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.50/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.50/2.21  tff('#skF_3', type, '#skF_3': $i).
% 5.50/2.21  tff('#skF_1', type, '#skF_1': $i).
% 5.50/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.50/2.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.50/2.21  
% 5.50/2.23  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.50/2.23  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.50/2.23  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.50/2.23  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.50/2.23  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.50/2.23  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.50/2.23  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.50/2.23  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.50/2.23  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.50/2.23  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.50/2.23  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.50/2.23  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 5.50/2.23  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.50/2.23  tff(c_111, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | k4_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.50/2.23  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.50/2.23  tff(c_60, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 5.50/2.23  tff(c_119, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_60])).
% 5.50/2.23  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.50/2.23  tff(c_24, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.50/2.23  tff(c_70, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.50/2.23  tff(c_74, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_70])).
% 5.50/2.23  tff(c_581, plain, (![A_68, B_69, C_70]: (k4_xboole_0(k3_xboole_0(A_68, B_69), C_70)=k3_xboole_0(A_68, k4_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.50/2.23  tff(c_632, plain, (![A_71, B_72, C_73]: (r1_xboole_0(k3_xboole_0(A_71, k4_xboole_0(B_72, C_73)), C_73))), inference(superposition, [status(thm), theory('equality')], [c_581, c_24])).
% 5.50/2.23  tff(c_677, plain, (![C_74]: (r1_xboole_0(k1_xboole_0, C_74))), inference(superposition, [status(thm), theory('equality')], [c_74, c_632])).
% 5.50/2.23  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.50/2.23  tff(c_681, plain, (![C_74]: (k3_xboole_0(k1_xboole_0, C_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_677, c_2])).
% 5.50/2.23  tff(c_694, plain, (![C_76]: (k3_xboole_0(k1_xboole_0, C_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_677, c_2])).
% 5.50/2.23  tff(c_18, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.50/2.23  tff(c_705, plain, (![C_76, C_16]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(C_76, C_16))=k4_xboole_0(k1_xboole_0, C_16))), inference(superposition, [status(thm), theory('equality')], [c_694, c_18])).
% 5.50/2.23  tff(c_740, plain, (![C_77]: (k4_xboole_0(k1_xboole_0, C_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_681, c_705])).
% 5.50/2.23  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.50/2.23  tff(c_757, plain, (![C_77]: (k5_xboole_0(C_77, k1_xboole_0)=k2_xboole_0(C_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_740, c_28])).
% 5.50/2.23  tff(c_777, plain, (![C_77]: (k2_xboole_0(C_77, k1_xboole_0)=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_757])).
% 5.50/2.23  tff(c_874, plain, (![C_81]: (k2_xboole_0(C_81, k1_xboole_0)=C_81)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_757])).
% 5.50/2.23  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.50/2.23  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.50/2.23  tff(c_133, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.50/2.23  tff(c_151, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k5_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_133])).
% 5.50/2.23  tff(c_157, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_151])).
% 5.50/2.23  tff(c_210, plain, (![A_52, B_53]: (k5_xboole_0(A_52, k4_xboole_0(B_53, A_52))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.50/2.23  tff(c_222, plain, (![A_10, B_11]: (k5_xboole_0(k2_xboole_0(A_10, B_11), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_157, c_210])).
% 5.50/2.23  tff(c_347, plain, (![A_60, B_61]: (k2_xboole_0(k2_xboole_0(A_60, B_61), A_60)=k2_xboole_0(A_60, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_222])).
% 5.50/2.23  tff(c_362, plain, (![A_60, B_61]: (k4_xboole_0(k2_xboole_0(A_60, B_61), k2_xboole_0(A_60, B_61))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_347, c_157])).
% 5.50/2.23  tff(c_883, plain, (![C_81]: (k4_xboole_0(k2_xboole_0(C_81, k1_xboole_0), C_81)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_874, c_362])).
% 5.50/2.23  tff(c_906, plain, (![C_81]: (k4_xboole_0(C_81, C_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_777, c_883])).
% 5.50/2.23  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.50/2.23  tff(c_120, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.50/2.23  tff(c_128, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_120])).
% 5.50/2.23  tff(c_1100, plain, (![A_85, B_86, C_87]: (k4_xboole_0(k3_xboole_0(A_85, B_86), k3_xboole_0(A_85, C_87))=k3_xboole_0(A_85, k4_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.50/2.23  tff(c_1107, plain, (![A_85, C_87]: (k3_xboole_0(A_85, k4_xboole_0(C_87, C_87))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1100, c_906])).
% 5.50/2.23  tff(c_1198, plain, (![A_85]: (k3_xboole_0(A_85, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_906, c_1107])).
% 5.50/2.23  tff(c_628, plain, (![A_10, B_11, C_70]: (k3_xboole_0(A_10, k4_xboole_0(k2_xboole_0(A_10, B_11), C_70))=k4_xboole_0(A_10, C_70))), inference(superposition, [status(thm), theory('equality')], [c_14, c_581])).
% 5.50/2.23  tff(c_1193, plain, (![A_10, B_11, C_87]: (k3_xboole_0(A_10, k4_xboole_0(k2_xboole_0(A_10, B_11), C_87))=k4_xboole_0(A_10, k3_xboole_0(A_10, C_87)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1100])).
% 5.50/2.23  tff(c_2392, plain, (![A_115, C_116]: (k4_xboole_0(A_115, k3_xboole_0(A_115, C_116))=k4_xboole_0(A_115, C_116))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_1193])).
% 5.50/2.23  tff(c_2726, plain, (![A_124, C_125]: (k3_xboole_0(k4_xboole_0(A_124, C_125), k3_xboole_0(A_124, C_125))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2392, c_74])).
% 5.50/2.23  tff(c_784, plain, (![A_78, B_79, C_80]: (k3_xboole_0(k3_xboole_0(A_78, B_79), C_80)=k3_xboole_0(A_78, k3_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.50/2.23  tff(c_823, plain, (![C_80]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_80))=k3_xboole_0('#skF_1', C_80))), inference(superposition, [status(thm), theory('equality')], [c_128, c_784])).
% 5.50/2.23  tff(c_2753, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2726, c_823])).
% 5.50/2.23  tff(c_2857, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_2753])).
% 5.50/2.23  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.50/2.23  tff(c_804, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k3_xboole_0(A_78, B_79), k3_xboole_0(A_78, k3_xboole_0(B_79, C_80)))=k4_xboole_0(k3_xboole_0(A_78, B_79), C_80))), inference(superposition, [status(thm), theory('equality')], [c_784, c_10])).
% 5.50/2.23  tff(c_7364, plain, (![A_184, B_185, C_186]: (k5_xboole_0(k3_xboole_0(A_184, B_185), k3_xboole_0(A_184, k3_xboole_0(B_185, C_186)))=k3_xboole_0(A_184, k4_xboole_0(B_185, C_186)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_804])).
% 5.50/2.23  tff(c_7494, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2857, c_7364])).
% 5.50/2.23  tff(c_7651, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_22, c_7494])).
% 5.50/2.23  tff(c_2390, plain, (![A_10, C_87]: (k4_xboole_0(A_10, k3_xboole_0(A_10, C_87))=k4_xboole_0(A_10, C_87))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_1193])).
% 5.50/2.23  tff(c_7716, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7651, c_2390])).
% 5.50/2.23  tff(c_7744, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_906, c_7716])).
% 5.50/2.23  tff(c_7746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_7744])).
% 5.50/2.23  tff(c_7747, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 5.50/2.23  tff(c_7764, plain, (![A_193, B_194]: (k3_xboole_0(A_193, B_194)=A_193 | ~r1_tarski(A_193, B_194))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.50/2.23  tff(c_7776, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_7764])).
% 5.50/2.23  tff(c_8254, plain, (![A_219, B_220, C_221]: (k4_xboole_0(k3_xboole_0(A_219, B_220), C_221)=k3_xboole_0(A_219, k4_xboole_0(B_220, C_221)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.50/2.23  tff(c_8311, plain, (![A_222, B_223, C_224]: (r1_xboole_0(k3_xboole_0(A_222, k4_xboole_0(B_223, C_224)), C_224))), inference(superposition, [status(thm), theory('equality')], [c_8254, c_24])).
% 5.50/2.23  tff(c_8350, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7776, c_8311])).
% 5.50/2.23  tff(c_8354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7747, c_8350])).
% 5.50/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.23  
% 5.50/2.23  Inference rules
% 5.50/2.23  ----------------------
% 5.50/2.23  #Ref     : 0
% 5.50/2.23  #Sup     : 2090
% 5.50/2.23  #Fact    : 0
% 5.50/2.23  #Define  : 0
% 5.50/2.23  #Split   : 1
% 5.50/2.23  #Chain   : 0
% 5.50/2.23  #Close   : 0
% 5.50/2.23  
% 5.50/2.23  Ordering : KBO
% 5.50/2.23  
% 5.50/2.23  Simplification rules
% 5.50/2.23  ----------------------
% 5.50/2.23  #Subsume      : 0
% 5.50/2.23  #Demod        : 2148
% 5.50/2.23  #Tautology    : 1434
% 5.50/2.23  #SimpNegUnit  : 2
% 5.50/2.23  #BackRed      : 3
% 5.50/2.23  
% 5.50/2.23  #Partial instantiations: 0
% 5.50/2.23  #Strategies tried      : 1
% 5.50/2.23  
% 5.50/2.23  Timing (in seconds)
% 5.50/2.23  ----------------------
% 5.50/2.23  Preprocessing        : 0.28
% 5.50/2.23  Parsing              : 0.15
% 5.50/2.23  CNF conversion       : 0.02
% 5.50/2.23  Main loop            : 1.14
% 5.50/2.23  Inferencing          : 0.34
% 5.50/2.23  Reduction            : 0.54
% 5.50/2.23  Demodulation         : 0.43
% 5.50/2.23  BG Simplification    : 0.04
% 5.50/2.23  Subsumption          : 0.15
% 5.50/2.23  Abstraction          : 0.07
% 5.50/2.23  MUC search           : 0.00
% 5.50/2.23  Cooper               : 0.00
% 5.50/2.23  Total                : 1.46
% 5.50/2.23  Index Insertion      : 0.00
% 5.50/2.23  Index Deletion       : 0.00
% 5.50/2.23  Index Matching       : 0.00
% 5.50/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

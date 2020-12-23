%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:11 EST 2020

% Result     : Theorem 13.68s
% Output     : CNFRefutation 13.82s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 658 expanded)
%              Number of leaves         :   20 ( 228 expanded)
%              Depth                    :   17
%              Number of atoms          :   84 ( 849 expanded)
%              Number of equality atoms :   69 ( 523 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_25,plain,(
    ! [B_18,A_19] : k2_xboole_0(B_18,A_19) = k2_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ! [A_19,B_18] : r1_tarski(A_19,k2_xboole_0(B_18,A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_18])).

tff(c_102,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [A_19,B_18] : k4_xboole_0(A_19,k2_xboole_0(B_18,A_19)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_102])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_331,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | k4_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_8651,plain,(
    ! [A_176,B_177,C_178] :
      ( k2_xboole_0(k4_xboole_0(A_176,B_177),C_178) = C_178
      | k4_xboole_0(A_176,k2_xboole_0(B_177,C_178)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_331])).

tff(c_8827,plain,(
    ! [A_19,B_18] : k2_xboole_0(k4_xboole_0(A_19,B_18),A_19) = A_19 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8651])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_102])).

tff(c_153,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_153])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_240,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k4_xboole_0(A_42,B_43),C_44) = k4_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_980,plain,(
    ! [A_67,B_68,C_69] : k4_xboole_0(A_67,k2_xboole_0(k4_xboole_0(A_67,B_68),C_69)) = k4_xboole_0(k3_xboole_0(A_67,B_68),C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_240])).

tff(c_1410,plain,(
    ! [A_77,B_78] : k4_xboole_0(k3_xboole_0(A_77,B_78),A_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_980])).

tff(c_1781,plain,(
    ! [A_87] : k4_xboole_0(k4_xboole_0(A_87,k1_xboole_0),A_87) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_1410])).

tff(c_85,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_1865,plain,(
    ! [A_88] : k2_xboole_0(k4_xboole_0(A_88,k1_xboole_0),A_88) = A_88 ),
    inference(superposition,[status(thm),theory(equality)],[c_1781,c_85])).

tff(c_1954,plain,(
    ! [B_2] : k2_xboole_0(B_2,k4_xboole_0(B_2,k1_xboole_0)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1865])).

tff(c_174,plain,(
    ! [A_38,B_39] : k2_xboole_0(A_38,k2_xboole_0(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(resolution,[status(thm)],[c_18,c_75])).

tff(c_211,plain,(
    ! [A_40,B_41] : r1_tarski(k2_xboole_0(A_40,B_41),k2_xboole_0(A_40,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_40])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_613,plain,(
    ! [A_59,B_60] : k4_xboole_0(k2_xboole_0(A_59,B_60),k2_xboole_0(A_59,B_60)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_211,c_10])).

tff(c_621,plain,(
    ! [A_59,B_60,C_11] : k4_xboole_0(k2_xboole_0(A_59,B_60),k2_xboole_0(k2_xboole_0(A_59,B_60),C_11)) = k4_xboole_0(k1_xboole_0,C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_14])).

tff(c_667,plain,(
    ! [C_61] : k4_xboole_0(k1_xboole_0,C_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_621])).

tff(c_711,plain,(
    ! [C_61] : k2_xboole_0(k1_xboole_0,C_61) = C_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_85])).

tff(c_86,plain,(
    ! [A_19,B_18] : k2_xboole_0(A_19,k2_xboole_0(B_18,A_19)) = k2_xboole_0(B_18,A_19) ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_2517,plain,(
    ! [A_99,B_100,B_101] : k4_xboole_0(A_99,k2_xboole_0(B_100,k2_xboole_0(k4_xboole_0(A_99,B_100),B_101))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_114])).

tff(c_2648,plain,(
    ! [A_99,A_19] : k4_xboole_0(A_99,k2_xboole_0(k4_xboole_0(A_99,A_19),A_19)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_2517])).

tff(c_3019,plain,(
    ! [A_109,A_110] : k4_xboole_0(A_109,k2_xboole_0(A_110,k4_xboole_0(A_109,A_110))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2648])).

tff(c_3232,plain,(
    ! [A_112] : k4_xboole_0(A_112,k4_xboole_0(A_112,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_3019])).

tff(c_3255,plain,(
    ! [A_112] : k2_xboole_0(A_112,k4_xboole_0(A_112,k1_xboole_0)) = k4_xboole_0(A_112,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3232,c_85])).

tff(c_3313,plain,(
    ! [A_112] : k4_xboole_0(A_112,k1_xboole_0) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_3255])).

tff(c_729,plain,(
    ! [C_62] : k2_xboole_0(k1_xboole_0,C_62) = C_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_85])).

tff(c_236,plain,(
    ! [A_40,B_41] : k4_xboole_0(k2_xboole_0(A_40,B_41),k2_xboole_0(A_40,B_41)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_211,c_10])).

tff(c_738,plain,(
    ! [C_62] : k4_xboole_0(k2_xboole_0(k1_xboole_0,C_62),C_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_236])).

tff(c_1168,plain,(
    ! [C_71] : k4_xboole_0(C_71,C_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_738])).

tff(c_1189,plain,(
    ! [C_71] : k4_xboole_0(C_71,k1_xboole_0) = k3_xboole_0(C_71,C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_16])).

tff(c_3332,plain,(
    ! [C_71] : k3_xboole_0(C_71,C_71) = C_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3313,c_1189])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_89])).

tff(c_347,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,k4_xboole_0(A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_16])).

tff(c_373,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_347])).

tff(c_1347,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_373])).

tff(c_3422,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3332,c_1347])).

tff(c_5370,plain,(
    ! [A_143,B_144,B_145] : k4_xboole_0(A_143,k2_xboole_0(B_144,k4_xboole_0(A_143,B_145))) = k4_xboole_0(k3_xboole_0(A_143,B_145),B_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_980])).

tff(c_2708,plain,(
    ! [A_99,A_19] : k4_xboole_0(A_99,k2_xboole_0(A_19,k4_xboole_0(A_99,A_19))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2648])).

tff(c_5613,plain,(
    ! [A_146,B_147] : k4_xboole_0(k3_xboole_0(A_146,B_147),B_147) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5370,c_2708])).

tff(c_5732,plain,(
    ! [A_148,B_149] : k2_xboole_0(k3_xboole_0(A_148,B_149),B_149) = B_149 ),
    inference(superposition,[status(thm),theory(equality)],[c_5613,c_85])).

tff(c_6019,plain,(
    ! [A_152,A_153] : k2_xboole_0(A_152,k3_xboole_0(A_153,A_152)) = A_152 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5732])).

tff(c_6134,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3422,c_6019])).

tff(c_8830,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8827,c_6134])).

tff(c_2193,plain,(
    ! [A_92,B_93,C_94] : k4_xboole_0(k4_xboole_0(A_92,B_93),k4_xboole_0(A_92,k2_xboole_0(B_93,C_94))) = k3_xboole_0(k4_xboole_0(A_92,B_93),C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_16])).

tff(c_13679,plain,(
    ! [A_229,A_230,B_231] : k4_xboole_0(k4_xboole_0(A_229,A_230),k4_xboole_0(A_229,k2_xboole_0(B_231,A_230))) = k3_xboole_0(k4_xboole_0(A_229,A_230),B_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2193])).

tff(c_13806,plain,(
    ! [B_231] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0(B_231,'#skF_2'))) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_8830,c_13679])).

tff(c_14056,plain,(
    ! [B_231] : k3_xboole_0('#skF_1',k2_xboole_0(B_231,'#skF_2')) = k3_xboole_0('#skF_1',B_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8830,c_16,c_13806])).

tff(c_20,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_47101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14056,c_23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.68/7.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.68/7.42  
% 13.68/7.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.68/7.42  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.68/7.42  
% 13.68/7.42  %Foreground sorts:
% 13.68/7.42  
% 13.68/7.42  
% 13.68/7.42  %Background operators:
% 13.68/7.42  
% 13.68/7.42  
% 13.68/7.42  %Foreground operators:
% 13.68/7.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.68/7.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.68/7.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.68/7.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.68/7.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.68/7.42  tff('#skF_2', type, '#skF_2': $i).
% 13.68/7.42  tff('#skF_3', type, '#skF_3': $i).
% 13.68/7.42  tff('#skF_1', type, '#skF_1': $i).
% 13.68/7.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.68/7.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.68/7.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.68/7.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.68/7.42  
% 13.82/7.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.82/7.44  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.82/7.44  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.82/7.44  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 13.82/7.44  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.82/7.44  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.82/7.44  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 13.82/7.44  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 13.82/7.44  tff(c_25, plain, (![B_18, A_19]: (k2_xboole_0(B_18, A_19)=k2_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.82/7.44  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.82/7.44  tff(c_40, plain, (![A_19, B_18]: (r1_tarski(A_19, k2_xboole_0(B_18, A_19)))), inference(superposition, [status(thm), theory('equality')], [c_25, c_18])).
% 13.82/7.44  tff(c_102, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.82/7.44  tff(c_113, plain, (![A_19, B_18]: (k4_xboole_0(A_19, k2_xboole_0(B_18, A_19))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_102])).
% 13.82/7.44  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.82/7.44  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.82/7.44  tff(c_75, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.82/7.44  tff(c_331, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | k4_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_75])).
% 13.82/7.44  tff(c_8651, plain, (![A_176, B_177, C_178]: (k2_xboole_0(k4_xboole_0(A_176, B_177), C_178)=C_178 | k4_xboole_0(A_176, k2_xboole_0(B_177, C_178))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_331])).
% 13.82/7.44  tff(c_8827, plain, (![A_19, B_18]: (k2_xboole_0(k4_xboole_0(A_19, B_18), A_19)=A_19)), inference(superposition, [status(thm), theory('equality')], [c_113, c_8651])).
% 13.82/7.44  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.82/7.44  tff(c_114, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_102])).
% 13.82/7.44  tff(c_153, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.82/7.44  tff(c_171, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_114, c_153])).
% 13.82/7.44  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.82/7.44  tff(c_240, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k4_xboole_0(A_42, B_43), C_44)=k4_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.82/7.44  tff(c_980, plain, (![A_67, B_68, C_69]: (k4_xboole_0(A_67, k2_xboole_0(k4_xboole_0(A_67, B_68), C_69))=k4_xboole_0(k3_xboole_0(A_67, B_68), C_69))), inference(superposition, [status(thm), theory('equality')], [c_16, c_240])).
% 13.82/7.44  tff(c_1410, plain, (![A_77, B_78]: (k4_xboole_0(k3_xboole_0(A_77, B_78), A_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113, c_980])).
% 13.82/7.44  tff(c_1781, plain, (![A_87]: (k4_xboole_0(k4_xboole_0(A_87, k1_xboole_0), A_87)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_171, c_1410])).
% 13.82/7.44  tff(c_85, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_75])).
% 13.82/7.44  tff(c_1865, plain, (![A_88]: (k2_xboole_0(k4_xboole_0(A_88, k1_xboole_0), A_88)=A_88)), inference(superposition, [status(thm), theory('equality')], [c_1781, c_85])).
% 13.82/7.44  tff(c_1954, plain, (![B_2]: (k2_xboole_0(B_2, k4_xboole_0(B_2, k1_xboole_0))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1865])).
% 13.82/7.44  tff(c_174, plain, (![A_38, B_39]: (k2_xboole_0(A_38, k2_xboole_0(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(resolution, [status(thm)], [c_18, c_75])).
% 13.82/7.44  tff(c_211, plain, (![A_40, B_41]: (r1_tarski(k2_xboole_0(A_40, B_41), k2_xboole_0(A_40, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_174, c_40])).
% 13.82/7.44  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.82/7.44  tff(c_613, plain, (![A_59, B_60]: (k4_xboole_0(k2_xboole_0(A_59, B_60), k2_xboole_0(A_59, B_60))=k1_xboole_0)), inference(resolution, [status(thm)], [c_211, c_10])).
% 13.82/7.44  tff(c_621, plain, (![A_59, B_60, C_11]: (k4_xboole_0(k2_xboole_0(A_59, B_60), k2_xboole_0(k2_xboole_0(A_59, B_60), C_11))=k4_xboole_0(k1_xboole_0, C_11))), inference(superposition, [status(thm), theory('equality')], [c_613, c_14])).
% 13.82/7.44  tff(c_667, plain, (![C_61]: (k4_xboole_0(k1_xboole_0, C_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_621])).
% 13.82/7.44  tff(c_711, plain, (![C_61]: (k2_xboole_0(k1_xboole_0, C_61)=C_61)), inference(superposition, [status(thm), theory('equality')], [c_667, c_85])).
% 13.82/7.44  tff(c_86, plain, (![A_19, B_18]: (k2_xboole_0(A_19, k2_xboole_0(B_18, A_19))=k2_xboole_0(B_18, A_19))), inference(resolution, [status(thm)], [c_40, c_75])).
% 13.82/7.44  tff(c_2517, plain, (![A_99, B_100, B_101]: (k4_xboole_0(A_99, k2_xboole_0(B_100, k2_xboole_0(k4_xboole_0(A_99, B_100), B_101)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_240, c_114])).
% 13.82/7.44  tff(c_2648, plain, (![A_99, A_19]: (k4_xboole_0(A_99, k2_xboole_0(k4_xboole_0(A_99, A_19), A_19))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_86, c_2517])).
% 13.82/7.44  tff(c_3019, plain, (![A_109, A_110]: (k4_xboole_0(A_109, k2_xboole_0(A_110, k4_xboole_0(A_109, A_110)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2648])).
% 13.82/7.44  tff(c_3232, plain, (![A_112]: (k4_xboole_0(A_112, k4_xboole_0(A_112, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_711, c_3019])).
% 13.82/7.44  tff(c_3255, plain, (![A_112]: (k2_xboole_0(A_112, k4_xboole_0(A_112, k1_xboole_0))=k4_xboole_0(A_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3232, c_85])).
% 13.82/7.44  tff(c_3313, plain, (![A_112]: (k4_xboole_0(A_112, k1_xboole_0)=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_3255])).
% 13.82/7.44  tff(c_729, plain, (![C_62]: (k2_xboole_0(k1_xboole_0, C_62)=C_62)), inference(superposition, [status(thm), theory('equality')], [c_667, c_85])).
% 13.82/7.44  tff(c_236, plain, (![A_40, B_41]: (k4_xboole_0(k2_xboole_0(A_40, B_41), k2_xboole_0(A_40, B_41))=k1_xboole_0)), inference(resolution, [status(thm)], [c_211, c_10])).
% 13.82/7.44  tff(c_738, plain, (![C_62]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, C_62), C_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_729, c_236])).
% 13.82/7.44  tff(c_1168, plain, (![C_71]: (k4_xboole_0(C_71, C_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_711, c_738])).
% 13.82/7.44  tff(c_1189, plain, (![C_71]: (k4_xboole_0(C_71, k1_xboole_0)=k3_xboole_0(C_71, C_71))), inference(superposition, [status(thm), theory('equality')], [c_1168, c_16])).
% 13.82/7.44  tff(c_3332, plain, (![C_71]: (k3_xboole_0(C_71, C_71)=C_71)), inference(demodulation, [status(thm), theory('equality')], [c_3313, c_1189])).
% 13.82/7.44  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.82/7.44  tff(c_89, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.82/7.44  tff(c_97, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_89])).
% 13.82/7.44  tff(c_347, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k3_xboole_0(A_49, k4_xboole_0(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_153, c_16])).
% 13.82/7.44  tff(c_373, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_97, c_347])).
% 13.82/7.44  tff(c_1347, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_373])).
% 13.82/7.44  tff(c_3422, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3332, c_1347])).
% 13.82/7.44  tff(c_5370, plain, (![A_143, B_144, B_145]: (k4_xboole_0(A_143, k2_xboole_0(B_144, k4_xboole_0(A_143, B_145)))=k4_xboole_0(k3_xboole_0(A_143, B_145), B_144))), inference(superposition, [status(thm), theory('equality')], [c_2, c_980])).
% 13.82/7.44  tff(c_2708, plain, (![A_99, A_19]: (k4_xboole_0(A_99, k2_xboole_0(A_19, k4_xboole_0(A_99, A_19)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2648])).
% 13.82/7.44  tff(c_5613, plain, (![A_146, B_147]: (k4_xboole_0(k3_xboole_0(A_146, B_147), B_147)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5370, c_2708])).
% 13.82/7.44  tff(c_5732, plain, (![A_148, B_149]: (k2_xboole_0(k3_xboole_0(A_148, B_149), B_149)=B_149)), inference(superposition, [status(thm), theory('equality')], [c_5613, c_85])).
% 13.82/7.44  tff(c_6019, plain, (![A_152, A_153]: (k2_xboole_0(A_152, k3_xboole_0(A_153, A_152))=A_152)), inference(superposition, [status(thm), theory('equality')], [c_2, c_5732])).
% 13.82/7.44  tff(c_6134, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3422, c_6019])).
% 13.82/7.44  tff(c_8830, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8827, c_6134])).
% 13.82/7.44  tff(c_2193, plain, (![A_92, B_93, C_94]: (k4_xboole_0(k4_xboole_0(A_92, B_93), k4_xboole_0(A_92, k2_xboole_0(B_93, C_94)))=k3_xboole_0(k4_xboole_0(A_92, B_93), C_94))), inference(superposition, [status(thm), theory('equality')], [c_240, c_16])).
% 13.82/7.44  tff(c_13679, plain, (![A_229, A_230, B_231]: (k4_xboole_0(k4_xboole_0(A_229, A_230), k4_xboole_0(A_229, k2_xboole_0(B_231, A_230)))=k3_xboole_0(k4_xboole_0(A_229, A_230), B_231))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2193])).
% 13.82/7.44  tff(c_13806, plain, (![B_231]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0(B_231, '#skF_2')))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_231))), inference(superposition, [status(thm), theory('equality')], [c_8830, c_13679])).
% 13.82/7.44  tff(c_14056, plain, (![B_231]: (k3_xboole_0('#skF_1', k2_xboole_0(B_231, '#skF_2'))=k3_xboole_0('#skF_1', B_231))), inference(demodulation, [status(thm), theory('equality')], [c_8830, c_16, c_13806])).
% 13.82/7.44  tff(c_20, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.82/7.44  tff(c_23, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 13.82/7.44  tff(c_47101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14056, c_23])).
% 13.82/7.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.82/7.44  
% 13.82/7.44  Inference rules
% 13.82/7.44  ----------------------
% 13.82/7.44  #Ref     : 0
% 13.82/7.44  #Sup     : 11655
% 13.82/7.44  #Fact    : 0
% 13.82/7.44  #Define  : 0
% 13.82/7.44  #Split   : 1
% 13.82/7.44  #Chain   : 0
% 13.82/7.44  #Close   : 0
% 13.82/7.44  
% 13.82/7.44  Ordering : KBO
% 13.82/7.44  
% 13.82/7.44  Simplification rules
% 13.82/7.44  ----------------------
% 13.82/7.44  #Subsume      : 76
% 13.82/7.44  #Demod        : 14080
% 13.82/7.44  #Tautology    : 7262
% 13.82/7.44  #SimpNegUnit  : 13
% 13.82/7.44  #BackRed      : 19
% 13.82/7.44  
% 13.82/7.44  #Partial instantiations: 0
% 13.82/7.44  #Strategies tried      : 1
% 13.82/7.44  
% 13.82/7.44  Timing (in seconds)
% 13.82/7.44  ----------------------
% 13.82/7.44  Preprocessing        : 0.26
% 13.82/7.44  Parsing              : 0.14
% 13.82/7.44  CNF conversion       : 0.02
% 13.82/7.44  Main loop            : 6.34
% 13.82/7.44  Inferencing          : 1.03
% 13.82/7.44  Reduction            : 4.04
% 13.82/7.44  Demodulation         : 3.73
% 13.82/7.44  BG Simplification    : 0.15
% 13.82/7.44  Subsumption          : 0.86
% 13.82/7.44  Abstraction          : 0.29
% 13.82/7.44  MUC search           : 0.00
% 13.82/7.44  Cooper               : 0.00
% 13.82/7.44  Total                : 6.63
% 13.82/7.44  Index Insertion      : 0.00
% 13.82/7.44  Index Deletion       : 0.00
% 13.82/7.44  Index Matching       : 0.00
% 13.82/7.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

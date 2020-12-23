%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:47 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   56 (  66 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :   34 (  44 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_14,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_23,B_24,C_25,D_26] : k3_enumset1(A_23,A_23,B_24,C_25,D_26) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] : k4_enumset1(A_27,A_27,B_28,C_29,D_30,E_31) = k3_enumset1(A_27,B_28,C_29,D_30,E_31) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] : k5_enumset1(A_32,A_32,B_33,C_34,D_35,E_36,F_37) = k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [D_41,B_39,A_38,F_43,G_44,E_42,C_40] : k6_enumset1(A_38,A_38,B_39,C_40,D_41,E_42,F_43,G_44) = k5_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_497,plain,(
    ! [A_106,H_104,C_101,G_105,B_100,F_99,D_102,E_103] : k2_xboole_0(k5_enumset1(A_106,B_100,C_101,D_102,E_103,F_99,G_105),k1_tarski(H_104)) = k6_enumset1(A_106,B_100,C_101,D_102,E_103,F_99,G_105,H_104) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_551,plain,(
    ! [B_33,C_34,E_36,F_37,H_104,A_32,D_35] : k6_enumset1(A_32,A_32,B_33,C_34,D_35,E_36,F_37,H_104) = k2_xboole_0(k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37),k1_tarski(H_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_497])).

tff(c_712,plain,(
    ! [A_113,B_110,H_114,D_115,E_109,C_112,F_111] : k2_xboole_0(k4_enumset1(A_113,B_110,C_112,D_115,E_109,F_111),k1_tarski(H_114)) = k5_enumset1(A_113,B_110,C_112,D_115,E_109,F_111,H_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_551])).

tff(c_772,plain,(
    ! [C_29,D_30,B_28,H_114,A_27,E_31] : k5_enumset1(A_27,A_27,B_28,C_29,D_30,E_31,H_114) = k2_xboole_0(k3_enumset1(A_27,B_28,C_29,D_30,E_31),k1_tarski(H_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_712])).

tff(c_792,plain,(
    ! [H_117,E_119,A_121,B_120,D_118,C_116] : k2_xboole_0(k3_enumset1(A_121,B_120,C_116,D_118,E_119),k1_tarski(H_117)) = k4_enumset1(A_121,B_120,C_116,D_118,E_119,H_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_772])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_872,plain,(
    ! [D_127,B_125,E_122,A_123,H_126,C_124] : k4_xboole_0(k3_enumset1(A_123,B_125,C_124,D_127,E_122),k4_enumset1(A_123,B_125,C_124,D_127,E_122,H_126)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_8])).

tff(c_882,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] : k4_xboole_0(k3_enumset1(A_27,A_27,B_28,C_29,D_30),k3_enumset1(A_27,B_28,C_29,D_30,E_31)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_872])).

tff(c_890,plain,(
    ! [C_128,A_132,E_130,B_131,D_129] : k4_xboole_0(k2_enumset1(A_132,B_131,C_128,D_129),k3_enumset1(A_132,B_131,C_128,D_129,E_130)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_882])).

tff(c_900,plain,(
    ! [A_23,B_24,C_25,D_26] : k4_xboole_0(k2_enumset1(A_23,A_23,B_24,C_25),k2_enumset1(A_23,B_24,C_25,D_26)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_890])).

tff(c_908,plain,(
    ! [A_133,B_134,C_135,D_136] : k4_xboole_0(k1_enumset1(A_133,B_134,C_135),k2_enumset1(A_133,B_134,C_135,D_136)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_900])).

tff(c_918,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k1_enumset1(A_20,A_20,B_21),k1_enumset1(A_20,B_21,C_22)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_908])).

tff(c_926,plain,(
    ! [A_137,B_138,C_139] : k4_xboole_0(k2_tarski(A_137,B_138),k1_enumset1(A_137,B_138,C_139)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_918])).

tff(c_936,plain,(
    ! [A_18,B_19] : k4_xboole_0(k2_tarski(A_18,A_18),k2_tarski(A_18,B_19)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_926])).

tff(c_942,plain,(
    ! [A_18,B_19] : k4_xboole_0(k1_tarski(A_18),k2_tarski(A_18,B_19)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_936])).

tff(c_55,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | k4_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_28])).

tff(c_946,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.49  
% 3.27/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.49  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.27/1.49  
% 3.27/1.49  %Foreground sorts:
% 3.27/1.49  
% 3.27/1.49  
% 3.27/1.49  %Background operators:
% 3.27/1.49  
% 3.27/1.49  
% 3.27/1.49  %Foreground operators:
% 3.27/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.27/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.49  
% 3.27/1.51  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.27/1.51  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.27/1.51  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.27/1.51  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.27/1.51  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.27/1.51  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.27/1.51  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.27/1.51  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 3.27/1.51  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.27/1.51  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.27/1.51  tff(f_54, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.27/1.51  tff(c_14, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.51  tff(c_16, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.51  tff(c_18, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.51  tff(c_20, plain, (![A_23, B_24, C_25, D_26]: (k3_enumset1(A_23, A_23, B_24, C_25, D_26)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.27/1.51  tff(c_22, plain, (![C_29, D_30, B_28, A_27, E_31]: (k4_enumset1(A_27, A_27, B_28, C_29, D_30, E_31)=k3_enumset1(A_27, B_28, C_29, D_30, E_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.51  tff(c_24, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (k5_enumset1(A_32, A_32, B_33, C_34, D_35, E_36, F_37)=k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.51  tff(c_26, plain, (![D_41, B_39, A_38, F_43, G_44, E_42, C_40]: (k6_enumset1(A_38, A_38, B_39, C_40, D_41, E_42, F_43, G_44)=k5_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.27/1.51  tff(c_497, plain, (![A_106, H_104, C_101, G_105, B_100, F_99, D_102, E_103]: (k2_xboole_0(k5_enumset1(A_106, B_100, C_101, D_102, E_103, F_99, G_105), k1_tarski(H_104))=k6_enumset1(A_106, B_100, C_101, D_102, E_103, F_99, G_105, H_104))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.51  tff(c_551, plain, (![B_33, C_34, E_36, F_37, H_104, A_32, D_35]: (k6_enumset1(A_32, A_32, B_33, C_34, D_35, E_36, F_37, H_104)=k2_xboole_0(k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37), k1_tarski(H_104)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_497])).
% 3.27/1.51  tff(c_712, plain, (![A_113, B_110, H_114, D_115, E_109, C_112, F_111]: (k2_xboole_0(k4_enumset1(A_113, B_110, C_112, D_115, E_109, F_111), k1_tarski(H_114))=k5_enumset1(A_113, B_110, C_112, D_115, E_109, F_111, H_114))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_551])).
% 3.27/1.51  tff(c_772, plain, (![C_29, D_30, B_28, H_114, A_27, E_31]: (k5_enumset1(A_27, A_27, B_28, C_29, D_30, E_31, H_114)=k2_xboole_0(k3_enumset1(A_27, B_28, C_29, D_30, E_31), k1_tarski(H_114)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_712])).
% 3.27/1.51  tff(c_792, plain, (![H_117, E_119, A_121, B_120, D_118, C_116]: (k2_xboole_0(k3_enumset1(A_121, B_120, C_116, D_118, E_119), k1_tarski(H_117))=k4_enumset1(A_121, B_120, C_116, D_118, E_119, H_117))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_772])).
% 3.27/1.51  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.51  tff(c_872, plain, (![D_127, B_125, E_122, A_123, H_126, C_124]: (k4_xboole_0(k3_enumset1(A_123, B_125, C_124, D_127, E_122), k4_enumset1(A_123, B_125, C_124, D_127, E_122, H_126))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_792, c_8])).
% 3.27/1.51  tff(c_882, plain, (![C_29, D_30, B_28, A_27, E_31]: (k4_xboole_0(k3_enumset1(A_27, A_27, B_28, C_29, D_30), k3_enumset1(A_27, B_28, C_29, D_30, E_31))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_872])).
% 3.27/1.51  tff(c_890, plain, (![C_128, A_132, E_130, B_131, D_129]: (k4_xboole_0(k2_enumset1(A_132, B_131, C_128, D_129), k3_enumset1(A_132, B_131, C_128, D_129, E_130))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_882])).
% 3.27/1.51  tff(c_900, plain, (![A_23, B_24, C_25, D_26]: (k4_xboole_0(k2_enumset1(A_23, A_23, B_24, C_25), k2_enumset1(A_23, B_24, C_25, D_26))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_890])).
% 3.27/1.51  tff(c_908, plain, (![A_133, B_134, C_135, D_136]: (k4_xboole_0(k1_enumset1(A_133, B_134, C_135), k2_enumset1(A_133, B_134, C_135, D_136))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_900])).
% 3.27/1.51  tff(c_918, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k1_enumset1(A_20, A_20, B_21), k1_enumset1(A_20, B_21, C_22))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_908])).
% 3.27/1.51  tff(c_926, plain, (![A_137, B_138, C_139]: (k4_xboole_0(k2_tarski(A_137, B_138), k1_enumset1(A_137, B_138, C_139))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_918])).
% 3.27/1.51  tff(c_936, plain, (![A_18, B_19]: (k4_xboole_0(k2_tarski(A_18, A_18), k2_tarski(A_18, B_19))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_926])).
% 3.27/1.51  tff(c_942, plain, (![A_18, B_19]: (k4_xboole_0(k1_tarski(A_18), k2_tarski(A_18, B_19))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_936])).
% 3.27/1.51  tff(c_55, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | k4_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.51  tff(c_28, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.27/1.51  tff(c_63, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_28])).
% 3.27/1.51  tff(c_946, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_942, c_63])).
% 3.27/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.51  
% 3.27/1.51  Inference rules
% 3.27/1.51  ----------------------
% 3.27/1.51  #Ref     : 0
% 3.27/1.51  #Sup     : 235
% 3.27/1.51  #Fact    : 0
% 3.27/1.51  #Define  : 0
% 3.27/1.51  #Split   : 0
% 3.27/1.51  #Chain   : 0
% 3.27/1.51  #Close   : 0
% 3.27/1.51  
% 3.27/1.51  Ordering : KBO
% 3.27/1.51  
% 3.27/1.51  Simplification rules
% 3.27/1.51  ----------------------
% 3.27/1.51  #Subsume      : 3
% 3.27/1.51  #Demod        : 229
% 3.27/1.51  #Tautology    : 79
% 3.27/1.51  #SimpNegUnit  : 0
% 3.27/1.51  #BackRed      : 1
% 3.27/1.51  
% 3.27/1.51  #Partial instantiations: 0
% 3.27/1.51  #Strategies tried      : 1
% 3.27/1.51  
% 3.27/1.51  Timing (in seconds)
% 3.27/1.51  ----------------------
% 3.27/1.51  Preprocessing        : 0.30
% 3.27/1.51  Parsing              : 0.16
% 3.27/1.51  CNF conversion       : 0.02
% 3.27/1.51  Main loop            : 0.45
% 3.27/1.51  Inferencing          : 0.14
% 3.27/1.51  Reduction            : 0.22
% 3.27/1.51  Demodulation         : 0.18
% 3.27/1.51  BG Simplification    : 0.02
% 3.42/1.51  Subsumption          : 0.04
% 3.42/1.51  Abstraction          : 0.04
% 3.42/1.51  MUC search           : 0.00
% 3.42/1.51  Cooper               : 0.00
% 3.42/1.51  Total                : 0.77
% 3.42/1.51  Index Insertion      : 0.00
% 3.42/1.51  Index Deletion       : 0.00
% 3.42/1.51  Index Matching       : 0.00
% 3.42/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

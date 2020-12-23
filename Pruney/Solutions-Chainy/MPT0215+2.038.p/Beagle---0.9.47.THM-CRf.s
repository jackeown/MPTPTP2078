%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:43 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   58 (  63 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :   42 (  48 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_28,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_24,B_25,C_26,D_27] : k3_enumset1(A_24,A_24,B_25,C_26,D_27) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [C_30,E_32,D_31,B_29,A_28] : k4_enumset1(A_28,A_28,B_29,C_30,D_31,E_32) = k3_enumset1(A_28,B_29,C_30,D_31,E_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] : k5_enumset1(A_33,A_33,B_34,C_35,D_36,E_37,F_38) = k4_enumset1(A_33,B_34,C_35,D_36,E_37,F_38) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [E_43,G_45,F_44,D_42,A_39,C_41,B_40] : k6_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44,G_45) = k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_155,plain,(
    ! [G_93,B_94,E_96,C_100,D_98,F_99,A_97,H_95] : k2_xboole_0(k2_enumset1(A_97,B_94,C_100,D_98),k2_enumset1(E_96,F_99,G_93,H_95)) = k6_enumset1(A_97,B_94,C_100,D_98,E_96,F_99,G_93,H_95) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_53,B_54,C_55] : r1_tarski(k3_xboole_0(A_53,B_54),k2_xboole_0(A_53,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_3,C_55] : r1_tarski(A_3,k2_xboole_0(A_3,C_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_187,plain,(
    ! [D_108,C_105,H_103,G_101,B_102,A_104,F_106,E_107] : r1_tarski(k2_enumset1(A_104,B_102,C_105,D_108),k6_enumset1(A_104,B_102,C_105,D_108,E_107,F_106,G_101,H_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_65])).

tff(c_190,plain,(
    ! [E_43,G_45,F_44,D_42,A_39,C_41,B_40] : r1_tarski(k2_enumset1(A_39,A_39,B_40,C_41),k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_187])).

tff(c_210,plain,(
    ! [D_122,F_123,B_119,G_121,E_124,A_118,C_120] : r1_tarski(k1_enumset1(A_118,B_119,C_120),k5_enumset1(A_118,B_119,C_120,D_122,E_124,F_123,G_121)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_190])).

tff(c_213,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] : r1_tarski(k1_enumset1(A_33,A_33,B_34),k4_enumset1(A_33,B_34,C_35,D_36,E_37,F_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_210])).

tff(c_219,plain,(
    ! [E_126,F_128,D_129,B_130,C_127,A_125] : r1_tarski(k2_tarski(A_125,B_130),k4_enumset1(A_125,B_130,C_127,D_129,E_126,F_128)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_213])).

tff(c_222,plain,(
    ! [C_30,E_32,D_31,B_29,A_28] : r1_tarski(k2_tarski(A_28,A_28),k3_enumset1(A_28,B_29,C_30,D_31,E_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_219])).

tff(c_231,plain,(
    ! [A_132,C_133,E_131,D_135,B_134] : r1_tarski(k1_tarski(A_132),k3_enumset1(A_132,B_134,C_133,D_135,E_131)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_222])).

tff(c_235,plain,(
    ! [A_136,B_137,C_138,D_139] : r1_tarski(k1_tarski(A_136),k2_enumset1(A_136,B_137,C_138,D_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_231])).

tff(c_239,plain,(
    ! [A_140,B_141,C_142] : r1_tarski(k1_tarski(A_140),k1_enumset1(A_140,B_141,C_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_235])).

tff(c_276,plain,(
    ! [A_150,B_151] : r1_tarski(k1_tarski(A_150),k2_tarski(A_150,B_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_239])).

tff(c_282,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_276])).

tff(c_26,plain,(
    ! [B_47,A_46] :
      ( B_47 = A_46
      | ~ r1_tarski(k1_tarski(A_46),k1_tarski(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_291,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_282,c_26])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:02:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.97/1.22  
% 1.97/1.22  %Foreground sorts:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Background operators:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Foreground operators:
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.22  
% 1.97/1.24  tff(f_58, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 1.97/1.24  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.97/1.24  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.97/1.24  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.97/1.24  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.24  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.97/1.24  tff(f_47, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.97/1.24  tff(f_49, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.97/1.24  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 1.97/1.24  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.97/1.24  tff(f_31, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.97/1.24  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.97/1.24  tff(c_28, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.24  tff(c_30, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.24  tff(c_14, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.24  tff(c_16, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.24  tff(c_18, plain, (![A_24, B_25, C_26, D_27]: (k3_enumset1(A_24, A_24, B_25, C_26, D_27)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.24  tff(c_12, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.24  tff(c_20, plain, (![C_30, E_32, D_31, B_29, A_28]: (k4_enumset1(A_28, A_28, B_29, C_30, D_31, E_32)=k3_enumset1(A_28, B_29, C_30, D_31, E_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.97/1.24  tff(c_22, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (k5_enumset1(A_33, A_33, B_34, C_35, D_36, E_37, F_38)=k4_enumset1(A_33, B_34, C_35, D_36, E_37, F_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.24  tff(c_24, plain, (![E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (k6_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44, G_45)=k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.24  tff(c_155, plain, (![G_93, B_94, E_96, C_100, D_98, F_99, A_97, H_95]: (k2_xboole_0(k2_enumset1(A_97, B_94, C_100, D_98), k2_enumset1(E_96, F_99, G_93, H_95))=k6_enumset1(A_97, B_94, C_100, D_98, E_96, F_99, G_93, H_95))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.24  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.24  tff(c_62, plain, (![A_53, B_54, C_55]: (r1_tarski(k3_xboole_0(A_53, B_54), k2_xboole_0(A_53, C_55)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.24  tff(c_65, plain, (![A_3, C_55]: (r1_tarski(A_3, k2_xboole_0(A_3, C_55)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 1.97/1.24  tff(c_187, plain, (![D_108, C_105, H_103, G_101, B_102, A_104, F_106, E_107]: (r1_tarski(k2_enumset1(A_104, B_102, C_105, D_108), k6_enumset1(A_104, B_102, C_105, D_108, E_107, F_106, G_101, H_103)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_65])).
% 1.97/1.24  tff(c_190, plain, (![E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (r1_tarski(k2_enumset1(A_39, A_39, B_40, C_41), k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_187])).
% 1.97/1.24  tff(c_210, plain, (![D_122, F_123, B_119, G_121, E_124, A_118, C_120]: (r1_tarski(k1_enumset1(A_118, B_119, C_120), k5_enumset1(A_118, B_119, C_120, D_122, E_124, F_123, G_121)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_190])).
% 1.97/1.24  tff(c_213, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (r1_tarski(k1_enumset1(A_33, A_33, B_34), k4_enumset1(A_33, B_34, C_35, D_36, E_37, F_38)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_210])).
% 1.97/1.24  tff(c_219, plain, (![E_126, F_128, D_129, B_130, C_127, A_125]: (r1_tarski(k2_tarski(A_125, B_130), k4_enumset1(A_125, B_130, C_127, D_129, E_126, F_128)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_213])).
% 1.97/1.24  tff(c_222, plain, (![C_30, E_32, D_31, B_29, A_28]: (r1_tarski(k2_tarski(A_28, A_28), k3_enumset1(A_28, B_29, C_30, D_31, E_32)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_219])).
% 1.97/1.24  tff(c_231, plain, (![A_132, C_133, E_131, D_135, B_134]: (r1_tarski(k1_tarski(A_132), k3_enumset1(A_132, B_134, C_133, D_135, E_131)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_222])).
% 1.97/1.24  tff(c_235, plain, (![A_136, B_137, C_138, D_139]: (r1_tarski(k1_tarski(A_136), k2_enumset1(A_136, B_137, C_138, D_139)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_231])).
% 1.97/1.24  tff(c_239, plain, (![A_140, B_141, C_142]: (r1_tarski(k1_tarski(A_140), k1_enumset1(A_140, B_141, C_142)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_235])).
% 1.97/1.24  tff(c_276, plain, (![A_150, B_151]: (r1_tarski(k1_tarski(A_150), k2_tarski(A_150, B_151)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_239])).
% 1.97/1.24  tff(c_282, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_276])).
% 1.97/1.24  tff(c_26, plain, (![B_47, A_46]: (B_47=A_46 | ~r1_tarski(k1_tarski(A_46), k1_tarski(B_47)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.97/1.24  tff(c_291, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_282, c_26])).
% 1.97/1.24  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_291])).
% 1.97/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.24  
% 1.97/1.24  Inference rules
% 1.97/1.24  ----------------------
% 1.97/1.24  #Ref     : 0
% 1.97/1.24  #Sup     : 64
% 1.97/1.24  #Fact    : 0
% 1.97/1.24  #Define  : 0
% 1.97/1.24  #Split   : 0
% 1.97/1.24  #Chain   : 0
% 1.97/1.24  #Close   : 0
% 1.97/1.24  
% 1.97/1.24  Ordering : KBO
% 1.97/1.24  
% 1.97/1.24  Simplification rules
% 1.97/1.24  ----------------------
% 1.97/1.24  #Subsume      : 0
% 1.97/1.24  #Demod        : 14
% 1.97/1.24  #Tautology    : 33
% 1.97/1.24  #SimpNegUnit  : 1
% 1.97/1.24  #BackRed      : 0
% 1.97/1.24  
% 1.97/1.24  #Partial instantiations: 0
% 1.97/1.24  #Strategies tried      : 1
% 1.97/1.24  
% 1.97/1.24  Timing (in seconds)
% 1.97/1.24  ----------------------
% 1.97/1.24  Preprocessing        : 0.29
% 1.97/1.24  Parsing              : 0.16
% 1.97/1.24  CNF conversion       : 0.02
% 1.97/1.24  Main loop            : 0.19
% 1.97/1.24  Inferencing          : 0.09
% 1.97/1.24  Reduction            : 0.06
% 1.97/1.24  Demodulation         : 0.05
% 1.97/1.24  BG Simplification    : 0.02
% 1.97/1.24  Subsumption          : 0.02
% 1.97/1.24  Abstraction          : 0.01
% 1.97/1.24  MUC search           : 0.00
% 1.97/1.24  Cooper               : 0.00
% 1.97/1.24  Total                : 0.52
% 1.97/1.24  Index Insertion      : 0.00
% 1.97/1.24  Index Deletion       : 0.00
% 1.97/1.24  Index Matching       : 0.00
% 1.97/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

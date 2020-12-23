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
% DateTime   : Thu Dec  3 09:47:43 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   55 (  60 expanded)
%              Number of leaves         :   30 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :   39 (  45 expanded)
%              Number of equality atoms :   23 (  29 expanded)
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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23,D_24] : k3_enumset1(A_21,A_21,B_22,C_23,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : k4_enumset1(A_25,A_25,B_26,C_27,D_28,E_29) = k3_enumset1(A_25,B_26,C_27,D_28,E_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35) = k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,C_38,B_37] : k6_enumset1(A_36,A_36,B_37,C_38,D_39,E_40,F_41,G_42) = k5_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    ! [D_81,F_86,E_87,B_82,G_85,H_88,C_83,A_84] : k2_xboole_0(k2_enumset1(A_84,B_82,C_83,D_81),k2_enumset1(E_87,F_86,G_85,H_88)) = k6_enumset1(A_84,B_82,C_83,D_81,E_87,F_86,G_85,H_88) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_135,plain,(
    ! [H_93,C_92,E_94,D_91,F_90,B_96,A_89,G_95] : r1_tarski(k2_enumset1(A_89,B_96,C_92,D_91),k6_enumset1(A_89,B_96,C_92,D_91,E_94,F_90,G_95,H_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_4])).

tff(c_138,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,C_38,B_37] : r1_tarski(k2_enumset1(A_36,A_36,B_37,C_38),k5_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_135])).

tff(c_163,plain,(
    ! [A_106,B_108,F_105,C_109,E_110,D_107,G_104] : r1_tarski(k1_enumset1(A_106,B_108,C_109),k5_enumset1(A_106,B_108,C_109,D_107,E_110,F_105,G_104)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_138])).

tff(c_166,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : r1_tarski(k1_enumset1(A_30,A_30,B_31),k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_163])).

tff(c_172,plain,(
    ! [E_115,F_113,D_116,C_111,A_114,B_112] : r1_tarski(k2_tarski(A_114,B_112),k4_enumset1(A_114,B_112,C_111,D_116,E_115,F_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_175,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : r1_tarski(k2_tarski(A_25,A_25),k3_enumset1(A_25,B_26,C_27,D_28,E_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_172])).

tff(c_184,plain,(
    ! [E_121,B_120,C_119,A_118,D_117] : r1_tarski(k1_tarski(A_118),k3_enumset1(A_118,B_120,C_119,D_117,E_121)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_175])).

tff(c_189,plain,(
    ! [A_126,B_127,C_128,D_129] : r1_tarski(k1_tarski(A_126),k2_enumset1(A_126,B_127,C_128,D_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_184])).

tff(c_193,plain,(
    ! [A_130,B_131,C_132] : r1_tarski(k1_tarski(A_130),k1_enumset1(A_130,B_131,C_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_189])).

tff(c_197,plain,(
    ! [A_133,B_134] : r1_tarski(k1_tarski(A_133),k2_tarski(A_133,B_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_193])).

tff(c_203,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_197])).

tff(c_24,plain,(
    ! [B_44,A_43] :
      ( B_44 = A_43
      | ~ r1_tarski(k1_tarski(A_43),k1_tarski(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_203,c_24])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.28  
% 2.05/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.29  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.05/1.29  
% 2.05/1.29  %Foreground sorts:
% 2.05/1.29  
% 2.05/1.29  
% 2.05/1.29  %Background operators:
% 2.05/1.29  
% 2.05/1.29  
% 2.05/1.29  %Foreground operators:
% 2.05/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.05/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.05/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.29  
% 2.05/1.30  tff(f_56, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 2.05/1.30  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.05/1.30  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.05/1.30  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.05/1.30  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.30  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.05/1.30  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.05/1.30  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.05/1.30  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 2.05/1.30  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.05/1.30  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.05/1.30  tff(c_26, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.05/1.30  tff(c_28, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.05/1.30  tff(c_12, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.30  tff(c_14, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.05/1.30  tff(c_16, plain, (![A_21, B_22, C_23, D_24]: (k3_enumset1(A_21, A_21, B_22, C_23, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.30  tff(c_10, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.30  tff(c_18, plain, (![A_25, E_29, C_27, D_28, B_26]: (k4_enumset1(A_25, A_25, B_26, C_27, D_28, E_29)=k3_enumset1(A_25, B_26, C_27, D_28, E_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.05/1.30  tff(c_20, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35)=k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.05/1.30  tff(c_22, plain, (![F_41, G_42, D_39, A_36, E_40, C_38, B_37]: (k6_enumset1(A_36, A_36, B_37, C_38, D_39, E_40, F_41, G_42)=k5_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.30  tff(c_116, plain, (![D_81, F_86, E_87, B_82, G_85, H_88, C_83, A_84]: (k2_xboole_0(k2_enumset1(A_84, B_82, C_83, D_81), k2_enumset1(E_87, F_86, G_85, H_88))=k6_enumset1(A_84, B_82, C_83, D_81, E_87, F_86, G_85, H_88))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.30  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.30  tff(c_135, plain, (![H_93, C_92, E_94, D_91, F_90, B_96, A_89, G_95]: (r1_tarski(k2_enumset1(A_89, B_96, C_92, D_91), k6_enumset1(A_89, B_96, C_92, D_91, E_94, F_90, G_95, H_93)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_4])).
% 2.05/1.30  tff(c_138, plain, (![F_41, G_42, D_39, A_36, E_40, C_38, B_37]: (r1_tarski(k2_enumset1(A_36, A_36, B_37, C_38), k5_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_135])).
% 2.05/1.30  tff(c_163, plain, (![A_106, B_108, F_105, C_109, E_110, D_107, G_104]: (r1_tarski(k1_enumset1(A_106, B_108, C_109), k5_enumset1(A_106, B_108, C_109, D_107, E_110, F_105, G_104)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_138])).
% 2.05/1.30  tff(c_166, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (r1_tarski(k1_enumset1(A_30, A_30, B_31), k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_163])).
% 2.05/1.30  tff(c_172, plain, (![E_115, F_113, D_116, C_111, A_114, B_112]: (r1_tarski(k2_tarski(A_114, B_112), k4_enumset1(A_114, B_112, C_111, D_116, E_115, F_113)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_166])).
% 2.05/1.30  tff(c_175, plain, (![A_25, E_29, C_27, D_28, B_26]: (r1_tarski(k2_tarski(A_25, A_25), k3_enumset1(A_25, B_26, C_27, D_28, E_29)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_172])).
% 2.05/1.30  tff(c_184, plain, (![E_121, B_120, C_119, A_118, D_117]: (r1_tarski(k1_tarski(A_118), k3_enumset1(A_118, B_120, C_119, D_117, E_121)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_175])).
% 2.05/1.30  tff(c_189, plain, (![A_126, B_127, C_128, D_129]: (r1_tarski(k1_tarski(A_126), k2_enumset1(A_126, B_127, C_128, D_129)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_184])).
% 2.05/1.30  tff(c_193, plain, (![A_130, B_131, C_132]: (r1_tarski(k1_tarski(A_130), k1_enumset1(A_130, B_131, C_132)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_189])).
% 2.05/1.30  tff(c_197, plain, (![A_133, B_134]: (r1_tarski(k1_tarski(A_133), k2_tarski(A_133, B_134)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_193])).
% 2.05/1.30  tff(c_203, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_197])).
% 2.05/1.30  tff(c_24, plain, (![B_44, A_43]: (B_44=A_43 | ~r1_tarski(k1_tarski(A_43), k1_tarski(B_44)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.30  tff(c_212, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_203, c_24])).
% 2.05/1.30  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_212])).
% 2.05/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.30  
% 2.05/1.30  Inference rules
% 2.05/1.30  ----------------------
% 2.05/1.30  #Ref     : 0
% 2.05/1.30  #Sup     : 44
% 2.05/1.30  #Fact    : 0
% 2.05/1.30  #Define  : 0
% 2.05/1.30  #Split   : 0
% 2.05/1.30  #Chain   : 0
% 2.05/1.30  #Close   : 0
% 2.05/1.30  
% 2.05/1.30  Ordering : KBO
% 2.05/1.30  
% 2.05/1.30  Simplification rules
% 2.05/1.30  ----------------------
% 2.05/1.30  #Subsume      : 0
% 2.05/1.30  #Demod        : 8
% 2.05/1.30  #Tautology    : 25
% 2.05/1.30  #SimpNegUnit  : 1
% 2.05/1.30  #BackRed      : 0
% 2.05/1.30  
% 2.05/1.30  #Partial instantiations: 0
% 2.05/1.30  #Strategies tried      : 1
% 2.05/1.30  
% 2.05/1.30  Timing (in seconds)
% 2.05/1.30  ----------------------
% 2.05/1.30  Preprocessing        : 0.33
% 2.05/1.30  Parsing              : 0.18
% 2.05/1.30  CNF conversion       : 0.02
% 2.05/1.30  Main loop            : 0.17
% 2.05/1.30  Inferencing          : 0.07
% 2.05/1.30  Reduction            : 0.05
% 2.05/1.30  Demodulation         : 0.04
% 2.05/1.30  BG Simplification    : 0.02
% 2.28/1.30  Subsumption          : 0.02
% 2.28/1.30  Abstraction          : 0.01
% 2.28/1.30  MUC search           : 0.00
% 2.28/1.30  Cooper               : 0.00
% 2.28/1.30  Total                : 0.53
% 2.28/1.31  Index Insertion      : 0.00
% 2.28/1.31  Index Deletion       : 0.00
% 2.28/1.31  Index Matching       : 0.00
% 2.28/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

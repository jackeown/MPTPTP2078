%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:43 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   56 (  67 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :   43 (  55 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_10,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18] : k2_enumset1(A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_19,B_20,C_21,D_22] : k3_enumset1(A_19,A_19,B_20,C_21,D_22) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] : k4_enumset1(A_23,A_23,B_24,C_25,D_26,E_27) = k3_enumset1(A_23,B_24,C_25,D_26,E_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] : k5_enumset1(A_28,A_28,B_29,C_30,D_31,E_32,F_33) = k4_enumset1(A_28,B_29,C_30,D_31,E_32,F_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [D_37,A_34,F_39,B_35,G_40,C_36,E_38] : k6_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,F_39,G_40) = k5_enumset1(A_34,B_35,C_36,D_37,E_38,F_39,G_40) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_143,plain,(
    ! [H_86,A_85,D_80,B_83,C_84,G_82,E_87,F_81] : k2_xboole_0(k5_enumset1(A_85,B_83,C_84,D_80,E_87,F_81,G_82),k1_tarski(H_86)) = k6_enumset1(A_85,B_83,C_84,D_80,E_87,F_81,G_82,H_86) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    ! [H_86,C_30,E_32,D_31,B_29,F_33,A_28] : k6_enumset1(A_28,A_28,B_29,C_30,D_31,E_32,F_33,H_86) = k2_xboole_0(k4_enumset1(A_28,B_29,C_30,D_31,E_32,F_33),k1_tarski(H_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_143])).

tff(c_156,plain,(
    ! [H_93,B_92,C_91,F_88,D_94,E_89,A_90] : k2_xboole_0(k4_enumset1(A_90,B_92,C_91,D_94,E_89,F_88),k1_tarski(H_93)) = k5_enumset1(A_90,B_92,C_91,D_94,E_89,F_88,H_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_152])).

tff(c_165,plain,(
    ! [H_93,A_23,B_24,D_26,C_25,E_27] : k5_enumset1(A_23,A_23,B_24,C_25,D_26,E_27,H_93) = k2_xboole_0(k3_enumset1(A_23,B_24,C_25,D_26,E_27),k1_tarski(H_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_156])).

tff(c_169,plain,(
    ! [H_100,C_95,A_99,E_96,B_97,D_98] : k2_xboole_0(k3_enumset1(A_99,B_97,C_95,D_98,E_96),k1_tarski(H_100)) = k4_enumset1(A_99,B_97,C_95,D_98,E_96,H_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_165])).

tff(c_178,plain,(
    ! [A_19,H_100,C_21,D_22,B_20] : k4_enumset1(A_19,A_19,B_20,C_21,D_22,H_100) = k2_xboole_0(k2_enumset1(A_19,B_20,C_21,D_22),k1_tarski(H_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_169])).

tff(c_182,plain,(
    ! [B_102,H_104,C_101,A_103,D_105] : k2_xboole_0(k2_enumset1(A_103,B_102,C_101,D_105),k1_tarski(H_104)) = k3_enumset1(A_103,B_102,C_101,D_105,H_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_178])).

tff(c_191,plain,(
    ! [A_16,B_17,C_18,H_104] : k3_enumset1(A_16,A_16,B_17,C_18,H_104) = k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k1_tarski(H_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_182])).

tff(c_195,plain,(
    ! [A_106,B_107,C_108,H_109] : k2_xboole_0(k1_enumset1(A_106,B_107,C_108),k1_tarski(H_109)) = k2_enumset1(A_106,B_107,C_108,H_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_191])).

tff(c_204,plain,(
    ! [A_14,B_15,H_109] : k2_xboole_0(k2_tarski(A_14,B_15),k1_tarski(H_109)) = k2_enumset1(A_14,A_14,B_15,H_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_195])).

tff(c_208,plain,(
    ! [A_110,B_111,H_112] : k2_xboole_0(k2_tarski(A_110,B_111),k1_tarski(H_112)) = k1_enumset1(A_110,B_111,H_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_204])).

tff(c_217,plain,(
    ! [A_13,H_112] : k2_xboole_0(k1_tarski(A_13),k1_tarski(H_112)) = k1_enumset1(A_13,A_13,H_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_208])).

tff(c_220,plain,(
    ! [A_13,H_112] : k2_xboole_0(k1_tarski(A_13),k1_tarski(H_112)) = k2_tarski(A_13,H_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_217])).

tff(c_28,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_67,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(k1_tarski(A_51),k1_tarski(B_52)) = k1_tarski(A_51)
      | B_52 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [B_60,A_61] :
      ( k5_xboole_0(k1_tarski(B_60),k1_tarski(A_61)) = k2_xboole_0(k1_tarski(B_60),k1_tarski(A_61))
      | B_60 = A_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_4])).

tff(c_26,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_109,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_26])).

tff(c_114,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_109])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:20:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.23  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.10/1.23  
% 2.10/1.23  %Foreground sorts:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Background operators:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Foreground operators:
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.10/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.23  
% 2.10/1.25  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.10/1.25  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.10/1.25  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.10/1.25  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.10/1.25  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.10/1.25  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.10/1.25  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.10/1.25  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 2.10/1.25  tff(f_56, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.10/1.25  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.10/1.25  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.10/1.25  tff(c_10, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.25  tff(c_8, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.25  tff(c_12, plain, (![A_16, B_17, C_18]: (k2_enumset1(A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.25  tff(c_14, plain, (![A_19, B_20, C_21, D_22]: (k3_enumset1(A_19, A_19, B_20, C_21, D_22)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.25  tff(c_16, plain, (![A_23, B_24, D_26, C_25, E_27]: (k4_enumset1(A_23, A_23, B_24, C_25, D_26, E_27)=k3_enumset1(A_23, B_24, C_25, D_26, E_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.25  tff(c_18, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (k5_enumset1(A_28, A_28, B_29, C_30, D_31, E_32, F_33)=k4_enumset1(A_28, B_29, C_30, D_31, E_32, F_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.25  tff(c_20, plain, (![D_37, A_34, F_39, B_35, G_40, C_36, E_38]: (k6_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, F_39, G_40)=k5_enumset1(A_34, B_35, C_36, D_37, E_38, F_39, G_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.25  tff(c_143, plain, (![H_86, A_85, D_80, B_83, C_84, G_82, E_87, F_81]: (k2_xboole_0(k5_enumset1(A_85, B_83, C_84, D_80, E_87, F_81, G_82), k1_tarski(H_86))=k6_enumset1(A_85, B_83, C_84, D_80, E_87, F_81, G_82, H_86))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.25  tff(c_152, plain, (![H_86, C_30, E_32, D_31, B_29, F_33, A_28]: (k6_enumset1(A_28, A_28, B_29, C_30, D_31, E_32, F_33, H_86)=k2_xboole_0(k4_enumset1(A_28, B_29, C_30, D_31, E_32, F_33), k1_tarski(H_86)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_143])).
% 2.10/1.25  tff(c_156, plain, (![H_93, B_92, C_91, F_88, D_94, E_89, A_90]: (k2_xboole_0(k4_enumset1(A_90, B_92, C_91, D_94, E_89, F_88), k1_tarski(H_93))=k5_enumset1(A_90, B_92, C_91, D_94, E_89, F_88, H_93))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_152])).
% 2.10/1.25  tff(c_165, plain, (![H_93, A_23, B_24, D_26, C_25, E_27]: (k5_enumset1(A_23, A_23, B_24, C_25, D_26, E_27, H_93)=k2_xboole_0(k3_enumset1(A_23, B_24, C_25, D_26, E_27), k1_tarski(H_93)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_156])).
% 2.10/1.25  tff(c_169, plain, (![H_100, C_95, A_99, E_96, B_97, D_98]: (k2_xboole_0(k3_enumset1(A_99, B_97, C_95, D_98, E_96), k1_tarski(H_100))=k4_enumset1(A_99, B_97, C_95, D_98, E_96, H_100))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_165])).
% 2.10/1.25  tff(c_178, plain, (![A_19, H_100, C_21, D_22, B_20]: (k4_enumset1(A_19, A_19, B_20, C_21, D_22, H_100)=k2_xboole_0(k2_enumset1(A_19, B_20, C_21, D_22), k1_tarski(H_100)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_169])).
% 2.10/1.25  tff(c_182, plain, (![B_102, H_104, C_101, A_103, D_105]: (k2_xboole_0(k2_enumset1(A_103, B_102, C_101, D_105), k1_tarski(H_104))=k3_enumset1(A_103, B_102, C_101, D_105, H_104))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_178])).
% 2.10/1.25  tff(c_191, plain, (![A_16, B_17, C_18, H_104]: (k3_enumset1(A_16, A_16, B_17, C_18, H_104)=k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k1_tarski(H_104)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_182])).
% 2.10/1.25  tff(c_195, plain, (![A_106, B_107, C_108, H_109]: (k2_xboole_0(k1_enumset1(A_106, B_107, C_108), k1_tarski(H_109))=k2_enumset1(A_106, B_107, C_108, H_109))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_191])).
% 2.10/1.25  tff(c_204, plain, (![A_14, B_15, H_109]: (k2_xboole_0(k2_tarski(A_14, B_15), k1_tarski(H_109))=k2_enumset1(A_14, A_14, B_15, H_109))), inference(superposition, [status(thm), theory('equality')], [c_10, c_195])).
% 2.10/1.25  tff(c_208, plain, (![A_110, B_111, H_112]: (k2_xboole_0(k2_tarski(A_110, B_111), k1_tarski(H_112))=k1_enumset1(A_110, B_111, H_112))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_204])).
% 2.10/1.25  tff(c_217, plain, (![A_13, H_112]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(H_112))=k1_enumset1(A_13, A_13, H_112))), inference(superposition, [status(thm), theory('equality')], [c_8, c_208])).
% 2.10/1.25  tff(c_220, plain, (![A_13, H_112]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(H_112))=k2_tarski(A_13, H_112))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_217])).
% 2.10/1.25  tff(c_28, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.25  tff(c_67, plain, (![A_51, B_52]: (k4_xboole_0(k1_tarski(A_51), k1_tarski(B_52))=k1_tarski(A_51) | B_52=A_51)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.25  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.25  tff(c_103, plain, (![B_60, A_61]: (k5_xboole_0(k1_tarski(B_60), k1_tarski(A_61))=k2_xboole_0(k1_tarski(B_60), k1_tarski(A_61)) | B_60=A_61)), inference(superposition, [status(thm), theory('equality')], [c_67, c_4])).
% 2.10/1.25  tff(c_26, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.25  tff(c_109, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_103, c_26])).
% 2.10/1.25  tff(c_114, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_109])).
% 2.10/1.25  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_114])).
% 2.10/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  Inference rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Ref     : 0
% 2.10/1.25  #Sup     : 43
% 2.10/1.25  #Fact    : 0
% 2.10/1.25  #Define  : 0
% 2.10/1.25  #Split   : 0
% 2.10/1.25  #Chain   : 0
% 2.10/1.25  #Close   : 0
% 2.10/1.25  
% 2.10/1.25  Ordering : KBO
% 2.10/1.25  
% 2.10/1.25  Simplification rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Subsume      : 0
% 2.10/1.25  #Demod        : 8
% 2.10/1.25  #Tautology    : 35
% 2.10/1.25  #SimpNegUnit  : 1
% 2.10/1.25  #BackRed      : 2
% 2.10/1.25  
% 2.10/1.25  #Partial instantiations: 0
% 2.10/1.25  #Strategies tried      : 1
% 2.10/1.25  
% 2.10/1.25  Timing (in seconds)
% 2.10/1.25  ----------------------
% 2.10/1.25  Preprocessing        : 0.32
% 2.10/1.25  Parsing              : 0.17
% 2.10/1.25  CNF conversion       : 0.02
% 2.10/1.25  Main loop            : 0.17
% 2.10/1.25  Inferencing          : 0.08
% 2.10/1.25  Reduction            : 0.05
% 2.10/1.25  Demodulation         : 0.03
% 2.10/1.25  BG Simplification    : 0.01
% 2.10/1.25  Subsumption          : 0.02
% 2.10/1.25  Abstraction          : 0.01
% 2.10/1.25  MUC search           : 0.00
% 2.10/1.26  Cooper               : 0.00
% 2.10/1.26  Total                : 0.52
% 2.10/1.26  Index Insertion      : 0.00
% 2.10/1.26  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

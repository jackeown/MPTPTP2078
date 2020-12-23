%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:40 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  66 expanded)
%              Number of leaves         :   32 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :   45 (  51 expanded)
%              Number of equality atoms :   29 (  35 expanded)
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_30,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_22,B_23,C_24] : k2_enumset1(A_22,A_22,B_23,C_24) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_25,B_26,C_27,D_28] : k3_enumset1(A_25,A_25,B_26,C_27,D_28) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [E_33,A_29,D_32,C_31,B_30] : k4_enumset1(A_29,A_29,B_30,C_31,D_32,E_33) = k3_enumset1(A_29,B_30,C_31,D_32,E_33) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] : k5_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,F_39) = k4_enumset1(A_34,B_35,C_36,D_37,E_38,F_39) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [E_44,C_42,G_46,F_45,A_40,D_43,B_41] : k6_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,F_45,G_46) = k5_enumset1(A_40,B_41,C_42,D_43,E_44,F_45,G_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_262,plain,(
    ! [E_108,C_103,H_109,F_102,A_105,D_107,G_104,B_106] : k2_xboole_0(k2_enumset1(A_105,B_106,C_103,D_107),k2_enumset1(E_108,F_102,G_104,H_109)) = k6_enumset1(A_105,B_106,C_103,D_107,E_108,F_102,G_104,H_109) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_286,plain,(
    ! [E_108,H_109,F_102,A_22,B_23,C_24,G_104] : k6_enumset1(A_22,A_22,B_23,C_24,E_108,F_102,G_104,H_109) = k2_xboole_0(k1_enumset1(A_22,B_23,C_24),k2_enumset1(E_108,F_102,G_104,H_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_262])).

tff(c_295,plain,(
    ! [A_110,F_112,H_115,B_116,G_111,E_114,C_113] : k2_xboole_0(k1_enumset1(A_110,B_116,C_113),k2_enumset1(E_114,F_112,G_111,H_115)) = k5_enumset1(A_110,B_116,C_113,E_114,F_112,G_111,H_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_286])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    ! [B_52,A_53] : k3_xboole_0(B_52,A_53) = k3_xboole_0(A_53,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [B_57,A_58] : r1_tarski(k3_xboole_0(B_57,A_58),A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_6])).

tff(c_102,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_99])).

tff(c_328,plain,(
    ! [B_122,G_123,A_117,F_121,C_119,H_120,E_118] : r1_tarski(k1_enumset1(A_117,B_122,C_119),k5_enumset1(A_117,B_122,C_119,E_118,F_121,G_123,H_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_102])).

tff(c_331,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] : r1_tarski(k1_enumset1(A_34,A_34,B_35),k4_enumset1(A_34,B_35,C_36,D_37,E_38,F_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_328])).

tff(c_337,plain,(
    ! [E_127,A_124,D_125,F_126,C_129,B_128] : r1_tarski(k2_tarski(A_124,B_128),k4_enumset1(A_124,B_128,C_129,D_125,E_127,F_126)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_331])).

tff(c_340,plain,(
    ! [E_33,A_29,D_32,C_31,B_30] : r1_tarski(k2_tarski(A_29,A_29),k3_enumset1(A_29,B_30,C_31,D_32,E_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_337])).

tff(c_349,plain,(
    ! [D_130,E_133,A_132,B_131,C_134] : r1_tarski(k1_tarski(A_132),k3_enumset1(A_132,B_131,C_134,D_130,E_133)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_340])).

tff(c_354,plain,(
    ! [A_139,B_140,C_141,D_142] : r1_tarski(k1_tarski(A_139),k2_enumset1(A_139,B_140,C_141,D_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_349])).

tff(c_358,plain,(
    ! [A_143,B_144,C_145] : r1_tarski(k1_tarski(A_143),k1_enumset1(A_143,B_144,C_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_354])).

tff(c_362,plain,(
    ! [A_146,B_147] : r1_tarski(k1_tarski(A_146),k2_tarski(A_146,B_147)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_358])).

tff(c_368,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_362])).

tff(c_28,plain,(
    ! [B_48,A_47] :
      ( B_48 = A_47
      | ~ r1_tarski(k1_tarski(A_47),k1_tarski(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_372,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_368,c_28])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:58:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.25  
% 2.20/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.25  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.20/1.25  
% 2.20/1.25  %Foreground sorts:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Background operators:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Foreground operators:
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.25  
% 2.20/1.27  tff(f_60, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 2.20/1.27  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.20/1.27  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.20/1.27  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.20/1.27  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.20/1.27  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.20/1.27  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.20/1.27  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.20/1.27  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 2.20/1.27  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.20/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.20/1.27  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.20/1.27  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.20/1.27  tff(c_30, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.27  tff(c_32, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.27  tff(c_16, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.27  tff(c_18, plain, (![A_22, B_23, C_24]: (k2_enumset1(A_22, A_22, B_23, C_24)=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.27  tff(c_20, plain, (![A_25, B_26, C_27, D_28]: (k3_enumset1(A_25, A_25, B_26, C_27, D_28)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.27  tff(c_14, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.27  tff(c_22, plain, (![E_33, A_29, D_32, C_31, B_30]: (k4_enumset1(A_29, A_29, B_30, C_31, D_32, E_33)=k3_enumset1(A_29, B_30, C_31, D_32, E_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.27  tff(c_24, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (k5_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, F_39)=k4_enumset1(A_34, B_35, C_36, D_37, E_38, F_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.27  tff(c_26, plain, (![E_44, C_42, G_46, F_45, A_40, D_43, B_41]: (k6_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, F_45, G_46)=k5_enumset1(A_40, B_41, C_42, D_43, E_44, F_45, G_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.27  tff(c_262, plain, (![E_108, C_103, H_109, F_102, A_105, D_107, G_104, B_106]: (k2_xboole_0(k2_enumset1(A_105, B_106, C_103, D_107), k2_enumset1(E_108, F_102, G_104, H_109))=k6_enumset1(A_105, B_106, C_103, D_107, E_108, F_102, G_104, H_109))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.27  tff(c_286, plain, (![E_108, H_109, F_102, A_22, B_23, C_24, G_104]: (k6_enumset1(A_22, A_22, B_23, C_24, E_108, F_102, G_104, H_109)=k2_xboole_0(k1_enumset1(A_22, B_23, C_24), k2_enumset1(E_108, F_102, G_104, H_109)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_262])).
% 2.20/1.27  tff(c_295, plain, (![A_110, F_112, H_115, B_116, G_111, E_114, C_113]: (k2_xboole_0(k1_enumset1(A_110, B_116, C_113), k2_enumset1(E_114, F_112, G_111, H_115))=k5_enumset1(A_110, B_116, C_113, E_114, F_112, G_111, H_115))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_286])).
% 2.20/1.27  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.27  tff(c_47, plain, (![B_52, A_53]: (k3_xboole_0(B_52, A_53)=k3_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.20/1.27  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.27  tff(c_99, plain, (![B_57, A_58]: (r1_tarski(k3_xboole_0(B_57, A_58), A_58))), inference(superposition, [status(thm), theory('equality')], [c_47, c_6])).
% 2.20/1.27  tff(c_102, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_99])).
% 2.20/1.27  tff(c_328, plain, (![B_122, G_123, A_117, F_121, C_119, H_120, E_118]: (r1_tarski(k1_enumset1(A_117, B_122, C_119), k5_enumset1(A_117, B_122, C_119, E_118, F_121, G_123, H_120)))), inference(superposition, [status(thm), theory('equality')], [c_295, c_102])).
% 2.20/1.27  tff(c_331, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (r1_tarski(k1_enumset1(A_34, A_34, B_35), k4_enumset1(A_34, B_35, C_36, D_37, E_38, F_39)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_328])).
% 2.20/1.27  tff(c_337, plain, (![E_127, A_124, D_125, F_126, C_129, B_128]: (r1_tarski(k2_tarski(A_124, B_128), k4_enumset1(A_124, B_128, C_129, D_125, E_127, F_126)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_331])).
% 2.20/1.27  tff(c_340, plain, (![E_33, A_29, D_32, C_31, B_30]: (r1_tarski(k2_tarski(A_29, A_29), k3_enumset1(A_29, B_30, C_31, D_32, E_33)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_337])).
% 2.20/1.27  tff(c_349, plain, (![D_130, E_133, A_132, B_131, C_134]: (r1_tarski(k1_tarski(A_132), k3_enumset1(A_132, B_131, C_134, D_130, E_133)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_340])).
% 2.20/1.27  tff(c_354, plain, (![A_139, B_140, C_141, D_142]: (r1_tarski(k1_tarski(A_139), k2_enumset1(A_139, B_140, C_141, D_142)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_349])).
% 2.20/1.27  tff(c_358, plain, (![A_143, B_144, C_145]: (r1_tarski(k1_tarski(A_143), k1_enumset1(A_143, B_144, C_145)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_354])).
% 2.20/1.27  tff(c_362, plain, (![A_146, B_147]: (r1_tarski(k1_tarski(A_146), k2_tarski(A_146, B_147)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_358])).
% 2.20/1.27  tff(c_368, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_362])).
% 2.20/1.27  tff(c_28, plain, (![B_48, A_47]: (B_48=A_47 | ~r1_tarski(k1_tarski(A_47), k1_tarski(B_48)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.20/1.27  tff(c_372, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_368, c_28])).
% 2.20/1.27  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_372])).
% 2.20/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.27  
% 2.20/1.27  Inference rules
% 2.20/1.27  ----------------------
% 2.20/1.27  #Ref     : 0
% 2.20/1.27  #Sup     : 83
% 2.20/1.27  #Fact    : 0
% 2.20/1.27  #Define  : 0
% 2.20/1.27  #Split   : 0
% 2.20/1.27  #Chain   : 0
% 2.20/1.27  #Close   : 0
% 2.20/1.27  
% 2.20/1.27  Ordering : KBO
% 2.20/1.27  
% 2.20/1.27  Simplification rules
% 2.20/1.27  ----------------------
% 2.20/1.27  #Subsume      : 0
% 2.20/1.27  #Demod        : 17
% 2.20/1.27  #Tautology    : 52
% 2.20/1.27  #SimpNegUnit  : 1
% 2.20/1.27  #BackRed      : 0
% 2.20/1.27  
% 2.20/1.27  #Partial instantiations: 0
% 2.20/1.27  #Strategies tried      : 1
% 2.20/1.27  
% 2.20/1.27  Timing (in seconds)
% 2.20/1.27  ----------------------
% 2.20/1.27  Preprocessing        : 0.31
% 2.20/1.27  Parsing              : 0.16
% 2.20/1.27  CNF conversion       : 0.02
% 2.20/1.27  Main loop            : 0.22
% 2.20/1.27  Inferencing          : 0.10
% 2.20/1.27  Reduction            : 0.07
% 2.20/1.27  Demodulation         : 0.06
% 2.20/1.27  BG Simplification    : 0.02
% 2.20/1.27  Subsumption          : 0.03
% 2.20/1.27  Abstraction          : 0.02
% 2.20/1.27  MUC search           : 0.00
% 2.20/1.27  Cooper               : 0.00
% 2.20/1.27  Total                : 0.56
% 2.20/1.27  Index Insertion      : 0.00
% 2.20/1.27  Index Deletion       : 0.00
% 2.20/1.27  Index Matching       : 0.00
% 2.20/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

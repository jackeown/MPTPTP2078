%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:56 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   63 (  63 expanded)
%              Number of leaves         :   36 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  54 expanded)
%              Number of equality atoms :   44 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(c_237,plain,(
    ! [C_89,B_90,A_91] : k1_enumset1(C_89,B_90,A_91) = k1_enumset1(A_91,B_90,C_89) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_253,plain,(
    ! [C_89,B_90] : k1_enumset1(C_89,B_90,B_90) = k2_tarski(B_90,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_22])).

tff(c_24,plain,(
    ! [A_22,B_23,C_24] : k2_enumset1(A_22,A_22,B_23,C_24) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_25,B_26,C_27,D_28] : k3_enumset1(A_25,A_25,B_26,C_27,D_28) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [E_33,A_29,D_32,C_31,B_30] : k4_enumset1(A_29,A_29,B_30,C_31,D_32,E_33) = k3_enumset1(A_29,B_30,C_31,D_32,E_33) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_508,plain,(
    ! [C_126,D_122,F_121,E_124,A_125,B_123] : k2_xboole_0(k1_tarski(A_125),k3_enumset1(B_123,C_126,D_122,E_124,F_121)) = k4_enumset1(A_125,B_123,C_126,D_122,E_124,F_121) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    ! [A_52,B_53] : k2_xboole_0(k1_tarski(A_52),B_53) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_528,plain,(
    ! [D_127,C_128,E_130,B_131,F_132,A_129] : k4_enumset1(A_129,B_131,C_128,D_127,E_130,F_132) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_46])).

tff(c_531,plain,(
    ! [C_137,D_133,E_136,B_134,A_135] : k3_enumset1(A_135,B_134,C_137,D_133,E_136) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_528])).

tff(c_534,plain,(
    ! [A_138,B_139,C_140,D_141] : k2_enumset1(A_138,B_139,C_140,D_141) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_531])).

tff(c_537,plain,(
    ! [A_142,B_143,C_144] : k1_enumset1(A_142,B_143,C_144) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_534])).

tff(c_539,plain,(
    ! [B_90,C_89] : k2_tarski(B_90,C_89) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_537])).

tff(c_14,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_75,plain,(
    ! [A_62,B_63] : k3_xboole_0(A_62,k2_xboole_0(A_62,B_63)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k2_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_75])).

tff(c_171,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_183,plain,(
    k5_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_2')) = k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_171])).

tff(c_190,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_183])).

tff(c_42,plain,(
    ! [B_48,C_49] : r1_tarski(k1_xboole_0,k2_tarski(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_221,plain,(
    ! [A_87,B_88] :
      ( r2_xboole_0(A_87,B_88)
      | B_88 = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k4_xboole_0(B_6,A_5) != k1_xboole_0
      | ~ r2_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_333,plain,(
    ! [B_97,A_98] :
      ( k4_xboole_0(B_97,A_98) != k1_xboole_0
      | B_97 = A_98
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(resolution,[status(thm)],[c_221,c_10])).

tff(c_370,plain,(
    ! [B_104,C_105] :
      ( k4_xboole_0(k2_tarski(B_104,C_105),k1_xboole_0) != k1_xboole_0
      | k2_tarski(B_104,C_105) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_333])).

tff(c_377,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_370])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_539,c_377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  
% 2.59/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  %$ r2_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.59/1.35  
% 2.59/1.35  %Foreground sorts:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Background operators:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Foreground operators:
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.59/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.59/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.59/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.59/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.59/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.35  
% 2.67/1.36  tff(f_45, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 2.67/1.36  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.67/1.36  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.67/1.36  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.67/1.36  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.67/1.36  tff(f_47, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.67/1.36  tff(f_81, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.67/1.36  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.67/1.36  tff(f_85, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.67/1.36  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.67/1.36  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.67/1.36  tff(f_76, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.67/1.36  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.67/1.36  tff(f_39, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 2.67/1.36  tff(c_237, plain, (![C_89, B_90, A_91]: (k1_enumset1(C_89, B_90, A_91)=k1_enumset1(A_91, B_90, C_89))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.36  tff(c_22, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.36  tff(c_253, plain, (![C_89, B_90]: (k1_enumset1(C_89, B_90, B_90)=k2_tarski(B_90, C_89))), inference(superposition, [status(thm), theory('equality')], [c_237, c_22])).
% 2.67/1.36  tff(c_24, plain, (![A_22, B_23, C_24]: (k2_enumset1(A_22, A_22, B_23, C_24)=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.67/1.36  tff(c_26, plain, (![A_25, B_26, C_27, D_28]: (k3_enumset1(A_25, A_25, B_26, C_27, D_28)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.36  tff(c_28, plain, (![E_33, A_29, D_32, C_31, B_30]: (k4_enumset1(A_29, A_29, B_30, C_31, D_32, E_33)=k3_enumset1(A_29, B_30, C_31, D_32, E_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.36  tff(c_508, plain, (![C_126, D_122, F_121, E_124, A_125, B_123]: (k2_xboole_0(k1_tarski(A_125), k3_enumset1(B_123, C_126, D_122, E_124, F_121))=k4_enumset1(A_125, B_123, C_126, D_122, E_124, F_121))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.36  tff(c_46, plain, (![A_52, B_53]: (k2_xboole_0(k1_tarski(A_52), B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.36  tff(c_528, plain, (![D_127, C_128, E_130, B_131, F_132, A_129]: (k4_enumset1(A_129, B_131, C_128, D_127, E_130, F_132)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_508, c_46])).
% 2.67/1.36  tff(c_531, plain, (![C_137, D_133, E_136, B_134, A_135]: (k3_enumset1(A_135, B_134, C_137, D_133, E_136)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_528])).
% 2.67/1.36  tff(c_534, plain, (![A_138, B_139, C_140, D_141]: (k2_enumset1(A_138, B_139, C_140, D_141)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_531])).
% 2.67/1.36  tff(c_537, plain, (![A_142, B_143, C_144]: (k1_enumset1(A_142, B_143, C_144)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_534])).
% 2.67/1.36  tff(c_539, plain, (![B_90, C_89]: (k2_tarski(B_90, C_89)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_253, c_537])).
% 2.67/1.36  tff(c_14, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.67/1.36  tff(c_48, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.67/1.36  tff(c_75, plain, (![A_62, B_63]: (k3_xboole_0(A_62, k2_xboole_0(A_62, B_63))=A_62)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.36  tff(c_84, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k2_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_48, c_75])).
% 2.67/1.36  tff(c_171, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.67/1.36  tff(c_183, plain, (k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_2'))=k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_84, c_171])).
% 2.67/1.36  tff(c_190, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_183])).
% 2.67/1.36  tff(c_42, plain, (![B_48, C_49]: (r1_tarski(k1_xboole_0, k2_tarski(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.67/1.36  tff(c_221, plain, (![A_87, B_88]: (r2_xboole_0(A_87, B_88) | B_88=A_87 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.67/1.36  tff(c_10, plain, (![B_6, A_5]: (k4_xboole_0(B_6, A_5)!=k1_xboole_0 | ~r2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.67/1.36  tff(c_333, plain, (![B_97, A_98]: (k4_xboole_0(B_97, A_98)!=k1_xboole_0 | B_97=A_98 | ~r1_tarski(A_98, B_97))), inference(resolution, [status(thm)], [c_221, c_10])).
% 2.67/1.36  tff(c_370, plain, (![B_104, C_105]: (k4_xboole_0(k2_tarski(B_104, C_105), k1_xboole_0)!=k1_xboole_0 | k2_tarski(B_104, C_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_333])).
% 2.67/1.36  tff(c_377, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_190, c_370])).
% 2.67/1.36  tff(c_548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_539, c_377])).
% 2.67/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  Inference rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Ref     : 0
% 2.67/1.36  #Sup     : 130
% 2.67/1.36  #Fact    : 0
% 2.67/1.36  #Define  : 0
% 2.67/1.36  #Split   : 2
% 2.67/1.36  #Chain   : 0
% 2.67/1.36  #Close   : 0
% 2.67/1.36  
% 2.67/1.36  Ordering : KBO
% 2.67/1.36  
% 2.67/1.36  Simplification rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Subsume      : 5
% 2.67/1.36  #Demod        : 42
% 2.67/1.36  #Tautology    : 92
% 2.67/1.36  #SimpNegUnit  : 2
% 2.67/1.36  #BackRed      : 5
% 2.67/1.36  
% 2.67/1.36  #Partial instantiations: 0
% 2.67/1.36  #Strategies tried      : 1
% 2.67/1.36  
% 2.67/1.36  Timing (in seconds)
% 2.67/1.36  ----------------------
% 2.67/1.37  Preprocessing        : 0.33
% 2.67/1.37  Parsing              : 0.17
% 2.67/1.37  CNF conversion       : 0.02
% 2.67/1.37  Main loop            : 0.27
% 2.67/1.37  Inferencing          : 0.11
% 2.67/1.37  Reduction            : 0.09
% 2.67/1.37  Demodulation         : 0.07
% 2.67/1.37  BG Simplification    : 0.02
% 2.67/1.37  Subsumption          : 0.04
% 2.67/1.37  Abstraction          : 0.02
% 2.67/1.37  MUC search           : 0.00
% 2.67/1.37  Cooper               : 0.00
% 2.67/1.37  Total                : 0.63
% 2.67/1.37  Index Insertion      : 0.00
% 2.67/1.37  Index Deletion       : 0.00
% 2.67/1.37  Index Matching       : 0.00
% 2.67/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

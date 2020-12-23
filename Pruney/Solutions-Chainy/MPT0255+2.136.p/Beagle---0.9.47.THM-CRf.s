%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:56 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 186 expanded)
%              Number of leaves         :   30 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 274 expanded)
%              Number of equality atoms :   62 ( 198 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_66,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k6_enumset1(A,A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k2_xboole_0(A_47,B_48)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_32,plain,(
    ! [B_32,C_33] : r1_tarski(k1_xboole_0,k2_tarski(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    ! [A_57,B_58] :
      ( r2_xboole_0(A_57,B_58)
      | B_58 = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k4_xboole_0(B_4,A_3) != k1_xboole_0
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [B_64,A_65] :
      ( k4_xboole_0(B_64,A_65) != k1_xboole_0
      | B_64 = A_65
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(resolution,[status(thm)],[c_74,c_8])).

tff(c_134,plain,(
    ! [B_66,C_67] :
      ( k4_xboole_0(k2_tarski(B_66,C_67),k1_xboole_0) != k1_xboole_0
      | k2_tarski(B_66,C_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_116])).

tff(c_138,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_134])).

tff(c_139,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_55])).

tff(c_226,plain,(
    ! [D_81,C_78,F_80,A_77,B_82,E_79] : k6_enumset1(A_77,A_77,A_77,B_82,C_78,D_81,E_79,F_80) = k4_enumset1(A_77,B_82,C_78,D_81,E_79,F_80) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_29,B_30] : k6_enumset1(A_29,A_29,A_29,A_29,A_29,A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_242,plain,(
    ! [E_83,F_84] : k4_enumset1(E_83,E_83,E_83,E_83,E_83,F_84) = k2_tarski(E_83,F_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_22])).

tff(c_14,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,E_19) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_258,plain,(
    ! [E_85,F_86] : k3_enumset1(E_85,E_85,E_85,E_85,F_86) = k2_tarski(E_85,F_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_14])).

tff(c_20,plain,(
    ! [A_28] : k3_enumset1(A_28,A_28,A_28,A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_265,plain,(
    ! [F_86] : k2_tarski(F_86,F_86) = k1_tarski(F_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_20])).

tff(c_233,plain,(
    ! [E_79,F_80] : k4_enumset1(E_79,E_79,E_79,E_79,E_79,F_80) = k2_tarski(E_79,F_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_22])).

tff(c_18,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k6_enumset1(A_22,A_22,A_22,B_23,C_24,D_25,E_26,F_27) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_20,B_21] : k2_enumset1(A_20,A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_357,plain,(
    ! [A_96,G_97,H_100,E_99,C_95,B_94,F_98,D_93] : k2_xboole_0(k2_enumset1(A_96,B_94,C_95,D_93),k2_enumset1(E_99,F_98,G_97,H_100)) = k6_enumset1(A_96,B_94,C_95,D_93,E_99,F_98,G_97,H_100) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_369,plain,(
    ! [G_97,H_100,E_99,A_20,B_21,F_98] : k6_enumset1(A_20,A_20,A_20,B_21,E_99,F_98,G_97,H_100) = k2_xboole_0(k2_tarski(A_20,B_21),k2_enumset1(E_99,F_98,G_97,H_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_357])).

tff(c_450,plain,(
    ! [E_108,B_111,A_113,G_109,F_110,H_112] : k2_xboole_0(k2_tarski(A_113,B_111),k2_enumset1(E_108,F_110,G_109,H_112)) = k4_enumset1(A_113,B_111,E_108,F_110,G_109,H_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_369])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_472,plain,(
    ! [B_118,A_117,G_115,F_119,E_114,H_116] : k4_xboole_0(k2_tarski(A_117,B_118),k4_enumset1(A_117,B_118,E_114,F_119,G_115,H_116)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_10])).

tff(c_482,plain,(
    ! [E_79,F_80] : k4_xboole_0(k2_tarski(E_79,E_79),k2_tarski(E_79,F_80)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_472])).

tff(c_494,plain,(
    ! [E_120,F_121] : k4_xboole_0(k1_tarski(E_120),k2_tarski(E_120,F_121)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_482])).

tff(c_504,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_494])).

tff(c_274,plain,(
    ! [F_87] : k2_tarski(F_87,F_87) = k1_tarski(F_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_20])).

tff(c_133,plain,(
    ! [B_32,C_33] :
      ( k4_xboole_0(k2_tarski(B_32,C_33),k1_xboole_0) != k1_xboole_0
      | k2_tarski(B_32,C_33) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_116])).

tff(c_286,plain,(
    ! [F_87] :
      ( k4_xboole_0(k1_tarski(F_87),k1_xboole_0) != k1_xboole_0
      | k2_tarski(F_87,F_87) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_133])).

tff(c_310,plain,(
    ! [F_87] :
      ( k4_xboole_0(k1_tarski(F_87),k1_xboole_0) != k1_xboole_0
      | k1_tarski(F_87) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_286])).

tff(c_513,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_310])).

tff(c_30,plain,(
    ! [B_32,C_33] : r1_tarski(k1_tarski(B_32),k2_tarski(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_159,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_30])).

tff(c_85,plain,(
    ! [B_58,A_57] :
      ( k4_xboole_0(B_58,A_57) != k1_xboole_0
      | B_58 = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_74,c_8])).

tff(c_188,plain,
    ( k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_xboole_0
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_159,c_85])).

tff(c_215,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_524,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_215])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_524])).

tff(c_530,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_36,plain,(
    ! [A_36,B_37] : k2_xboole_0(k1_tarski(A_36),B_37) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_542,plain,(
    ! [B_37] : k2_xboole_0(k1_xboole_0,B_37) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_36])).

tff(c_140,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_38])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_542,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 16:09:12 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  %$ r2_xboole_0 > r1_tarski > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.21/1.29  
% 2.21/1.29  %Foreground sorts:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Background operators:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Foreground operators:
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.29  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.21/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.29  
% 2.57/1.31  tff(f_75, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.57/1.31  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.57/1.31  tff(f_66, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.57/1.31  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.57/1.31  tff(f_37, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 2.57/1.31  tff(f_47, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 2.57/1.31  tff(f_51, axiom, (![A, B]: (k6_enumset1(A, A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_enumset1)).
% 2.57/1.31  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.57/1.31  tff(f_49, axiom, (![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 2.57/1.31  tff(f_45, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 2.57/1.31  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_enumset1)).
% 2.57/1.31  tff(f_71, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.57/1.31  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.31  tff(c_48, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k2_xboole_0(A_47, B_48))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.31  tff(c_55, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_48])).
% 2.57/1.31  tff(c_32, plain, (![B_32, C_33]: (r1_tarski(k1_xboole_0, k2_tarski(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.57/1.31  tff(c_74, plain, (![A_57, B_58]: (r2_xboole_0(A_57, B_58) | B_58=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.31  tff(c_8, plain, (![B_4, A_3]: (k4_xboole_0(B_4, A_3)!=k1_xboole_0 | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.31  tff(c_116, plain, (![B_64, A_65]: (k4_xboole_0(B_64, A_65)!=k1_xboole_0 | B_64=A_65 | ~r1_tarski(A_65, B_64))), inference(resolution, [status(thm)], [c_74, c_8])).
% 2.57/1.31  tff(c_134, plain, (![B_66, C_67]: (k4_xboole_0(k2_tarski(B_66, C_67), k1_xboole_0)!=k1_xboole_0 | k2_tarski(B_66, C_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_116])).
% 2.57/1.31  tff(c_138, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_55, c_134])).
% 2.57/1.31  tff(c_139, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_138, c_55])).
% 2.57/1.31  tff(c_226, plain, (![D_81, C_78, F_80, A_77, B_82, E_79]: (k6_enumset1(A_77, A_77, A_77, B_82, C_78, D_81, E_79, F_80)=k4_enumset1(A_77, B_82, C_78, D_81, E_79, F_80))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.57/1.31  tff(c_22, plain, (![A_29, B_30]: (k6_enumset1(A_29, A_29, A_29, A_29, A_29, A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.31  tff(c_242, plain, (![E_83, F_84]: (k4_enumset1(E_83, E_83, E_83, E_83, E_83, F_84)=k2_tarski(E_83, F_84))), inference(superposition, [status(thm), theory('equality')], [c_226, c_22])).
% 2.57/1.31  tff(c_14, plain, (![B_16, A_15, D_18, E_19, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, E_19)=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.31  tff(c_258, plain, (![E_85, F_86]: (k3_enumset1(E_85, E_85, E_85, E_85, F_86)=k2_tarski(E_85, F_86))), inference(superposition, [status(thm), theory('equality')], [c_242, c_14])).
% 2.57/1.31  tff(c_20, plain, (![A_28]: (k3_enumset1(A_28, A_28, A_28, A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.31  tff(c_265, plain, (![F_86]: (k2_tarski(F_86, F_86)=k1_tarski(F_86))), inference(superposition, [status(thm), theory('equality')], [c_258, c_20])).
% 2.57/1.31  tff(c_233, plain, (![E_79, F_80]: (k4_enumset1(E_79, E_79, E_79, E_79, E_79, F_80)=k2_tarski(E_79, F_80))), inference(superposition, [status(thm), theory('equality')], [c_226, c_22])).
% 2.57/1.31  tff(c_18, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k6_enumset1(A_22, A_22, A_22, B_23, C_24, D_25, E_26, F_27)=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.57/1.31  tff(c_16, plain, (![A_20, B_21]: (k2_enumset1(A_20, A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.31  tff(c_357, plain, (![A_96, G_97, H_100, E_99, C_95, B_94, F_98, D_93]: (k2_xboole_0(k2_enumset1(A_96, B_94, C_95, D_93), k2_enumset1(E_99, F_98, G_97, H_100))=k6_enumset1(A_96, B_94, C_95, D_93, E_99, F_98, G_97, H_100))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.57/1.31  tff(c_369, plain, (![G_97, H_100, E_99, A_20, B_21, F_98]: (k6_enumset1(A_20, A_20, A_20, B_21, E_99, F_98, G_97, H_100)=k2_xboole_0(k2_tarski(A_20, B_21), k2_enumset1(E_99, F_98, G_97, H_100)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_357])).
% 2.57/1.31  tff(c_450, plain, (![E_108, B_111, A_113, G_109, F_110, H_112]: (k2_xboole_0(k2_tarski(A_113, B_111), k2_enumset1(E_108, F_110, G_109, H_112))=k4_enumset1(A_113, B_111, E_108, F_110, G_109, H_112))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_369])).
% 2.57/1.31  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.31  tff(c_472, plain, (![B_118, A_117, G_115, F_119, E_114, H_116]: (k4_xboole_0(k2_tarski(A_117, B_118), k4_enumset1(A_117, B_118, E_114, F_119, G_115, H_116))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_450, c_10])).
% 2.57/1.31  tff(c_482, plain, (![E_79, F_80]: (k4_xboole_0(k2_tarski(E_79, E_79), k2_tarski(E_79, F_80))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_233, c_472])).
% 2.57/1.31  tff(c_494, plain, (![E_120, F_121]: (k4_xboole_0(k1_tarski(E_120), k2_tarski(E_120, F_121))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_265, c_482])).
% 2.57/1.31  tff(c_504, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_138, c_494])).
% 2.57/1.31  tff(c_274, plain, (![F_87]: (k2_tarski(F_87, F_87)=k1_tarski(F_87))), inference(superposition, [status(thm), theory('equality')], [c_258, c_20])).
% 2.57/1.31  tff(c_133, plain, (![B_32, C_33]: (k4_xboole_0(k2_tarski(B_32, C_33), k1_xboole_0)!=k1_xboole_0 | k2_tarski(B_32, C_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_116])).
% 2.57/1.31  tff(c_286, plain, (![F_87]: (k4_xboole_0(k1_tarski(F_87), k1_xboole_0)!=k1_xboole_0 | k2_tarski(F_87, F_87)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_274, c_133])).
% 2.57/1.31  tff(c_310, plain, (![F_87]: (k4_xboole_0(k1_tarski(F_87), k1_xboole_0)!=k1_xboole_0 | k1_tarski(F_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_265, c_286])).
% 2.57/1.31  tff(c_513, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_504, c_310])).
% 2.57/1.31  tff(c_30, plain, (![B_32, C_33]: (r1_tarski(k1_tarski(B_32), k2_tarski(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.57/1.31  tff(c_159, plain, (r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_138, c_30])).
% 2.57/1.31  tff(c_85, plain, (![B_58, A_57]: (k4_xboole_0(B_58, A_57)!=k1_xboole_0 | B_58=A_57 | ~r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_74, c_8])).
% 2.57/1.31  tff(c_188, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_xboole_0 | k1_tarski('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_159, c_85])).
% 2.57/1.31  tff(c_215, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_188])).
% 2.57/1.31  tff(c_524, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_513, c_215])).
% 2.57/1.31  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_524])).
% 2.57/1.31  tff(c_530, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_188])).
% 2.57/1.31  tff(c_36, plain, (![A_36, B_37]: (k2_xboole_0(k1_tarski(A_36), B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.57/1.31  tff(c_542, plain, (![B_37]: (k2_xboole_0(k1_xboole_0, B_37)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_530, c_36])).
% 2.57/1.31  tff(c_140, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_138, c_38])).
% 2.57/1.31  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_542, c_140])).
% 2.57/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.31  
% 2.57/1.31  Inference rules
% 2.57/1.31  ----------------------
% 2.57/1.31  #Ref     : 0
% 2.57/1.31  #Sup     : 127
% 2.57/1.31  #Fact    : 0
% 2.57/1.31  #Define  : 0
% 2.57/1.31  #Split   : 2
% 2.57/1.31  #Chain   : 0
% 2.57/1.31  #Close   : 0
% 2.57/1.31  
% 2.57/1.31  Ordering : KBO
% 2.57/1.31  
% 2.57/1.31  Simplification rules
% 2.57/1.31  ----------------------
% 2.57/1.31  #Subsume      : 3
% 2.57/1.31  #Demod        : 37
% 2.57/1.31  #Tautology    : 85
% 2.57/1.31  #SimpNegUnit  : 1
% 2.57/1.31  #BackRed      : 8
% 2.57/1.31  
% 2.57/1.31  #Partial instantiations: 0
% 2.57/1.31  #Strategies tried      : 1
% 2.57/1.31  
% 2.57/1.31  Timing (in seconds)
% 2.57/1.31  ----------------------
% 2.57/1.31  Preprocessing        : 0.30
% 2.57/1.31  Parsing              : 0.16
% 2.57/1.31  CNF conversion       : 0.02
% 2.57/1.31  Main loop            : 0.26
% 2.57/1.31  Inferencing          : 0.10
% 2.57/1.31  Reduction            : 0.08
% 2.57/1.31  Demodulation         : 0.06
% 2.57/1.31  BG Simplification    : 0.02
% 2.57/1.31  Subsumption          : 0.04
% 2.57/1.31  Abstraction          : 0.02
% 2.57/1.31  MUC search           : 0.00
% 2.57/1.31  Cooper               : 0.00
% 2.57/1.31  Total                : 0.60
% 2.57/1.31  Index Insertion      : 0.00
% 2.57/1.31  Index Deletion       : 0.00
% 2.57/1.31  Index Matching       : 0.00
% 2.57/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

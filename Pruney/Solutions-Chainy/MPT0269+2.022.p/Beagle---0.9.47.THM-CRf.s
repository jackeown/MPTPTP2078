%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:46 EST 2020

% Result     : Theorem 8.71s
% Output     : CNFRefutation 8.71s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 109 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   61 ( 116 expanded)
%              Number of equality atoms :   53 ( 108 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(A_12,B_13),k2_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_389,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1657,plain,(
    ! [A_134,B_135] : k5_xboole_0(A_134,k5_xboole_0(B_135,k2_xboole_0(A_134,B_135))) = k3_xboole_0(A_134,B_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_389])).

tff(c_96,plain,(
    ! [B_58,A_59] : k5_xboole_0(B_58,A_59) = k5_xboole_0(A_59,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_59] : k5_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_6])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_466,plain,(
    ! [A_11,C_83] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_389])).

tff(c_479,plain,(
    ! [A_11,C_83] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_83)) = C_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_466])).

tff(c_1672,plain,(
    ! [B_135,A_134] : k5_xboole_0(B_135,k2_xboole_0(A_134,B_135)) = k5_xboole_0(A_134,k3_xboole_0(A_134,B_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_479])).

tff(c_1743,plain,(
    ! [B_136,A_137] : k5_xboole_0(B_136,k2_xboole_0(A_137,B_136)) = k4_xboole_0(A_137,B_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1672])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_480,plain,(
    ! [A_84,C_85] : k5_xboole_0(A_84,k5_xboole_0(A_84,C_85)) = C_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_466])).

tff(c_529,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_480])).

tff(c_1884,plain,(
    ! [A_139,B_140] : k5_xboole_0(k2_xboole_0(A_139,B_140),k4_xboole_0(A_139,B_140)) = B_140 ),
    inference(superposition,[status(thm),theory(equality)],[c_1743,c_529])).

tff(c_1920,plain,(
    k5_xboole_0(k2_xboole_0('#skF_1',k1_tarski('#skF_2')),k1_xboole_0) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1884])).

tff(c_551,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k5_xboole_0(B_87,A_86)) = B_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_480])).

tff(c_587,plain,(
    ! [A_11,C_83] : k5_xboole_0(k5_xboole_0(A_11,C_83),C_83) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_551])).

tff(c_1929,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1920,c_587])).

tff(c_1965,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1929])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1983,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1965,c_8])).

tff(c_16,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1263,plain,(
    ! [B_115,C_116,A_117] :
      ( k2_tarski(B_115,C_116) = A_117
      | k1_tarski(C_116) = A_117
      | k1_tarski(B_115) = A_117
      | k1_xboole_0 = A_117
      | ~ r1_tarski(A_117,k2_tarski(B_115,C_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1278,plain,(
    ! [A_14,A_117] :
      ( k2_tarski(A_14,A_14) = A_117
      | k1_tarski(A_14) = A_117
      | k1_tarski(A_14) = A_117
      | k1_xboole_0 = A_117
      | ~ r1_tarski(A_117,k1_tarski(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1263])).

tff(c_12383,plain,(
    ! [A_218,A_219] :
      ( k1_tarski(A_218) = A_219
      | k1_tarski(A_218) = A_219
      | k1_tarski(A_218) = A_219
      | k1_xboole_0 = A_219
      | ~ r1_tarski(A_219,k1_tarski(A_218)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1278])).

tff(c_12386,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1983,c_12383])).

tff(c_12396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_42,c_42,c_12386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.71/3.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.30  
% 8.71/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.31  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.71/3.31  
% 8.71/3.31  %Foreground sorts:
% 8.71/3.31  
% 8.71/3.31  
% 8.71/3.31  %Background operators:
% 8.71/3.31  
% 8.71/3.31  
% 8.71/3.31  %Foreground operators:
% 8.71/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.71/3.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.71/3.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.71/3.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.71/3.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.71/3.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.71/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.71/3.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.71/3.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.71/3.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.71/3.31  tff('#skF_2', type, '#skF_2': $i).
% 8.71/3.31  tff('#skF_1', type, '#skF_1': $i).
% 8.71/3.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.71/3.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.71/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.71/3.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.71/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.71/3.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.71/3.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.71/3.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.71/3.31  
% 8.71/3.32  tff(f_80, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 8.71/3.32  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.71/3.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.71/3.32  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.71/3.32  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.71/3.32  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.71/3.32  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.71/3.32  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.71/3.32  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.71/3.32  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 8.71/3.32  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.71/3.32  tff(c_42, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.71/3.32  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.71/3.32  tff(c_46, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.71/3.32  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.71/3.32  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k2_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.71/3.32  tff(c_389, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.71/3.32  tff(c_1657, plain, (![A_134, B_135]: (k5_xboole_0(A_134, k5_xboole_0(B_135, k2_xboole_0(A_134, B_135)))=k3_xboole_0(A_134, B_135))), inference(superposition, [status(thm), theory('equality')], [c_14, c_389])).
% 8.71/3.32  tff(c_96, plain, (![B_58, A_59]: (k5_xboole_0(B_58, A_59)=k5_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.71/3.32  tff(c_112, plain, (![A_59]: (k5_xboole_0(k1_xboole_0, A_59)=A_59)), inference(superposition, [status(thm), theory('equality')], [c_96, c_6])).
% 8.71/3.32  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.71/3.32  tff(c_466, plain, (![A_11, C_83]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_12, c_389])).
% 8.71/3.32  tff(c_479, plain, (![A_11, C_83]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_83))=C_83)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_466])).
% 8.71/3.32  tff(c_1672, plain, (![B_135, A_134]: (k5_xboole_0(B_135, k2_xboole_0(A_134, B_135))=k5_xboole_0(A_134, k3_xboole_0(A_134, B_135)))), inference(superposition, [status(thm), theory('equality')], [c_1657, c_479])).
% 8.71/3.32  tff(c_1743, plain, (![B_136, A_137]: (k5_xboole_0(B_136, k2_xboole_0(A_137, B_136))=k4_xboole_0(A_137, B_136))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1672])).
% 8.71/3.32  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.71/3.32  tff(c_480, plain, (![A_84, C_85]: (k5_xboole_0(A_84, k5_xboole_0(A_84, C_85))=C_85)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_466])).
% 8.71/3.32  tff(c_529, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_480])).
% 8.71/3.32  tff(c_1884, plain, (![A_139, B_140]: (k5_xboole_0(k2_xboole_0(A_139, B_140), k4_xboole_0(A_139, B_140))=B_140)), inference(superposition, [status(thm), theory('equality')], [c_1743, c_529])).
% 8.71/3.32  tff(c_1920, plain, (k5_xboole_0(k2_xboole_0('#skF_1', k1_tarski('#skF_2')), k1_xboole_0)=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46, c_1884])).
% 8.71/3.32  tff(c_551, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k5_xboole_0(B_87, A_86))=B_87)), inference(superposition, [status(thm), theory('equality')], [c_2, c_480])).
% 8.71/3.32  tff(c_587, plain, (![A_11, C_83]: (k5_xboole_0(k5_xboole_0(A_11, C_83), C_83)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_479, c_551])).
% 8.71/3.32  tff(c_1929, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1920, c_587])).
% 8.71/3.32  tff(c_1965, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1929])).
% 8.71/3.32  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.71/3.32  tff(c_1983, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1965, c_8])).
% 8.71/3.32  tff(c_16, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.71/3.32  tff(c_1263, plain, (![B_115, C_116, A_117]: (k2_tarski(B_115, C_116)=A_117 | k1_tarski(C_116)=A_117 | k1_tarski(B_115)=A_117 | k1_xboole_0=A_117 | ~r1_tarski(A_117, k2_tarski(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.71/3.32  tff(c_1278, plain, (![A_14, A_117]: (k2_tarski(A_14, A_14)=A_117 | k1_tarski(A_14)=A_117 | k1_tarski(A_14)=A_117 | k1_xboole_0=A_117 | ~r1_tarski(A_117, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1263])).
% 8.71/3.32  tff(c_12383, plain, (![A_218, A_219]: (k1_tarski(A_218)=A_219 | k1_tarski(A_218)=A_219 | k1_tarski(A_218)=A_219 | k1_xboole_0=A_219 | ~r1_tarski(A_219, k1_tarski(A_218)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1278])).
% 8.71/3.32  tff(c_12386, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1983, c_12383])).
% 8.71/3.32  tff(c_12396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_42, c_42, c_12386])).
% 8.71/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.32  
% 8.71/3.32  Inference rules
% 8.71/3.32  ----------------------
% 8.71/3.32  #Ref     : 0
% 8.71/3.32  #Sup     : 3192
% 8.71/3.32  #Fact    : 0
% 8.71/3.32  #Define  : 0
% 8.71/3.32  #Split   : 0
% 8.71/3.32  #Chain   : 0
% 8.71/3.32  #Close   : 0
% 8.71/3.32  
% 8.71/3.32  Ordering : KBO
% 8.71/3.32  
% 8.71/3.32  Simplification rules
% 8.71/3.32  ----------------------
% 8.71/3.32  #Subsume      : 158
% 8.71/3.32  #Demod        : 2871
% 8.71/3.32  #Tautology    : 1328
% 8.71/3.32  #SimpNegUnit  : 1
% 8.71/3.32  #BackRed      : 3
% 8.71/3.32  
% 8.71/3.32  #Partial instantiations: 0
% 8.71/3.32  #Strategies tried      : 1
% 8.71/3.32  
% 8.71/3.32  Timing (in seconds)
% 8.71/3.32  ----------------------
% 8.71/3.32  Preprocessing        : 0.31
% 8.71/3.32  Parsing              : 0.16
% 8.71/3.32  CNF conversion       : 0.02
% 8.71/3.32  Main loop            : 2.25
% 8.71/3.32  Inferencing          : 0.45
% 8.71/3.32  Reduction            : 1.39
% 8.71/3.32  Demodulation         : 1.25
% 8.71/3.32  BG Simplification    : 0.07
% 8.71/3.32  Subsumption          : 0.26
% 8.71/3.32  Abstraction          : 0.10
% 8.71/3.32  MUC search           : 0.00
% 8.71/3.32  Cooper               : 0.00
% 8.71/3.32  Total                : 2.59
% 8.71/3.32  Index Insertion      : 0.00
% 8.71/3.32  Index Deletion       : 0.00
% 8.71/3.32  Index Matching       : 0.00
% 8.71/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:50 EST 2020

% Result     : Theorem 5.76s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 101 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 ( 108 expanded)
%              Number of equality atoms :   55 ( 100 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k5_xboole_0(k5_xboole_0(A_8,B_9),C_10) = k5_xboole_0(A_8,k5_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_341,plain,(
    ! [A_81,B_82] : k5_xboole_0(k5_xboole_0(A_81,B_82),k2_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1331,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k5_xboole_0(B_127,k2_xboole_0(A_126,B_127))) = k3_xboole_0(A_126,B_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_341])).

tff(c_42,plain,(
    ! [A_47] : k3_tarski(k1_tarski(A_47)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_139,plain,(
    ! [A_14] : k3_tarski(k1_tarski(A_14)) = k2_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_130])).

tff(c_142,plain,(
    ! [A_14] : k2_xboole_0(A_14,A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_139])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_387,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_11,A_11)) = k3_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_341])).

tff(c_391,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2,c_387])).

tff(c_187,plain,(
    ! [A_75,B_76,C_77] : k5_xboole_0(k5_xboole_0(A_75,B_76),C_77) = k5_xboole_0(A_75,k5_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_228,plain,(
    ! [A_11,C_77] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_77)) = k5_xboole_0(k1_xboole_0,C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_187])).

tff(c_529,plain,(
    ! [A_11,C_77] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_77)) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_228])).

tff(c_1346,plain,(
    ! [B_127,A_126] : k5_xboole_0(B_127,k2_xboole_0(A_126,B_127)) = k5_xboole_0(A_126,k3_xboole_0(A_126,B_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_529])).

tff(c_1412,plain,(
    ! [B_128,A_129] : k5_xboole_0(B_128,k2_xboole_0(A_129,B_128)) = k4_xboole_0(A_129,B_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1346])).

tff(c_1636,plain,(
    ! [B_135,A_136] : k5_xboole_0(B_135,k4_xboole_0(A_136,B_135)) = k2_xboole_0(A_136,B_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_1412,c_529])).

tff(c_1696,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1636])).

tff(c_1706,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1696])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1716,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1706,c_8])).

tff(c_1173,plain,(
    ! [B_120,C_121,A_122] :
      ( k2_tarski(B_120,C_121) = A_122
      | k1_tarski(C_121) = A_122
      | k1_tarski(B_120) = A_122
      | k1_xboole_0 = A_122
      | ~ r1_tarski(A_122,k2_tarski(B_120,C_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1186,plain,(
    ! [A_14,A_122] :
      ( k2_tarski(A_14,A_14) = A_122
      | k1_tarski(A_14) = A_122
      | k1_tarski(A_14) = A_122
      | k1_xboole_0 = A_122
      | ~ r1_tarski(A_122,k1_tarski(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1173])).

tff(c_4392,plain,(
    ! [A_174,A_175] :
      ( k1_tarski(A_174) = A_175
      | k1_tarski(A_174) = A_175
      | k1_tarski(A_174) = A_175
      | k1_xboole_0 = A_175
      | ~ r1_tarski(A_175,k1_tarski(A_174)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1186])).

tff(c_4395,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1716,c_4392])).

tff(c_4406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_44,c_44,c_4395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n012.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 11:42:37 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.76/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.12  
% 5.76/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.13  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.76/2.13  
% 5.76/2.13  %Foreground sorts:
% 5.76/2.13  
% 5.76/2.13  
% 5.76/2.13  %Background operators:
% 5.76/2.13  
% 5.76/2.13  
% 5.76/2.13  %Foreground operators:
% 5.76/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.76/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.76/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.76/2.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.76/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.76/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.76/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.76/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.76/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.76/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.76/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.76/2.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.76/2.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.76/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.76/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.76/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.76/2.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.76/2.13  
% 5.76/2.15  tff(f_82, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 5.76/2.15  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.76/2.15  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.76/2.15  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.76/2.15  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.76/2.15  tff(f_72, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 5.76/2.15  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.76/2.15  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.76/2.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.76/2.15  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.76/2.15  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.76/2.15  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 5.76/2.15  tff(c_46, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.76/2.15  tff(c_44, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.76/2.15  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.76/2.15  tff(c_48, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.76/2.15  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.76/2.15  tff(c_10, plain, (![A_8, B_9, C_10]: (k5_xboole_0(k5_xboole_0(A_8, B_9), C_10)=k5_xboole_0(A_8, k5_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.76/2.15  tff(c_341, plain, (![A_81, B_82]: (k5_xboole_0(k5_xboole_0(A_81, B_82), k2_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.76/2.15  tff(c_1331, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k5_xboole_0(B_127, k2_xboole_0(A_126, B_127)))=k3_xboole_0(A_126, B_127))), inference(superposition, [status(thm), theory('equality')], [c_10, c_341])).
% 5.76/2.15  tff(c_42, plain, (![A_47]: (k3_tarski(k1_tarski(A_47))=A_47)), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.76/2.15  tff(c_16, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.76/2.15  tff(c_130, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.76/2.15  tff(c_139, plain, (![A_14]: (k3_tarski(k1_tarski(A_14))=k2_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_130])).
% 5.76/2.15  tff(c_142, plain, (![A_14]: (k2_xboole_0(A_14, A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_139])).
% 5.76/2.15  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.76/2.15  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.76/2.15  tff(c_387, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_11, A_11))=k3_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_341])).
% 5.76/2.15  tff(c_391, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_2, c_387])).
% 5.76/2.15  tff(c_187, plain, (![A_75, B_76, C_77]: (k5_xboole_0(k5_xboole_0(A_75, B_76), C_77)=k5_xboole_0(A_75, k5_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.76/2.15  tff(c_228, plain, (![A_11, C_77]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_77))=k5_xboole_0(k1_xboole_0, C_77))), inference(superposition, [status(thm), theory('equality')], [c_12, c_187])).
% 5.76/2.15  tff(c_529, plain, (![A_11, C_77]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_77))=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_391, c_228])).
% 5.76/2.15  tff(c_1346, plain, (![B_127, A_126]: (k5_xboole_0(B_127, k2_xboole_0(A_126, B_127))=k5_xboole_0(A_126, k3_xboole_0(A_126, B_127)))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_529])).
% 5.76/2.15  tff(c_1412, plain, (![B_128, A_129]: (k5_xboole_0(B_128, k2_xboole_0(A_129, B_128))=k4_xboole_0(A_129, B_128))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1346])).
% 5.76/2.15  tff(c_1636, plain, (![B_135, A_136]: (k5_xboole_0(B_135, k4_xboole_0(A_136, B_135))=k2_xboole_0(A_136, B_135))), inference(superposition, [status(thm), theory('equality')], [c_1412, c_529])).
% 5.76/2.15  tff(c_1696, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1636])).
% 5.76/2.15  tff(c_1706, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1696])).
% 5.76/2.15  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.76/2.15  tff(c_1716, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1706, c_8])).
% 5.76/2.15  tff(c_1173, plain, (![B_120, C_121, A_122]: (k2_tarski(B_120, C_121)=A_122 | k1_tarski(C_121)=A_122 | k1_tarski(B_120)=A_122 | k1_xboole_0=A_122 | ~r1_tarski(A_122, k2_tarski(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.76/2.15  tff(c_1186, plain, (![A_14, A_122]: (k2_tarski(A_14, A_14)=A_122 | k1_tarski(A_14)=A_122 | k1_tarski(A_14)=A_122 | k1_xboole_0=A_122 | ~r1_tarski(A_122, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1173])).
% 5.76/2.15  tff(c_4392, plain, (![A_174, A_175]: (k1_tarski(A_174)=A_175 | k1_tarski(A_174)=A_175 | k1_tarski(A_174)=A_175 | k1_xboole_0=A_175 | ~r1_tarski(A_175, k1_tarski(A_174)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1186])).
% 5.76/2.15  tff(c_4395, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1716, c_4392])).
% 5.76/2.15  tff(c_4406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_44, c_44, c_4395])).
% 5.76/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.15  
% 5.76/2.15  Inference rules
% 5.76/2.15  ----------------------
% 5.76/2.15  #Ref     : 0
% 5.76/2.15  #Sup     : 1079
% 5.76/2.15  #Fact    : 0
% 5.76/2.15  #Define  : 0
% 5.76/2.15  #Split   : 0
% 5.76/2.15  #Chain   : 0
% 5.76/2.15  #Close   : 0
% 5.76/2.15  
% 5.76/2.15  Ordering : KBO
% 5.76/2.15  
% 5.76/2.15  Simplification rules
% 5.76/2.15  ----------------------
% 5.76/2.15  #Subsume      : 3
% 5.76/2.15  #Demod        : 895
% 5.76/2.15  #Tautology    : 611
% 5.76/2.15  #SimpNegUnit  : 1
% 5.76/2.15  #BackRed      : 3
% 5.76/2.15  
% 5.76/2.15  #Partial instantiations: 0
% 5.76/2.15  #Strategies tried      : 1
% 5.76/2.15  
% 5.76/2.15  Timing (in seconds)
% 5.76/2.15  ----------------------
% 5.76/2.15  Preprocessing        : 0.35
% 5.76/2.15  Parsing              : 0.19
% 5.76/2.15  CNF conversion       : 0.02
% 5.76/2.15  Main loop            : 1.06
% 5.76/2.15  Inferencing          : 0.32
% 5.76/2.15  Reduction            : 0.50
% 5.76/2.15  Demodulation         : 0.43
% 5.76/2.15  BG Simplification    : 0.04
% 5.76/2.15  Subsumption          : 0.15
% 5.76/2.15  Abstraction          : 0.05
% 5.76/2.15  MUC search           : 0.00
% 5.76/2.16  Cooper               : 0.00
% 5.76/2.16  Total                : 1.44
% 5.76/2.16  Index Insertion      : 0.00
% 5.76/2.16  Index Deletion       : 0.00
% 5.76/2.16  Index Matching       : 0.00
% 5.76/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

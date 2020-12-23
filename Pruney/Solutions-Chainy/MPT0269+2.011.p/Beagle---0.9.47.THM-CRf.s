%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:45 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   57 (  78 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  71 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_238,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_255,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_238])).

tff(c_132,plain,(
    ! [B_59,A_60] : k5_xboole_0(B_59,A_60) = k5_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    ! [A_60] : k5_xboole_0(k1_xboole_0,A_60) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_14])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_397,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k5_xboole_0(A_78,B_79),C_80) = k5_xboole_0(A_78,k5_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_465,plain,(
    ! [A_18,C_80] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_80)) = k5_xboole_0(k1_xboole_0,C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_397])).

tff(c_486,plain,(
    ! [A_81,C_82] : k5_xboole_0(A_81,k5_xboole_0(A_81,C_82)) = C_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_465])).

tff(c_1258,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k4_xboole_0(A_122,B_123)) = k3_xboole_0(B_123,A_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_486])).

tff(c_1310,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k5_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1258])).

tff(c_1319,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1310])).

tff(c_483,plain,(
    ! [A_18,C_80] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_80)) = C_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_465])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_893,plain,(
    ! [A_94,B_95,C_96] : k5_xboole_0(k3_xboole_0(A_94,B_95),k3_xboole_0(C_96,B_95)) = k3_xboole_0(k5_xboole_0(A_94,C_96),B_95) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_957,plain,(
    ! [A_5,C_96] : k5_xboole_0(A_5,k3_xboole_0(C_96,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_96),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_893])).

tff(c_1185,plain,(
    ! [A_120,C_121] : k3_xboole_0(A_120,k5_xboole_0(A_120,C_121)) = k4_xboole_0(A_120,C_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_2,c_957])).

tff(c_1598,plain,(
    ! [A_128,C_129] : k4_xboole_0(A_128,k5_xboole_0(A_128,C_129)) = k3_xboole_0(A_128,C_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_1185])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1671,plain,(
    ! [A_130,C_131] : r1_tarski(k3_xboole_0(A_130,C_131),A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_1598,c_12])).

tff(c_1690,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_1671])).

tff(c_34,plain,(
    ! [B_48,A_47] :
      ( k1_tarski(B_48) = A_47
      | k1_xboole_0 = A_47
      | ~ r1_tarski(A_47,k1_tarski(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1720,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1690,c_34])).

tff(c_1724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_1720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:24:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.69  
% 3.40/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.69  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.40/1.69  
% 3.40/1.69  %Foreground sorts:
% 3.40/1.69  
% 3.40/1.69  
% 3.40/1.69  %Background operators:
% 3.40/1.69  
% 3.40/1.69  
% 3.40/1.69  %Foreground operators:
% 3.40/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.40/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.69  
% 3.70/1.70  tff(f_73, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.70/1.70  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.70/1.70  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.70/1.70  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.70/1.70  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.70/1.70  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.70/1.70  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.70/1.70  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.70/1.70  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 3.70/1.70  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.70/1.70  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.70/1.70  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.70/1.70  tff(c_40, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.70/1.70  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.70/1.70  tff(c_44, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.70/1.70  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.70/1.70  tff(c_238, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.70/1.70  tff(c_255, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_238])).
% 3.70/1.70  tff(c_132, plain, (![B_59, A_60]: (k5_xboole_0(B_59, A_60)=k5_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.70/1.70  tff(c_148, plain, (![A_60]: (k5_xboole_0(k1_xboole_0, A_60)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_132, c_14])).
% 3.70/1.70  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.70/1.70  tff(c_397, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k5_xboole_0(A_78, B_79), C_80)=k5_xboole_0(A_78, k5_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.70/1.70  tff(c_465, plain, (![A_18, C_80]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_80))=k5_xboole_0(k1_xboole_0, C_80))), inference(superposition, [status(thm), theory('equality')], [c_18, c_397])).
% 3.70/1.70  tff(c_486, plain, (![A_81, C_82]: (k5_xboole_0(A_81, k5_xboole_0(A_81, C_82))=C_82)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_465])).
% 3.70/1.70  tff(c_1258, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k4_xboole_0(A_122, B_123))=k3_xboole_0(B_123, A_122))), inference(superposition, [status(thm), theory('equality')], [c_255, c_486])).
% 3.70/1.70  tff(c_1310, plain, (k3_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k5_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_1258])).
% 3.70/1.70  tff(c_1319, plain, (k3_xboole_0(k1_tarski('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1310])).
% 3.70/1.70  tff(c_483, plain, (![A_18, C_80]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_80))=C_80)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_465])).
% 3.70/1.70  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.70  tff(c_893, plain, (![A_94, B_95, C_96]: (k5_xboole_0(k3_xboole_0(A_94, B_95), k3_xboole_0(C_96, B_95))=k3_xboole_0(k5_xboole_0(A_94, C_96), B_95))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.70/1.70  tff(c_957, plain, (![A_5, C_96]: (k5_xboole_0(A_5, k3_xboole_0(C_96, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_96), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_893])).
% 3.70/1.70  tff(c_1185, plain, (![A_120, C_121]: (k3_xboole_0(A_120, k5_xboole_0(A_120, C_121))=k4_xboole_0(A_120, C_121))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_2, c_957])).
% 3.70/1.70  tff(c_1598, plain, (![A_128, C_129]: (k4_xboole_0(A_128, k5_xboole_0(A_128, C_129))=k3_xboole_0(A_128, C_129))), inference(superposition, [status(thm), theory('equality')], [c_483, c_1185])).
% 3.70/1.70  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.70/1.70  tff(c_1671, plain, (![A_130, C_131]: (r1_tarski(k3_xboole_0(A_130, C_131), A_130))), inference(superposition, [status(thm), theory('equality')], [c_1598, c_12])).
% 3.70/1.70  tff(c_1690, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1319, c_1671])).
% 3.70/1.70  tff(c_34, plain, (![B_48, A_47]: (k1_tarski(B_48)=A_47 | k1_xboole_0=A_47 | ~r1_tarski(A_47, k1_tarski(B_48)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.70/1.70  tff(c_1720, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1690, c_34])).
% 3.70/1.70  tff(c_1724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_1720])).
% 3.70/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.70  
% 3.70/1.70  Inference rules
% 3.70/1.70  ----------------------
% 3.70/1.70  #Ref     : 0
% 3.70/1.70  #Sup     : 418
% 3.70/1.70  #Fact    : 0
% 3.70/1.70  #Define  : 0
% 3.70/1.70  #Split   : 0
% 3.70/1.70  #Chain   : 0
% 3.70/1.70  #Close   : 0
% 3.70/1.70  
% 3.70/1.70  Ordering : KBO
% 3.70/1.70  
% 3.70/1.70  Simplification rules
% 3.70/1.70  ----------------------
% 3.70/1.70  #Subsume      : 6
% 3.70/1.70  #Demod        : 249
% 3.70/1.70  #Tautology    : 280
% 3.70/1.70  #SimpNegUnit  : 1
% 3.70/1.70  #BackRed      : 4
% 3.70/1.70  
% 3.70/1.70  #Partial instantiations: 0
% 3.70/1.70  #Strategies tried      : 1
% 3.70/1.70  
% 3.70/1.70  Timing (in seconds)
% 3.70/1.70  ----------------------
% 3.70/1.70  Preprocessing        : 0.41
% 3.70/1.70  Parsing              : 0.21
% 3.70/1.70  CNF conversion       : 0.02
% 3.70/1.70  Main loop            : 0.46
% 3.70/1.70  Inferencing          : 0.16
% 3.70/1.70  Reduction            : 0.19
% 3.70/1.70  Demodulation         : 0.16
% 3.70/1.70  BG Simplification    : 0.03
% 3.70/1.70  Subsumption          : 0.06
% 3.70/1.70  Abstraction          : 0.03
% 3.70/1.70  MUC search           : 0.00
% 3.70/1.70  Cooper               : 0.00
% 3.70/1.70  Total                : 0.90
% 3.70/1.70  Index Insertion      : 0.00
% 3.70/1.70  Index Deletion       : 0.00
% 3.70/1.70  Index Matching       : 0.00
% 3.70/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:07 EST 2020

% Result     : Theorem 15.82s
% Output     : CNFRefutation 15.82s
% Verified   : 
% Statistics : Number of formulae       :   49 (  63 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  53 expanded)
%              Number of equality atoms :   33 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_50,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_140,plain,(
    ! [B_69,A_70] : k5_xboole_0(B_69,A_70) = k5_xboole_0(A_70,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_156,plain,(
    ! [A_70] : k5_xboole_0(k1_xboole_0,A_70) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_22])).

tff(c_26,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_541,plain,(
    ! [B_96,A_97] :
      ( k1_tarski(B_96) = A_97
      | k1_xboole_0 = A_97
      | ~ r1_tarski(A_97,k1_tarski(B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14609,plain,(
    ! [B_318,B_319] :
      ( k3_xboole_0(k1_tarski(B_318),B_319) = k1_tarski(B_318)
      | k3_xboole_0(k1_tarski(B_318),B_319) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_541])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14820,plain,(
    ! [B_318,B_319] :
      ( k5_xboole_0(k1_tarski(B_318),k1_tarski(B_318)) = k4_xboole_0(k1_tarski(B_318),B_319)
      | k3_xboole_0(k1_tarski(B_318),B_319) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14609,c_12])).

tff(c_57005,plain,(
    ! [B_567,B_568] :
      ( k4_xboole_0(k1_tarski(B_567),B_568) = k1_xboole_0
      | k3_xboole_0(k1_tarski(B_567),B_568) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14820])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_57507,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_57005,c_52])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_883,plain,(
    ! [A_112,B_113,C_114] : k5_xboole_0(k5_xboole_0(A_112,B_113),C_114) = k5_xboole_0(A_112,k5_xboole_0(B_113,C_114)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5101,plain,(
    ! [A_219,B_220,A_218] : k5_xboole_0(A_219,k5_xboole_0(B_220,A_218)) = k5_xboole_0(A_218,k5_xboole_0(A_219,B_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_883])).

tff(c_5573,plain,(
    ! [A_221,A_222] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_221,A_222)) = k5_xboole_0(A_222,A_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_5101])).

tff(c_5726,plain,(
    ! [A_9,B_10] : k5_xboole_0(k3_xboole_0(A_9,B_10),A_9) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5573])).

tff(c_5785,plain,(
    ! [A_9,B_10] : k5_xboole_0(k3_xboole_0(A_9,B_10),A_9) = k4_xboole_0(A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_5726])).

tff(c_57685,plain,(
    k5_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57507,c_5785])).

tff(c_57813,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_57685])).

tff(c_57815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_57813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:43:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.82/8.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.82/8.44  
% 15.82/8.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.82/8.44  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 15.82/8.44  
% 15.82/8.44  %Foreground sorts:
% 15.82/8.44  
% 15.82/8.44  
% 15.82/8.44  %Background operators:
% 15.82/8.44  
% 15.82/8.44  
% 15.82/8.44  %Foreground operators:
% 15.82/8.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.82/8.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.82/8.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.82/8.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.82/8.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.82/8.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.82/8.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.82/8.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.82/8.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.82/8.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.82/8.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.82/8.44  tff('#skF_2', type, '#skF_2': $i).
% 15.82/8.44  tff('#skF_1', type, '#skF_1': $i).
% 15.82/8.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.82/8.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.82/8.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.82/8.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.82/8.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.82/8.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.82/8.44  
% 15.82/8.45  tff(f_80, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 15.82/8.45  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 15.82/8.45  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 15.82/8.45  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 15.82/8.45  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.82/8.45  tff(f_75, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 15.82/8.45  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.82/8.45  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 15.82/8.45  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.82/8.45  tff(c_140, plain, (![B_69, A_70]: (k5_xboole_0(B_69, A_70)=k5_xboole_0(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.82/8.45  tff(c_22, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.82/8.45  tff(c_156, plain, (![A_70]: (k5_xboole_0(k1_xboole_0, A_70)=A_70)), inference(superposition, [status(thm), theory('equality')], [c_140, c_22])).
% 15.82/8.45  tff(c_26, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.82/8.45  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.82/8.45  tff(c_541, plain, (![B_96, A_97]: (k1_tarski(B_96)=A_97 | k1_xboole_0=A_97 | ~r1_tarski(A_97, k1_tarski(B_96)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.82/8.45  tff(c_14609, plain, (![B_318, B_319]: (k3_xboole_0(k1_tarski(B_318), B_319)=k1_tarski(B_318) | k3_xboole_0(k1_tarski(B_318), B_319)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_541])).
% 15.82/8.45  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.82/8.45  tff(c_14820, plain, (![B_318, B_319]: (k5_xboole_0(k1_tarski(B_318), k1_tarski(B_318))=k4_xboole_0(k1_tarski(B_318), B_319) | k3_xboole_0(k1_tarski(B_318), B_319)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14609, c_12])).
% 15.82/8.45  tff(c_57005, plain, (![B_567, B_568]: (k4_xboole_0(k1_tarski(B_567), B_568)=k1_xboole_0 | k3_xboole_0(k1_tarski(B_567), B_568)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14820])).
% 15.82/8.45  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.82/8.45  tff(c_57507, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_57005, c_52])).
% 15.82/8.45  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.82/8.45  tff(c_883, plain, (![A_112, B_113, C_114]: (k5_xboole_0(k5_xboole_0(A_112, B_113), C_114)=k5_xboole_0(A_112, k5_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.82/8.45  tff(c_5101, plain, (![A_219, B_220, A_218]: (k5_xboole_0(A_219, k5_xboole_0(B_220, A_218))=k5_xboole_0(A_218, k5_xboole_0(A_219, B_220)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_883])).
% 15.82/8.45  tff(c_5573, plain, (![A_221, A_222]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_221, A_222))=k5_xboole_0(A_222, A_221))), inference(superposition, [status(thm), theory('equality')], [c_156, c_5101])).
% 15.82/8.45  tff(c_5726, plain, (![A_9, B_10]: (k5_xboole_0(k3_xboole_0(A_9, B_10), A_9)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5573])).
% 15.82/8.45  tff(c_5785, plain, (![A_9, B_10]: (k5_xboole_0(k3_xboole_0(A_9, B_10), A_9)=k4_xboole_0(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_5726])).
% 15.82/8.45  tff(c_57685, plain, (k5_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57507, c_5785])).
% 15.82/8.45  tff(c_57813, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_57685])).
% 15.82/8.45  tff(c_57815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_57813])).
% 15.82/8.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.82/8.45  
% 15.82/8.45  Inference rules
% 15.82/8.45  ----------------------
% 15.82/8.45  #Ref     : 0
% 15.82/8.45  #Sup     : 14742
% 15.82/8.45  #Fact    : 1
% 15.82/8.45  #Define  : 0
% 15.82/8.45  #Split   : 0
% 15.82/8.45  #Chain   : 0
% 15.82/8.45  #Close   : 0
% 15.82/8.45  
% 15.82/8.45  Ordering : KBO
% 15.82/8.45  
% 15.82/8.45  Simplification rules
% 15.82/8.45  ----------------------
% 15.82/8.45  #Subsume      : 495
% 15.82/8.45  #Demod        : 18580
% 15.82/8.45  #Tautology    : 8984
% 15.82/8.45  #SimpNegUnit  : 2
% 15.82/8.45  #BackRed      : 11
% 15.82/8.45  
% 15.82/8.45  #Partial instantiations: 0
% 15.82/8.45  #Strategies tried      : 1
% 15.82/8.45  
% 15.82/8.45  Timing (in seconds)
% 15.82/8.45  ----------------------
% 15.82/8.45  Preprocessing        : 0.32
% 15.82/8.45  Parsing              : 0.17
% 15.82/8.45  CNF conversion       : 0.02
% 15.82/8.45  Main loop            : 7.39
% 15.82/8.45  Inferencing          : 0.95
% 15.82/8.45  Reduction            : 4.82
% 15.82/8.45  Demodulation         : 4.45
% 15.82/8.45  BG Simplification    : 0.13
% 15.82/8.46  Subsumption          : 1.13
% 15.82/8.46  Abstraction          : 0.22
% 15.82/8.46  MUC search           : 0.00
% 15.82/8.46  Cooper               : 0.00
% 15.82/8.46  Total                : 7.73
% 15.82/8.46  Index Insertion      : 0.00
% 15.82/8.46  Index Deletion       : 0.00
% 15.82/8.46  Index Matching       : 0.00
% 15.82/8.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

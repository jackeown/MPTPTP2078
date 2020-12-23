%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:07 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  90 expanded)
%              Number of equality atoms :   40 (  69 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(A_56,B_57)
      | k3_xboole_0(A_56,B_57) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_154,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = A_66
      | k3_xboole_0(A_66,B_67) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_111,c_12])).

tff(c_38,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_163,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_38])).

tff(c_173,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_163])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_213,plain,(
    ! [B_73,A_74] :
      ( k1_tarski(B_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_229,plain,(
    ! [B_73,B_8] :
      ( k3_xboole_0(k1_tarski(B_73),B_8) = k1_tarski(B_73)
      | k3_xboole_0(k1_tarski(B_73),B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_213])).

tff(c_293,plain,(
    ! [B_86,B_87] :
      ( k3_xboole_0(k1_tarski(B_86),B_87) = k1_xboole_0
      | k1_tarski(B_86) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_229])).

tff(c_447,plain,(
    ! [B_113,B_114] :
      ( k3_xboole_0(B_113,k1_tarski(B_114)) = k1_xboole_0
      | k1_tarski(B_114) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_293])).

tff(c_499,plain,(
    k1_tarski('#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_173])).

tff(c_16,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_256,plain,(
    ! [B_84,B_85] :
      ( k3_xboole_0(k1_tarski(B_84),B_85) = k1_tarski(B_84)
      | k3_xboole_0(k1_tarski(B_84),B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_213])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_265,plain,(
    ! [B_84,B_85] :
      ( k5_xboole_0(k1_tarski(B_84),k1_tarski(B_84)) = k4_xboole_0(k1_tarski(B_84),B_85)
      | k3_xboole_0(k1_tarski(B_84),B_85) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_8])).

tff(c_519,plain,(
    ! [B_124,B_125] :
      ( k4_xboole_0(k1_tarski(B_124),B_125) = k1_xboole_0
      | k3_xboole_0(k1_tarski(B_124),B_125) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_265])).

tff(c_40,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_545,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_40])).

tff(c_553,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_229])).

tff(c_586,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | k3_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_553])).

tff(c_588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_499,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.29  
% 2.29/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.30  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.29/1.30  
% 2.29/1.30  %Foreground sorts:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Background operators:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Foreground operators:
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.29/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.29/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.29/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.30  
% 2.29/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.29/1.31  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.29/1.31  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.29/1.31  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 2.29/1.31  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.29/1.31  tff(f_61, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.29/1.31  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.29/1.31  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.29/1.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.29/1.31  tff(c_111, plain, (![A_56, B_57]: (r1_xboole_0(A_56, B_57) | k3_xboole_0(A_56, B_57)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.31  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.29/1.31  tff(c_154, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=A_66 | k3_xboole_0(A_66, B_67)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_111, c_12])).
% 2.29/1.31  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.31  tff(c_163, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_154, c_38])).
% 2.29/1.31  tff(c_173, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_163])).
% 2.29/1.31  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.31  tff(c_213, plain, (![B_73, A_74]: (k1_tarski(B_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(B_73)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.29/1.31  tff(c_229, plain, (![B_73, B_8]: (k3_xboole_0(k1_tarski(B_73), B_8)=k1_tarski(B_73) | k3_xboole_0(k1_tarski(B_73), B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_213])).
% 2.29/1.31  tff(c_293, plain, (![B_86, B_87]: (k3_xboole_0(k1_tarski(B_86), B_87)=k1_xboole_0 | k1_tarski(B_86)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_229])).
% 2.29/1.31  tff(c_447, plain, (![B_113, B_114]: (k3_xboole_0(B_113, k1_tarski(B_114))=k1_xboole_0 | k1_tarski(B_114)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_293])).
% 2.29/1.31  tff(c_499, plain, (k1_tarski('#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_447, c_173])).
% 2.29/1.31  tff(c_16, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.29/1.31  tff(c_256, plain, (![B_84, B_85]: (k3_xboole_0(k1_tarski(B_84), B_85)=k1_tarski(B_84) | k3_xboole_0(k1_tarski(B_84), B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_213])).
% 2.29/1.31  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.31  tff(c_265, plain, (![B_84, B_85]: (k5_xboole_0(k1_tarski(B_84), k1_tarski(B_84))=k4_xboole_0(k1_tarski(B_84), B_85) | k3_xboole_0(k1_tarski(B_84), B_85)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256, c_8])).
% 2.29/1.31  tff(c_519, plain, (![B_124, B_125]: (k4_xboole_0(k1_tarski(B_124), B_125)=k1_xboole_0 | k3_xboole_0(k1_tarski(B_124), B_125)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_265])).
% 2.29/1.31  tff(c_40, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.31  tff(c_545, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_519, c_40])).
% 2.29/1.31  tff(c_553, plain, (k1_tarski('#skF_1')=k1_xboole_0 | k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_545, c_229])).
% 2.29/1.31  tff(c_586, plain, (k1_tarski('#skF_1')=k1_xboole_0 | k3_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_553])).
% 2.29/1.31  tff(c_588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_499, c_586])).
% 2.29/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  Inference rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Ref     : 0
% 2.29/1.31  #Sup     : 135
% 2.29/1.31  #Fact    : 1
% 2.29/1.31  #Define  : 0
% 2.29/1.31  #Split   : 1
% 2.29/1.31  #Chain   : 0
% 2.29/1.31  #Close   : 0
% 2.29/1.31  
% 2.29/1.31  Ordering : KBO
% 2.29/1.31  
% 2.29/1.31  Simplification rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Subsume      : 22
% 2.29/1.31  #Demod        : 18
% 2.29/1.31  #Tautology    : 71
% 2.29/1.31  #SimpNegUnit  : 7
% 2.29/1.31  #BackRed      : 0
% 2.29/1.31  
% 2.29/1.31  #Partial instantiations: 0
% 2.29/1.31  #Strategies tried      : 1
% 2.29/1.31  
% 2.29/1.31  Timing (in seconds)
% 2.29/1.31  ----------------------
% 2.29/1.31  Preprocessing        : 0.31
% 2.29/1.31  Parsing              : 0.17
% 2.29/1.31  CNF conversion       : 0.02
% 2.29/1.31  Main loop            : 0.24
% 2.29/1.31  Inferencing          : 0.09
% 2.29/1.31  Reduction            : 0.08
% 2.29/1.31  Demodulation         : 0.06
% 2.29/1.31  BG Simplification    : 0.01
% 2.29/1.31  Subsumption          : 0.04
% 2.29/1.31  Abstraction          : 0.02
% 2.29/1.31  MUC search           : 0.00
% 2.29/1.31  Cooper               : 0.00
% 2.29/1.31  Total                : 0.58
% 2.29/1.31  Index Insertion      : 0.00
% 2.29/1.31  Index Deletion       : 0.00
% 2.29/1.31  Index Matching       : 0.00
% 2.29/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:52 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 172 expanded)
%              Number of leaves         :   35 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 ( 159 expanded)
%              Number of equality atoms :   37 ( 133 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_385,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_412,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = k4_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_385])).

tff(c_419,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_412])).

tff(c_456,plain,(
    ! [A_99,B_100] : k2_xboole_0(k3_xboole_0(A_99,B_100),k4_xboole_0(A_99,B_100)) = A_99 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_495,plain,(
    ! [A_16] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_16,k1_xboole_0)) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_456])).

tff(c_501,plain,(
    ! [A_16] : k2_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_495])).

tff(c_54,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_211,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_24])).

tff(c_219,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_222,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_xboole_0) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_211,c_219])).

tff(c_227,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_222])).

tff(c_230,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_54])).

tff(c_525,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_230])).

tff(c_26,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_409,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_385])).

tff(c_418,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_409])).

tff(c_50,plain,(
    ! [B_65] : k4_xboole_0(k1_tarski(B_65),k1_tarski(B_65)) != k1_tarski(B_65) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_420,plain,(
    ! [B_65] : k1_tarski(B_65) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_50])).

tff(c_557,plain,(
    ! [B_65] : k1_tarski(B_65) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_420])).

tff(c_565,plain,(
    ! [A_16] : k3_xboole_0(A_16,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_525,c_16])).

tff(c_562,plain,(
    k2_tarski('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_227])).

tff(c_48,plain,(
    ! [A_62,B_63] : k3_xboole_0(k1_tarski(A_62),k2_tarski(A_62,B_63)) = k1_tarski(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_662,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_48])).

tff(c_1050,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_662])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_557,c_1050])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.77/1.39  
% 2.77/1.39  %Foreground sorts:
% 2.77/1.39  
% 2.77/1.39  
% 2.77/1.39  %Background operators:
% 2.77/1.39  
% 2.77/1.39  
% 2.77/1.39  %Foreground operators:
% 2.77/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.77/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.77/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.39  
% 2.77/1.40  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.77/1.40  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.77/1.40  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.77/1.40  tff(f_61, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.77/1.40  tff(f_100, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.77/1.40  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.77/1.40  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.77/1.40  tff(f_69, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.77/1.40  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.77/1.40  tff(f_96, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.77/1.40  tff(f_91, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.77/1.40  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.77/1.40  tff(c_16, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.40  tff(c_385, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.40  tff(c_412, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=k4_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_385])).
% 2.77/1.40  tff(c_419, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_412])).
% 2.77/1.40  tff(c_456, plain, (![A_99, B_100]: (k2_xboole_0(k3_xboole_0(A_99, B_100), k4_xboole_0(A_99, B_100))=A_99)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.40  tff(c_495, plain, (![A_16]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_16, k1_xboole_0))=A_16)), inference(superposition, [status(thm), theory('equality')], [c_16, c_456])).
% 2.77/1.40  tff(c_501, plain, (![A_16]: (k2_xboole_0(k1_xboole_0, A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_419, c_495])).
% 2.77/1.40  tff(c_54, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.77/1.40  tff(c_24, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.77/1.40  tff(c_211, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_24])).
% 2.77/1.40  tff(c_219, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.40  tff(c_222, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_xboole_0)=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_211, c_219])).
% 2.77/1.40  tff(c_227, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_222])).
% 2.77/1.40  tff(c_230, plain, (k2_xboole_0(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_227, c_54])).
% 2.77/1.40  tff(c_525, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_501, c_230])).
% 2.77/1.40  tff(c_26, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.77/1.40  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.40  tff(c_409, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_385])).
% 2.77/1.40  tff(c_418, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_409])).
% 2.77/1.40  tff(c_50, plain, (![B_65]: (k4_xboole_0(k1_tarski(B_65), k1_tarski(B_65))!=k1_tarski(B_65))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.77/1.40  tff(c_420, plain, (![B_65]: (k1_tarski(B_65)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_418, c_50])).
% 2.77/1.40  tff(c_557, plain, (![B_65]: (k1_tarski(B_65)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_525, c_420])).
% 2.77/1.40  tff(c_565, plain, (![A_16]: (k3_xboole_0(A_16, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_525, c_525, c_16])).
% 2.77/1.40  tff(c_562, plain, (k2_tarski('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_525, c_227])).
% 2.77/1.40  tff(c_48, plain, (![A_62, B_63]: (k3_xboole_0(k1_tarski(A_62), k2_tarski(A_62, B_63))=k1_tarski(A_62))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.77/1.40  tff(c_662, plain, (k3_xboole_0(k1_tarski('#skF_3'), '#skF_5')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_562, c_48])).
% 2.77/1.40  tff(c_1050, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_565, c_662])).
% 2.77/1.40  tff(c_1051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_557, c_1050])).
% 2.77/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.40  
% 2.77/1.40  Inference rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Ref     : 0
% 2.77/1.40  #Sup     : 243
% 2.77/1.40  #Fact    : 0
% 2.77/1.40  #Define  : 0
% 2.77/1.40  #Split   : 0
% 2.77/1.40  #Chain   : 0
% 2.77/1.40  #Close   : 0
% 2.77/1.40  
% 2.77/1.40  Ordering : KBO
% 2.77/1.40  
% 2.77/1.40  Simplification rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Subsume      : 1
% 2.77/1.40  #Demod        : 107
% 2.77/1.40  #Tautology    : 188
% 2.77/1.40  #SimpNegUnit  : 3
% 2.77/1.40  #BackRed      : 20
% 2.77/1.40  
% 2.77/1.40  #Partial instantiations: 0
% 2.77/1.40  #Strategies tried      : 1
% 2.77/1.40  
% 2.77/1.40  Timing (in seconds)
% 2.77/1.40  ----------------------
% 2.77/1.40  Preprocessing        : 0.31
% 2.77/1.40  Parsing              : 0.17
% 2.77/1.40  CNF conversion       : 0.02
% 2.77/1.40  Main loop            : 0.31
% 2.77/1.40  Inferencing          : 0.11
% 2.77/1.40  Reduction            : 0.11
% 2.77/1.40  Demodulation         : 0.09
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.04
% 2.77/1.40  Abstraction          : 0.02
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.65
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

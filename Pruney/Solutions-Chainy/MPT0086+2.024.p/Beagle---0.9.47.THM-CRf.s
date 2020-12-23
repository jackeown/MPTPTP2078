%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:16 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 103 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   34 (  95 expanded)
%              Number of equality atoms :   29 (  90 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_43])).

tff(c_61,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_362,plain,(
    ! [A_39,B_40] : k2_xboole_0(k4_xboole_0(A_39,B_40),k3_xboole_0(A_39,B_40)) = k2_xboole_0(k4_xboole_0(A_39,B_40),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_102])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k4_xboole_0(A_9,B_10),k3_xboole_0(A_9,C_11)) = k4_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_368,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(B_40,B_40)) = k2_xboole_0(k4_xboole_0(A_39,B_40),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_14])).

tff(c_398,plain,(
    ! [A_39,B_40] : k2_xboole_0(k4_xboole_0(A_39,B_40),A_39) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_61,c_368])).

tff(c_62,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_67,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = k3_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_79,plain,(
    ! [A_20] : k3_xboole_0(A_20,A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_162,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k4_xboole_0(A_27,B_28),k3_xboole_0(A_27,C_29)) = k4_xboole_0(A_27,k4_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_174,plain,(
    ! [A_20,B_28] : k4_xboole_0(A_20,k4_xboole_0(B_28,A_20)) = k2_xboole_0(k4_xboole_0(A_20,B_28),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_162])).

tff(c_829,plain,(
    ! [A_20,B_28] : k4_xboole_0(A_20,k4_xboole_0(B_28,A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_174])).

tff(c_830,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_174])).

tff(c_869,plain,(
    ! [A_57,B_58] : k3_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k4_xboole_0(A_57,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_12])).

tff(c_929,plain,(
    ! [A_59,B_60] : k3_xboole_0(A_59,k4_xboole_0(B_60,A_59)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_869])).

tff(c_961,plain,(
    ! [B_28,A_20] : k3_xboole_0(k4_xboole_0(B_28,A_20),A_20) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_929])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k3_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_16])).

tff(c_1077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.29  
% 2.45/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.29  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.45/1.29  
% 2.45/1.29  %Foreground sorts:
% 2.45/1.29  
% 2.45/1.29  
% 2.45/1.29  %Background operators:
% 2.45/1.29  
% 2.45/1.29  
% 2.45/1.29  %Foreground operators:
% 2.45/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.29  
% 2.45/1.30  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.45/1.30  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.45/1.30  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.45/1.30  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.45/1.30  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.45/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.45/1.30  tff(f_42, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.45/1.30  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.30  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.30  tff(c_43, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.30  tff(c_58, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_43])).
% 2.45/1.30  tff(c_61, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_58])).
% 2.45/1.30  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.30  tff(c_102, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.30  tff(c_362, plain, (![A_39, B_40]: (k2_xboole_0(k4_xboole_0(A_39, B_40), k3_xboole_0(A_39, B_40))=k2_xboole_0(k4_xboole_0(A_39, B_40), A_39))), inference(superposition, [status(thm), theory('equality')], [c_12, c_102])).
% 2.45/1.30  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k3_xboole_0(A_9, C_11))=k4_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.30  tff(c_368, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(B_40, B_40))=k2_xboole_0(k4_xboole_0(A_39, B_40), A_39))), inference(superposition, [status(thm), theory('equality')], [c_362, c_14])).
% 2.45/1.30  tff(c_398, plain, (![A_39, B_40]: (k2_xboole_0(k4_xboole_0(A_39, B_40), A_39)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_61, c_368])).
% 2.45/1.30  tff(c_62, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_58])).
% 2.45/1.30  tff(c_67, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=k3_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_62, c_12])).
% 2.45/1.30  tff(c_79, plain, (![A_20]: (k3_xboole_0(A_20, A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_67])).
% 2.45/1.30  tff(c_162, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k4_xboole_0(A_27, B_28), k3_xboole_0(A_27, C_29))=k4_xboole_0(A_27, k4_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.30  tff(c_174, plain, (![A_20, B_28]: (k4_xboole_0(A_20, k4_xboole_0(B_28, A_20))=k2_xboole_0(k4_xboole_0(A_20, B_28), A_20))), inference(superposition, [status(thm), theory('equality')], [c_79, c_162])).
% 2.45/1.30  tff(c_829, plain, (![A_20, B_28]: (k4_xboole_0(A_20, k4_xboole_0(B_28, A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_398, c_174])).
% 2.45/1.30  tff(c_830, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(B_58, A_57))=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_398, c_174])).
% 2.45/1.30  tff(c_869, plain, (![A_57, B_58]: (k3_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k4_xboole_0(A_57, A_57))), inference(superposition, [status(thm), theory('equality')], [c_830, c_12])).
% 2.45/1.30  tff(c_929, plain, (![A_59, B_60]: (k3_xboole_0(A_59, k4_xboole_0(B_60, A_59))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_869])).
% 2.45/1.30  tff(c_961, plain, (![B_28, A_20]: (k3_xboole_0(k4_xboole_0(B_28, A_20), A_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_829, c_929])).
% 2.45/1.30  tff(c_34, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k3_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.30  tff(c_16, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.45/1.30  tff(c_42, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_16])).
% 2.45/1.30  tff(c_1077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_961, c_42])).
% 2.45/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.30  
% 2.45/1.30  Inference rules
% 2.45/1.30  ----------------------
% 2.45/1.30  #Ref     : 0
% 2.45/1.30  #Sup     : 256
% 2.45/1.30  #Fact    : 0
% 2.45/1.30  #Define  : 0
% 2.45/1.30  #Split   : 0
% 2.45/1.30  #Chain   : 0
% 2.45/1.30  #Close   : 0
% 2.45/1.30  
% 2.45/1.30  Ordering : KBO
% 2.45/1.30  
% 2.45/1.30  Simplification rules
% 2.45/1.30  ----------------------
% 2.45/1.30  #Subsume      : 0
% 2.45/1.30  #Demod        : 214
% 2.45/1.30  #Tautology    : 188
% 2.45/1.30  #SimpNegUnit  : 0
% 2.45/1.30  #BackRed      : 4
% 2.45/1.30  
% 2.45/1.30  #Partial instantiations: 0
% 2.45/1.30  #Strategies tried      : 1
% 2.45/1.30  
% 2.45/1.30  Timing (in seconds)
% 2.45/1.30  ----------------------
% 2.45/1.31  Preprocessing        : 0.25
% 2.45/1.31  Parsing              : 0.14
% 2.45/1.31  CNF conversion       : 0.01
% 2.45/1.31  Main loop            : 0.32
% 2.45/1.31  Inferencing          : 0.13
% 2.45/1.31  Reduction            : 0.11
% 2.45/1.31  Demodulation         : 0.09
% 2.45/1.31  BG Simplification    : 0.02
% 2.45/1.31  Subsumption          : 0.04
% 2.45/1.31  Abstraction          : 0.02
% 2.45/1.31  MUC search           : 0.00
% 2.45/1.31  Cooper               : 0.00
% 2.45/1.31  Total                : 0.60
% 2.45/1.31  Index Insertion      : 0.00
% 2.45/1.31  Index Deletion       : 0.00
% 2.45/1.31  Index Matching       : 0.00
% 2.45/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:51 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  29 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [B_11,A_12] : k2_xboole_0(B_11,A_12) = k2_xboole_0(A_12,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_4])).

tff(c_113,plain,(
    ! [A_14,B_15] : k4_xboole_0(k2_xboole_0(A_14,B_15),B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_113])).

tff(c_134,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_122])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(k2_xboole_0(A_6,B_7),B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_139,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [B_7,A_6] : k2_xboole_0(B_7,k4_xboole_0(A_6,B_7)) = k2_xboole_0(B_7,k2_xboole_0(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_139])).

tff(c_323,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,k2_xboole_0(A_24,B_23)) = k2_xboole_0(B_23,A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_155])).

tff(c_430,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,k2_xboole_0(B_27,A_28)) = k2_xboole_0(B_27,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_323])).

tff(c_449,plain,(
    ! [B_27,A_28] : k4_xboole_0(k2_xboole_0(B_27,A_28),k2_xboole_0(B_27,A_28)) = k4_xboole_0(B_27,k2_xboole_0(B_27,A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_8])).

tff(c_494,plain,(
    ! [B_27,A_28] : k4_xboole_0(B_27,k2_xboole_0(B_27,A_28)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_449])).

tff(c_12,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.23  %$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.23  
% 1.81/1.23  %Foreground sorts:
% 1.81/1.23  
% 1.81/1.23  
% 1.81/1.23  %Background operators:
% 1.81/1.23  
% 1.81/1.23  
% 1.81/1.23  %Foreground operators:
% 1.81/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.23  
% 1.81/1.23  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.81/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.81/1.23  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.81/1.23  tff(f_33, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.81/1.23  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.81/1.23  tff(f_38, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.81/1.23  tff(c_10, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.23  tff(c_29, plain, (![B_11, A_12]: (k2_xboole_0(B_11, A_12)=k2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.23  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.23  tff(c_45, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(superposition, [status(thm), theory('equality')], [c_29, c_4])).
% 1.81/1.23  tff(c_113, plain, (![A_14, B_15]: (k4_xboole_0(k2_xboole_0(A_14, B_15), B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.23  tff(c_122, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_45, c_113])).
% 1.81/1.23  tff(c_134, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_122])).
% 1.81/1.23  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.23  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.23  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(k2_xboole_0(A_6, B_7), B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.23  tff(c_139, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.23  tff(c_155, plain, (![B_7, A_6]: (k2_xboole_0(B_7, k4_xboole_0(A_6, B_7))=k2_xboole_0(B_7, k2_xboole_0(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_139])).
% 1.81/1.23  tff(c_323, plain, (![B_23, A_24]: (k2_xboole_0(B_23, k2_xboole_0(A_24, B_23))=k2_xboole_0(B_23, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_155])).
% 1.81/1.23  tff(c_430, plain, (![B_27, A_28]: (k2_xboole_0(B_27, k2_xboole_0(B_27, A_28))=k2_xboole_0(B_27, A_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_323])).
% 1.81/1.23  tff(c_449, plain, (![B_27, A_28]: (k4_xboole_0(k2_xboole_0(B_27, A_28), k2_xboole_0(B_27, A_28))=k4_xboole_0(B_27, k2_xboole_0(B_27, A_28)))), inference(superposition, [status(thm), theory('equality')], [c_430, c_8])).
% 1.81/1.23  tff(c_494, plain, (![B_27, A_28]: (k4_xboole_0(B_27, k2_xboole_0(B_27, A_28))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_449])).
% 1.81/1.23  tff(c_12, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.81/1.23  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_494, c_12])).
% 1.81/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.23  
% 1.81/1.23  Inference rules
% 1.81/1.23  ----------------------
% 1.81/1.23  #Ref     : 0
% 1.81/1.23  #Sup     : 115
% 1.81/1.23  #Fact    : 0
% 1.81/1.23  #Define  : 0
% 1.81/1.23  #Split   : 0
% 1.81/1.23  #Chain   : 0
% 1.81/1.23  #Close   : 0
% 1.81/1.23  
% 1.81/1.24  Ordering : KBO
% 1.81/1.24  
% 1.81/1.24  Simplification rules
% 1.81/1.24  ----------------------
% 1.81/1.24  #Subsume      : 0
% 1.81/1.24  #Demod        : 112
% 1.81/1.24  #Tautology    : 100
% 1.81/1.24  #SimpNegUnit  : 0
% 1.81/1.24  #BackRed      : 1
% 1.81/1.24  
% 1.81/1.24  #Partial instantiations: 0
% 1.81/1.24  #Strategies tried      : 1
% 1.81/1.24  
% 1.81/1.24  Timing (in seconds)
% 1.81/1.24  ----------------------
% 2.10/1.24  Preprocessing        : 0.25
% 2.10/1.24  Parsing              : 0.13
% 2.10/1.24  CNF conversion       : 0.01
% 2.10/1.24  Main loop            : 0.21
% 2.10/1.24  Inferencing          : 0.07
% 2.10/1.24  Reduction            : 0.10
% 2.10/1.24  Demodulation         : 0.08
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.02
% 2.10/1.24  Abstraction          : 0.01
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.48
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:51 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   32 (  37 expanded)
%              Number of equality atoms :   27 (  32 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [B_6] : k3_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_117,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [B_6] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_117])).

tff(c_133,plain,(
    ! [B_34] : k4_xboole_0(k1_xboole_0,B_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_126])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_138,plain,(
    ! [B_34] : k5_xboole_0(B_34,k1_xboole_0) = k2_xboole_0(B_34,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_14])).

tff(c_152,plain,(
    ! [B_35] : k2_xboole_0(B_35,k1_xboole_0) = B_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_138])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_158,plain,(
    ! [B_35] : k4_xboole_0(B_35,B_35) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_10])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_129,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_226,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_129])).

tff(c_183,plain,(
    ! [A_37,B_38] : k3_xboole_0(k1_tarski(A_37),k2_tarski(A_37,B_38)) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_189,plain,(
    ! [A_37,B_38] : k5_xboole_0(k1_tarski(A_37),k1_tarski(A_37)) = k4_xboole_0(k1_tarski(A_37),k2_tarski(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_4])).

tff(c_283,plain,(
    ! [A_37,B_38] : k4_xboole_0(k1_tarski(A_37),k2_tarski(A_37,B_38)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_189])).

tff(c_22,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.31  
% 1.85/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.31  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.85/1.31  
% 1.85/1.31  %Foreground sorts:
% 1.85/1.31  
% 1.85/1.31  
% 1.85/1.31  %Background operators:
% 1.85/1.31  
% 1.85/1.31  
% 1.85/1.31  %Foreground operators:
% 1.85/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.85/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.31  
% 1.85/1.32  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.85/1.32  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.85/1.32  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.85/1.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.85/1.32  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.85/1.32  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.85/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.85/1.32  tff(f_47, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 1.85/1.32  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.85/1.32  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.85/1.32  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.32  tff(c_46, plain, (![A_23]: (k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.32  tff(c_57, plain, (![B_6]: (k3_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_46])).
% 1.85/1.32  tff(c_117, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.32  tff(c_126, plain, (![B_6]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_6))), inference(superposition, [status(thm), theory('equality')], [c_57, c_117])).
% 1.85/1.32  tff(c_133, plain, (![B_34]: (k4_xboole_0(k1_xboole_0, B_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_126])).
% 1.85/1.32  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.32  tff(c_138, plain, (![B_34]: (k5_xboole_0(B_34, k1_xboole_0)=k2_xboole_0(B_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_133, c_14])).
% 1.85/1.32  tff(c_152, plain, (![B_35]: (k2_xboole_0(B_35, k1_xboole_0)=B_35)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_138])).
% 1.85/1.32  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.85/1.32  tff(c_158, plain, (![B_35]: (k4_xboole_0(B_35, B_35)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_10])).
% 1.85/1.32  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.32  tff(c_129, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 1.85/1.32  tff(c_226, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_129])).
% 1.85/1.32  tff(c_183, plain, (![A_37, B_38]: (k3_xboole_0(k1_tarski(A_37), k2_tarski(A_37, B_38))=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.85/1.32  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.32  tff(c_189, plain, (![A_37, B_38]: (k5_xboole_0(k1_tarski(A_37), k1_tarski(A_37))=k4_xboole_0(k1_tarski(A_37), k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_4])).
% 1.85/1.32  tff(c_283, plain, (![A_37, B_38]: (k4_xboole_0(k1_tarski(A_37), k2_tarski(A_37, B_38))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_226, c_189])).
% 1.85/1.32  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.85/1.32  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_22])).
% 1.85/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.32  
% 1.85/1.32  Inference rules
% 1.85/1.32  ----------------------
% 1.85/1.32  #Ref     : 0
% 1.85/1.32  #Sup     : 61
% 1.85/1.32  #Fact    : 0
% 1.85/1.32  #Define  : 0
% 1.85/1.32  #Split   : 0
% 1.85/1.32  #Chain   : 0
% 1.85/1.32  #Close   : 0
% 1.85/1.32  
% 1.85/1.32  Ordering : KBO
% 1.85/1.32  
% 1.85/1.32  Simplification rules
% 1.85/1.32  ----------------------
% 1.85/1.32  #Subsume      : 0
% 1.85/1.32  #Demod        : 20
% 1.85/1.32  #Tautology    : 52
% 1.85/1.32  #SimpNegUnit  : 0
% 1.85/1.32  #BackRed      : 1
% 1.85/1.32  
% 1.85/1.32  #Partial instantiations: 0
% 1.85/1.32  #Strategies tried      : 1
% 1.85/1.32  
% 1.85/1.32  Timing (in seconds)
% 1.85/1.32  ----------------------
% 1.85/1.32  Preprocessing        : 0.28
% 1.85/1.32  Parsing              : 0.14
% 1.85/1.32  CNF conversion       : 0.01
% 1.85/1.32  Main loop            : 0.14
% 1.85/1.32  Inferencing          : 0.06
% 1.85/1.33  Reduction            : 0.05
% 1.85/1.33  Demodulation         : 0.03
% 1.85/1.33  BG Simplification    : 0.01
% 1.85/1.33  Subsumption          : 0.02
% 1.85/1.33  Abstraction          : 0.01
% 1.85/1.33  MUC search           : 0.00
% 1.85/1.33  Cooper               : 0.00
% 1.85/1.33  Total                : 0.44
% 1.85/1.33  Index Insertion      : 0.00
% 1.85/1.33  Index Deletion       : 0.00
% 1.85/1.33  Index Matching       : 0.00
% 1.85/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

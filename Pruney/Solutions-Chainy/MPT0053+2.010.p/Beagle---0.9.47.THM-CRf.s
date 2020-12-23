%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:52 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [B_14,A_15] : k3_xboole_0(B_14,A_15) = k3_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [B_19,A_20] : r1_tarski(k3_xboole_0(B_19,A_20),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_4])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    ! [B_27,A_28] : k4_xboole_0(k3_xboole_0(B_27,A_28),A_28) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_10])).

tff(c_145,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_126])).

tff(c_12,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:18:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.72/1.14  
% 1.72/1.14  %Foreground sorts:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Background operators:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Foreground operators:
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.14  
% 1.72/1.15  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.72/1.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.72/1.15  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.72/1.15  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.72/1.15  tff(f_38, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.72/1.15  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.15  tff(c_27, plain, (![B_14, A_15]: (k3_xboole_0(B_14, A_15)=k3_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.15  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.15  tff(c_82, plain, (![B_19, A_20]: (r1_tarski(k3_xboole_0(B_19, A_20), A_20))), inference(superposition, [status(thm), theory('equality')], [c_27, c_4])).
% 1.72/1.15  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.15  tff(c_126, plain, (![B_27, A_28]: (k4_xboole_0(k3_xboole_0(B_27, A_28), A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_82, c_10])).
% 1.72/1.15  tff(c_145, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_126])).
% 1.72/1.15  tff(c_12, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.15  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_12])).
% 1.72/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.15  
% 1.72/1.15  Inference rules
% 1.72/1.15  ----------------------
% 1.72/1.15  #Ref     : 0
% 1.72/1.15  #Sup     : 35
% 1.72/1.15  #Fact    : 0
% 1.72/1.15  #Define  : 0
% 1.72/1.15  #Split   : 0
% 1.72/1.15  #Chain   : 0
% 1.72/1.15  #Close   : 0
% 1.72/1.15  
% 1.72/1.15  Ordering : KBO
% 1.72/1.15  
% 1.72/1.15  Simplification rules
% 1.72/1.15  ----------------------
% 1.72/1.15  #Subsume      : 0
% 1.72/1.15  #Demod        : 9
% 1.72/1.15  #Tautology    : 27
% 1.72/1.15  #SimpNegUnit  : 0
% 1.72/1.15  #BackRed      : 1
% 1.72/1.15  
% 1.72/1.15  #Partial instantiations: 0
% 1.72/1.15  #Strategies tried      : 1
% 1.72/1.15  
% 1.72/1.15  Timing (in seconds)
% 1.72/1.15  ----------------------
% 1.72/1.15  Preprocessing        : 0.25
% 1.72/1.15  Parsing              : 0.14
% 1.72/1.15  CNF conversion       : 0.01
% 1.72/1.15  Main loop            : 0.13
% 1.72/1.15  Inferencing          : 0.05
% 1.72/1.15  Reduction            : 0.04
% 1.72/1.15  Demodulation         : 0.03
% 1.72/1.15  BG Simplification    : 0.01
% 1.72/1.15  Subsumption          : 0.02
% 1.72/1.15  Abstraction          : 0.01
% 1.72/1.15  MUC search           : 0.00
% 1.72/1.15  Cooper               : 0.00
% 1.72/1.15  Total                : 0.40
% 1.72/1.15  Index Insertion      : 0.00
% 1.72/1.15  Index Deletion       : 0.00
% 1.72/1.15  Index Matching       : 0.00
% 1.72/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

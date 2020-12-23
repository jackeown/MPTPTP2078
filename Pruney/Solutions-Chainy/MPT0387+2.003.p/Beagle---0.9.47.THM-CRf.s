%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:11 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_12,plain,(
    k1_setfam_1('#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    r2_hidden(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_setfam_1(B_5),A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    ! [B_10,A_11] :
      ( B_10 = A_11
      | ~ r1_tarski(B_10,A_11)
      | ~ r1_tarski(A_11,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_19])).

tff(c_50,plain,(
    ! [B_13] :
      ( k1_setfam_1(B_13) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_13) ) ),
    inference(resolution,[status(thm)],[c_10,c_32])).

tff(c_53,plain,(
    k1_setfam_1('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_50])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.08  
% 1.49/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.08  %$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1
% 1.49/1.08  
% 1.49/1.08  %Foreground sorts:
% 1.49/1.08  
% 1.49/1.08  
% 1.49/1.08  %Background operators:
% 1.49/1.08  
% 1.49/1.08  
% 1.49/1.08  %Foreground operators:
% 1.49/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.49/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.49/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.49/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.49/1.08  
% 1.61/1.09  tff(f_42, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_setfam_1)).
% 1.61/1.09  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.61/1.09  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.61/1.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.61/1.09  tff(c_12, plain, (k1_setfam_1('#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.09  tff(c_14, plain, (r2_hidden(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.09  tff(c_10, plain, (![B_5, A_4]: (r1_tarski(k1_setfam_1(B_5), A_4) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.61/1.09  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.09  tff(c_19, plain, (![B_10, A_11]: (B_10=A_11 | ~r1_tarski(B_10, A_11) | ~r1_tarski(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.09  tff(c_32, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_19])).
% 1.61/1.09  tff(c_50, plain, (![B_13]: (k1_setfam_1(B_13)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_13))), inference(resolution, [status(thm)], [c_10, c_32])).
% 1.61/1.09  tff(c_53, plain, (k1_setfam_1('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_50])).
% 1.61/1.09  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_53])).
% 1.61/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  Inference rules
% 1.61/1.09  ----------------------
% 1.61/1.09  #Ref     : 0
% 1.61/1.09  #Sup     : 7
% 1.61/1.09  #Fact    : 0
% 1.61/1.09  #Define  : 0
% 1.61/1.09  #Split   : 0
% 1.61/1.09  #Chain   : 0
% 1.61/1.09  #Close   : 0
% 1.61/1.09  
% 1.61/1.09  Ordering : KBO
% 1.61/1.09  
% 1.61/1.09  Simplification rules
% 1.61/1.09  ----------------------
% 1.61/1.09  #Subsume      : 0
% 1.61/1.09  #Demod        : 2
% 1.61/1.09  #Tautology    : 4
% 1.61/1.09  #SimpNegUnit  : 1
% 1.61/1.09  #BackRed      : 0
% 1.61/1.09  
% 1.61/1.09  #Partial instantiations: 0
% 1.61/1.09  #Strategies tried      : 1
% 1.61/1.09  
% 1.61/1.09  Timing (in seconds)
% 1.61/1.09  ----------------------
% 1.61/1.09  Preprocessing        : 0.25
% 1.61/1.09  Parsing              : 0.14
% 1.61/1.09  CNF conversion       : 0.01
% 1.61/1.09  Main loop            : 0.08
% 1.61/1.09  Inferencing          : 0.04
% 1.61/1.09  Reduction            : 0.02
% 1.61/1.09  Demodulation         : 0.02
% 1.61/1.09  BG Simplification    : 0.01
% 1.61/1.09  Subsumption          : 0.01
% 1.61/1.09  Abstraction          : 0.00
% 1.61/1.09  MUC search           : 0.00
% 1.61/1.09  Cooper               : 0.00
% 1.61/1.09  Total                : 0.35
% 1.61/1.09  Index Insertion      : 0.00
% 1.61/1.09  Index Deletion       : 0.00
% 1.61/1.09  Index Matching       : 0.00
% 1.61/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

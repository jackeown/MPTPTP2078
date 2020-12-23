%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:09 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   37 (  38 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [B_48,A_49] :
      ( k3_xboole_0(B_48,k1_tarski(A_49)) = k1_tarski(A_49)
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_138,plain,(
    ! [A_49,B_48] :
      ( k5_xboole_0(k1_tarski(A_49),k1_tarski(A_49)) = k4_xboole_0(k1_tarski(A_49),B_48)
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_98])).

tff(c_162,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(k1_tarski(A_50),B_51) = k1_xboole_0
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_138])).

tff(c_30,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_176,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_30])).

tff(c_191,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(k1_tarski(A_57),B_58) = k1_tarski(A_57)
      | r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_203,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_28])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:50:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.27  
% 1.97/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.27  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.27  
% 1.97/1.27  %Foreground sorts:
% 1.97/1.27  
% 1.97/1.27  
% 1.97/1.27  %Background operators:
% 1.97/1.27  
% 1.97/1.27  
% 1.97/1.27  %Foreground operators:
% 1.97/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.27  
% 1.97/1.28  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.97/1.28  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.97/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.97/1.28  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.97/1.28  tff(f_59, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 1.97/1.28  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.97/1.28  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.28  tff(c_132, plain, (![B_48, A_49]: (k3_xboole_0(B_48, k1_tarski(A_49))=k1_tarski(A_49) | ~r2_hidden(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.28  tff(c_89, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.28  tff(c_98, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_89])).
% 1.97/1.28  tff(c_138, plain, (![A_49, B_48]: (k5_xboole_0(k1_tarski(A_49), k1_tarski(A_49))=k4_xboole_0(k1_tarski(A_49), B_48) | ~r2_hidden(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_132, c_98])).
% 1.97/1.28  tff(c_162, plain, (![A_50, B_51]: (k4_xboole_0(k1_tarski(A_50), B_51)=k1_xboole_0 | ~r2_hidden(A_50, B_51))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_138])).
% 1.97/1.28  tff(c_30, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.97/1.28  tff(c_176, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_162, c_30])).
% 1.97/1.28  tff(c_191, plain, (![A_57, B_58]: (k4_xboole_0(k1_tarski(A_57), B_58)=k1_tarski(A_57) | r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.97/1.28  tff(c_28, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.97/1.28  tff(c_203, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_191, c_28])).
% 1.97/1.28  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_203])).
% 1.97/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.28  
% 1.97/1.28  Inference rules
% 1.97/1.28  ----------------------
% 1.97/1.28  #Ref     : 0
% 1.97/1.28  #Sup     : 46
% 1.97/1.28  #Fact    : 0
% 1.97/1.28  #Define  : 0
% 1.97/1.28  #Split   : 0
% 1.97/1.28  #Chain   : 0
% 1.97/1.28  #Close   : 0
% 1.97/1.28  
% 1.97/1.28  Ordering : KBO
% 1.97/1.28  
% 1.97/1.28  Simplification rules
% 1.97/1.28  ----------------------
% 1.97/1.28  #Subsume      : 1
% 1.97/1.28  #Demod        : 4
% 1.97/1.28  #Tautology    : 32
% 1.97/1.28  #SimpNegUnit  : 1
% 1.97/1.28  #BackRed      : 0
% 1.97/1.28  
% 1.97/1.28  #Partial instantiations: 0
% 1.97/1.28  #Strategies tried      : 1
% 1.97/1.28  
% 1.97/1.28  Timing (in seconds)
% 1.97/1.28  ----------------------
% 1.97/1.28  Preprocessing        : 0.33
% 1.97/1.28  Parsing              : 0.18
% 1.97/1.28  CNF conversion       : 0.02
% 1.97/1.28  Main loop            : 0.14
% 1.97/1.28  Inferencing          : 0.06
% 1.97/1.28  Reduction            : 0.04
% 1.97/1.28  Demodulation         : 0.03
% 1.97/1.28  BG Simplification    : 0.01
% 1.97/1.28  Subsumption          : 0.02
% 1.97/1.28  Abstraction          : 0.01
% 1.97/1.28  MUC search           : 0.00
% 1.97/1.28  Cooper               : 0.00
% 1.97/1.28  Total                : 0.49
% 1.97/1.28  Index Insertion      : 0.00
% 1.97/1.28  Index Deletion       : 0.00
% 1.97/1.28  Index Matching       : 0.00
% 1.97/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:05:55 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_14,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_tarski(A_10)) = k1_ordinal1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ! [B_16,A_17] : k2_xboole_0(B_16,A_17) = k2_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(B_19,A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_88,plain,(
    ! [A_10] : r1_tarski(k1_tarski(A_10),k1_ordinal1(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_79])).

tff(c_94,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,B_24)
      | ~ r1_tarski(k1_tarski(A_23),B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [A_10] : r2_hidden(A_10,k1_ordinal1(A_10)) ),
    inference(resolution,[status(thm)],[c_88,c_94])).

tff(c_16,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.10  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1
% 1.64/1.10  
% 1.64/1.10  %Foreground sorts:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Background operators:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Foreground operators:
% 1.64/1.10  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.10  
% 1.64/1.11  tff(f_39, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.64/1.11  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.64/1.11  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.64/1.11  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.64/1.11  tff(f_42, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.64/1.11  tff(c_14, plain, (![A_10]: (k2_xboole_0(A_10, k1_tarski(A_10))=k1_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.11  tff(c_40, plain, (![B_16, A_17]: (k2_xboole_0(B_16, A_17)=k2_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.11  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.11  tff(c_79, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(B_19, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4])).
% 1.64/1.11  tff(c_88, plain, (![A_10]: (r1_tarski(k1_tarski(A_10), k1_ordinal1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_79])).
% 1.64/1.11  tff(c_94, plain, (![A_23, B_24]: (r2_hidden(A_23, B_24) | ~r1_tarski(k1_tarski(A_23), B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.11  tff(c_114, plain, (![A_10]: (r2_hidden(A_10, k1_ordinal1(A_10)))), inference(resolution, [status(thm)], [c_88, c_94])).
% 1.64/1.11  tff(c_16, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.11  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_16])).
% 1.64/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  Inference rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Ref     : 0
% 1.64/1.11  #Sup     : 23
% 1.64/1.11  #Fact    : 0
% 1.64/1.11  #Define  : 0
% 1.64/1.11  #Split   : 0
% 1.64/1.11  #Chain   : 0
% 1.64/1.11  #Close   : 0
% 1.64/1.11  
% 1.64/1.11  Ordering : KBO
% 1.64/1.11  
% 1.64/1.11  Simplification rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Subsume      : 0
% 1.64/1.11  #Demod        : 4
% 1.64/1.11  #Tautology    : 16
% 1.64/1.11  #SimpNegUnit  : 0
% 1.64/1.11  #BackRed      : 1
% 1.64/1.11  
% 1.64/1.11  #Partial instantiations: 0
% 1.64/1.11  #Strategies tried      : 1
% 1.64/1.11  
% 1.64/1.11  Timing (in seconds)
% 1.64/1.11  ----------------------
% 1.64/1.11  Preprocessing        : 0.27
% 1.64/1.12  Parsing              : 0.14
% 1.64/1.12  CNF conversion       : 0.01
% 1.64/1.12  Main loop            : 0.10
% 1.64/1.12  Inferencing          : 0.04
% 1.64/1.12  Reduction            : 0.03
% 1.64/1.12  Demodulation         : 0.03
% 1.64/1.12  BG Simplification    : 0.01
% 1.64/1.12  Subsumption          : 0.01
% 1.64/1.12  Abstraction          : 0.01
% 1.64/1.12  MUC search           : 0.00
% 1.64/1.12  Cooper               : 0.00
% 1.64/1.12  Total                : 0.39
% 1.64/1.12  Index Insertion      : 0.00
% 1.64/1.12  Index Deletion       : 0.00
% 1.64/1.12  Index Matching       : 0.00
% 1.64/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:52 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  34 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k3_tarski(A),B)
          & r2_hidden(C,A) )
       => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k3_tarski(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    r1_tarski(k3_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    k2_xboole_0(k3_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    k2_xboole_0('#skF_2',k3_tarski('#skF_1')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_81,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_tarski(A_16,k2_xboole_0(C_17,B_18))
      | ~ r1_tarski(A_16,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,'#skF_2')
      | ~ r1_tarski(A_19,k3_tarski('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_81])).

tff(c_104,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,'#skF_2')
      | ~ r2_hidden(A_20,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_107,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_104])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:29:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.09  
% 1.66/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.10  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.66/1.10  
% 1.66/1.10  %Foreground sorts:
% 1.66/1.10  
% 1.66/1.10  
% 1.66/1.10  %Background operators:
% 1.66/1.10  
% 1.66/1.10  
% 1.66/1.10  %Foreground operators:
% 1.66/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.66/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.10  
% 1.66/1.11  tff(f_46, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 1.66/1.11  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.66/1.11  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.66/1.11  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.66/1.11  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.66/1.11  tff(c_10, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.11  tff(c_12, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.11  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k3_tarski(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.66/1.11  tff(c_14, plain, (r1_tarski(k3_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.11  tff(c_49, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.11  tff(c_57, plain, (k2_xboole_0(k3_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_49])).
% 1.66/1.11  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.11  tff(c_61, plain, (k2_xboole_0('#skF_2', k3_tarski('#skF_1'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 1.66/1.11  tff(c_81, plain, (![A_16, C_17, B_18]: (r1_tarski(A_16, k2_xboole_0(C_17, B_18)) | ~r1_tarski(A_16, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.11  tff(c_98, plain, (![A_19]: (r1_tarski(A_19, '#skF_2') | ~r1_tarski(A_19, k3_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_61, c_81])).
% 1.66/1.11  tff(c_104, plain, (![A_20]: (r1_tarski(A_20, '#skF_2') | ~r2_hidden(A_20, '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_98])).
% 1.66/1.11  tff(c_107, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_104])).
% 1.66/1.11  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_107])).
% 1.66/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.11  
% 1.66/1.11  Inference rules
% 1.66/1.11  ----------------------
% 1.66/1.11  #Ref     : 0
% 1.66/1.11  #Sup     : 25
% 1.66/1.11  #Fact    : 0
% 1.66/1.11  #Define  : 0
% 1.66/1.11  #Split   : 0
% 1.66/1.11  #Chain   : 0
% 1.66/1.11  #Close   : 0
% 1.66/1.11  
% 1.66/1.11  Ordering : KBO
% 1.66/1.11  
% 1.66/1.11  Simplification rules
% 1.66/1.11  ----------------------
% 1.66/1.11  #Subsume      : 0
% 1.66/1.11  #Demod        : 3
% 1.66/1.11  #Tautology    : 16
% 1.66/1.11  #SimpNegUnit  : 1
% 1.66/1.11  #BackRed      : 0
% 1.66/1.11  
% 1.66/1.11  #Partial instantiations: 0
% 1.66/1.11  #Strategies tried      : 1
% 1.66/1.11  
% 1.66/1.11  Timing (in seconds)
% 1.66/1.11  ----------------------
% 1.66/1.11  Preprocessing        : 0.25
% 1.66/1.11  Parsing              : 0.14
% 1.66/1.11  CNF conversion       : 0.01
% 1.66/1.11  Main loop            : 0.11
% 1.66/1.11  Inferencing          : 0.05
% 1.66/1.11  Reduction            : 0.03
% 1.66/1.11  Demodulation         : 0.03
% 1.66/1.11  BG Simplification    : 0.01
% 1.66/1.11  Subsumption          : 0.02
% 1.66/1.11  Abstraction          : 0.00
% 1.66/1.11  MUC search           : 0.00
% 1.66/1.11  Cooper               : 0.00
% 1.66/1.11  Total                : 0.38
% 1.66/1.11  Index Insertion      : 0.00
% 1.66/1.11  Index Deletion       : 0.00
% 1.66/1.11  Index Matching       : 0.00
% 1.66/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

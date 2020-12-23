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
% DateTime   : Thu Dec  3 09:44:08 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 (  51 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_133,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_tarski(k3_xboole_0(A_31,C_32),k3_xboole_0(B_33,C_32))
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_19,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_53,plain,(
    ! [B_17,A_18] :
      ( r1_xboole_0(B_17,A_18)
      | ~ r1_xboole_0(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_19,c_53])).

tff(c_90,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_xboole_0(A_25,C_26)
      | ~ r1_xboole_0(B_27,C_26)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [A_25] :
      ( r1_xboole_0(A_25,'#skF_1')
      | ~ r1_tarski(A_25,k3_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_56,c_90])).

tff(c_160,plain,(
    ! [A_36] :
      ( r1_xboole_0(k3_xboole_0(A_36,'#skF_2'),'#skF_1')
      | ~ r1_tarski(A_36,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_133,c_95])).

tff(c_57,plain,(
    ! [A_19,B_20] :
      ( ~ r1_xboole_0(k3_xboole_0(A_19,B_20),B_20)
      | r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_57])).

tff(c_166,plain,
    ( r1_xboole_0('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_60])).

tff(c_180,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_166])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_185,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.37  
% 2.05/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.38  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.05/1.38  
% 2.05/1.38  %Foreground sorts:
% 2.05/1.38  
% 2.05/1.38  
% 2.05/1.38  %Background operators:
% 2.05/1.38  
% 2.05/1.38  
% 2.05/1.38  %Foreground operators:
% 2.05/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.38  
% 2.05/1.39  tff(f_58, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.05/1.39  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 2.05/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.05/1.39  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.05/1.39  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.05/1.39  tff(f_49, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.05/1.39  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.39  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.39  tff(c_133, plain, (![A_31, C_32, B_33]: (r1_tarski(k3_xboole_0(A_31, C_32), k3_xboole_0(B_33, C_32)) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.39  tff(c_14, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.39  tff(c_19, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.05/1.39  tff(c_53, plain, (![B_17, A_18]: (r1_xboole_0(B_17, A_18) | ~r1_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.39  tff(c_56, plain, (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_19, c_53])).
% 2.05/1.39  tff(c_90, plain, (![A_25, C_26, B_27]: (r1_xboole_0(A_25, C_26) | ~r1_xboole_0(B_27, C_26) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.05/1.39  tff(c_95, plain, (![A_25]: (r1_xboole_0(A_25, '#skF_1') | ~r1_tarski(A_25, k3_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_90])).
% 2.05/1.39  tff(c_160, plain, (![A_36]: (r1_xboole_0(k3_xboole_0(A_36, '#skF_2'), '#skF_1') | ~r1_tarski(A_36, '#skF_3'))), inference(resolution, [status(thm)], [c_133, c_95])).
% 2.05/1.39  tff(c_57, plain, (![A_19, B_20]: (~r1_xboole_0(k3_xboole_0(A_19, B_20), B_20) | r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.39  tff(c_60, plain, (![B_2, A_1]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), B_2) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_57])).
% 2.05/1.39  tff(c_166, plain, (r1_xboole_0('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_160, c_60])).
% 2.05/1.39  tff(c_180, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_166])).
% 2.05/1.39  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.39  tff(c_185, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_180, c_4])).
% 2.05/1.39  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_185])).
% 2.05/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.39  
% 2.05/1.39  Inference rules
% 2.05/1.39  ----------------------
% 2.05/1.39  #Ref     : 0
% 2.05/1.39  #Sup     : 42
% 2.05/1.39  #Fact    : 0
% 2.05/1.39  #Define  : 0
% 2.05/1.39  #Split   : 2
% 2.05/1.39  #Chain   : 0
% 2.05/1.39  #Close   : 0
% 2.05/1.39  
% 2.05/1.39  Ordering : KBO
% 2.05/1.39  
% 2.05/1.39  Simplification rules
% 2.05/1.39  ----------------------
% 2.05/1.39  #Subsume      : 5
% 2.05/1.39  #Demod        : 4
% 2.05/1.39  #Tautology    : 11
% 2.05/1.39  #SimpNegUnit  : 1
% 2.05/1.39  #BackRed      : 0
% 2.05/1.39  
% 2.05/1.39  #Partial instantiations: 0
% 2.05/1.39  #Strategies tried      : 1
% 2.05/1.39  
% 2.05/1.39  Timing (in seconds)
% 2.05/1.39  ----------------------
% 2.05/1.39  Preprocessing        : 0.33
% 2.05/1.39  Parsing              : 0.20
% 2.05/1.39  CNF conversion       : 0.02
% 2.05/1.39  Main loop            : 0.26
% 2.05/1.39  Inferencing          : 0.09
% 2.05/1.39  Reduction            : 0.08
% 2.05/1.39  Demodulation         : 0.07
% 2.05/1.39  BG Simplification    : 0.01
% 2.05/1.39  Subsumption          : 0.06
% 2.05/1.39  Abstraction          : 0.01
% 2.05/1.39  MUC search           : 0.00
% 2.05/1.39  Cooper               : 0.00
% 2.05/1.39  Total                : 0.63
% 2.05/1.39  Index Insertion      : 0.00
% 2.05/1.39  Index Deletion       : 0.00
% 2.05/1.39  Index Matching       : 0.00
% 2.05/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

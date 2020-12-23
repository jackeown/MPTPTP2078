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
% DateTime   : Thu Dec  3 09:42:30 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(A_14,C_15)
      | ~ r1_tarski(B_16,C_15)
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_18,A_19,B_20] :
      ( r1_tarski(A_18,k2_xboole_0(A_19,B_20))
      | ~ r1_tarski(A_18,A_19) ) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_89,plain,(
    ! [A_21,A_22,B_23] :
      ( r1_tarski(A_21,k2_xboole_0(A_22,B_23))
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_8,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_8])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:01:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.51  
% 2.07/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.52  %$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.07/1.52  
% 2.07/1.52  %Foreground sorts:
% 2.07/1.52  
% 2.07/1.52  
% 2.07/1.52  %Background operators:
% 2.07/1.52  
% 2.07/1.52  
% 2.07/1.52  %Foreground operators:
% 2.07/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.52  
% 2.07/1.53  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.07/1.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.07/1.53  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.07/1.53  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.07/1.53  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.07/1.53  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.53  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.53  tff(c_60, plain, (![A_14, C_15, B_16]: (r1_tarski(A_14, C_15) | ~r1_tarski(B_16, C_15) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.53  tff(c_75, plain, (![A_18, A_19, B_20]: (r1_tarski(A_18, k2_xboole_0(A_19, B_20)) | ~r1_tarski(A_18, A_19))), inference(resolution, [status(thm)], [c_6, c_60])).
% 2.07/1.53  tff(c_89, plain, (![A_21, A_22, B_23]: (r1_tarski(A_21, k2_xboole_0(A_22, B_23)) | ~r1_tarski(A_21, B_23))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 2.07/1.53  tff(c_8, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.07/1.53  tff(c_94, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_89, c_8])).
% 2.07/1.53  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_94])).
% 2.07/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.53  
% 2.07/1.53  Inference rules
% 2.07/1.53  ----------------------
% 2.07/1.53  #Ref     : 0
% 2.07/1.53  #Sup     : 24
% 2.07/1.53  #Fact    : 0
% 2.07/1.53  #Define  : 0
% 2.07/1.53  #Split   : 0
% 2.07/1.53  #Chain   : 0
% 2.07/1.53  #Close   : 0
% 2.07/1.53  
% 2.07/1.53  Ordering : KBO
% 2.07/1.53  
% 2.07/1.53  Simplification rules
% 2.07/1.53  ----------------------
% 2.07/1.53  #Subsume      : 0
% 2.07/1.53  #Demod        : 4
% 2.07/1.53  #Tautology    : 11
% 2.07/1.53  #SimpNegUnit  : 0
% 2.07/1.53  #BackRed      : 0
% 2.07/1.53  
% 2.07/1.53  #Partial instantiations: 0
% 2.07/1.53  #Strategies tried      : 1
% 2.07/1.53  
% 2.07/1.53  Timing (in seconds)
% 2.07/1.53  ----------------------
% 2.07/1.53  Preprocessing        : 0.40
% 2.07/1.53  Parsing              : 0.21
% 2.07/1.53  CNF conversion       : 0.02
% 2.07/1.54  Main loop            : 0.21
% 2.07/1.54  Inferencing          : 0.07
% 2.07/1.54  Reduction            : 0.07
% 2.07/1.54  Demodulation         : 0.07
% 2.07/1.54  BG Simplification    : 0.02
% 2.07/1.54  Subsumption          : 0.03
% 2.07/1.54  Abstraction          : 0.01
% 2.07/1.54  MUC search           : 0.00
% 2.07/1.54  Cooper               : 0.00
% 2.07/1.54  Total                : 0.65
% 2.07/1.54  Index Insertion      : 0.00
% 2.07/1.54  Index Deletion       : 0.00
% 2.07/1.54  Index Matching       : 0.00
% 2.07/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

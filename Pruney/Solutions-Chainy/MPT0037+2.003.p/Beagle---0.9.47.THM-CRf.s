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
% DateTime   : Thu Dec  3 09:42:41 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  15 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => k2_xboole_0(A,k3_xboole_0(C,B)) = k3_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_13,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_9])).

tff(c_18,plain,(
    ! [A_8,B_9,C_10] : k3_xboole_0(k2_xboole_0(A_8,B_9),k2_xboole_0(A_8,C_10)) = k2_xboole_0(A_8,k3_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [B_9] : k3_xboole_0(k2_xboole_0('#skF_1',B_9),'#skF_2') = k2_xboole_0('#skF_1',k3_xboole_0(B_9,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13,c_18])).

tff(c_6,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:31:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.10  
% 1.70/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.11  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.70/1.11  
% 1.70/1.11  %Foreground sorts:
% 1.70/1.11  
% 1.70/1.11  
% 1.70/1.11  %Background operators:
% 1.70/1.11  
% 1.70/1.11  
% 1.70/1.11  %Foreground operators:
% 1.70/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.11  
% 1.70/1.11  tff(f_36, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => (k2_xboole_0(A, k3_xboole_0(C, B)) = k3_xboole_0(k2_xboole_0(A, C), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_xboole_1)).
% 1.70/1.11  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.70/1.11  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 1.70/1.11  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.70/1.11  tff(c_9, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.11  tff(c_13, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_8, c_9])).
% 1.70/1.11  tff(c_18, plain, (![A_8, B_9, C_10]: (k3_xboole_0(k2_xboole_0(A_8, B_9), k2_xboole_0(A_8, C_10))=k2_xboole_0(A_8, k3_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.11  tff(c_30, plain, (![B_9]: (k3_xboole_0(k2_xboole_0('#skF_1', B_9), '#skF_2')=k2_xboole_0('#skF_1', k3_xboole_0(B_9, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_13, c_18])).
% 1.70/1.11  tff(c_6, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.70/1.11  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_6])).
% 1.70/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.11  
% 1.70/1.11  Inference rules
% 1.70/1.11  ----------------------
% 1.70/1.11  #Ref     : 0
% 1.70/1.11  #Sup     : 15
% 1.70/1.11  #Fact    : 0
% 1.70/1.11  #Define  : 0
% 1.70/1.11  #Split   : 0
% 1.70/1.11  #Chain   : 0
% 1.70/1.11  #Close   : 0
% 1.70/1.11  
% 1.70/1.11  Ordering : KBO
% 1.70/1.11  
% 1.70/1.11  Simplification rules
% 1.70/1.11  ----------------------
% 1.70/1.11  #Subsume      : 0
% 1.70/1.11  #Demod        : 1
% 1.70/1.11  #Tautology    : 8
% 1.70/1.11  #SimpNegUnit  : 0
% 1.70/1.11  #BackRed      : 1
% 1.70/1.11  
% 1.70/1.11  #Partial instantiations: 0
% 1.70/1.11  #Strategies tried      : 1
% 1.70/1.11  
% 1.70/1.11  Timing (in seconds)
% 1.70/1.11  ----------------------
% 1.70/1.12  Preprocessing        : 0.26
% 1.70/1.12  Parsing              : 0.14
% 1.70/1.12  CNF conversion       : 0.02
% 1.70/1.12  Main loop            : 0.09
% 1.70/1.12  Inferencing          : 0.04
% 1.70/1.12  Reduction            : 0.03
% 1.70/1.12  Demodulation         : 0.02
% 1.70/1.12  BG Simplification    : 0.01
% 1.70/1.12  Subsumption          : 0.01
% 1.70/1.12  Abstraction          : 0.01
% 1.70/1.12  MUC search           : 0.00
% 1.70/1.12  Cooper               : 0.00
% 1.70/1.12  Total                : 0.38
% 1.70/1.12  Index Insertion      : 0.00
% 1.70/1.12  Index Deletion       : 0.00
% 1.70/1.12  Index Matching       : 0.00
% 1.70/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

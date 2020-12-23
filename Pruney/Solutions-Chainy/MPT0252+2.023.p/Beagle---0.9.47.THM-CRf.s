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
% DateTime   : Thu Dec  3 09:51:04 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  33 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(c_14,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17,plain,(
    r1_tarski(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_78,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(k2_xboole_0(A_21,B_23),C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [B_24,C_25,A_26] :
      ( r1_tarski(B_24,C_25)
      | ~ r1_tarski(k2_xboole_0(A_26,B_24),C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_78])).

tff(c_105,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_17,c_92])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_228,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(k1_tarski(A_34),C_35)
      | ~ r1_tarski(k2_tarski(A_34,B_36),C_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_238,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_228])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_241,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_238,c_10])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.20  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.87/1.20  
% 1.87/1.20  %Foreground sorts:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Background operators:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Foreground operators:
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.20  
% 1.87/1.21  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.87/1.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.87/1.21  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.87/1.21  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.87/1.21  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 1.87/1.21  tff(c_14, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.87/1.21  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.21  tff(c_16, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.87/1.21  tff(c_17, plain, (r1_tarski(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.87/1.21  tff(c_78, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(k2_xboole_0(A_21, B_23), C_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.21  tff(c_92, plain, (![B_24, C_25, A_26]: (r1_tarski(B_24, C_25) | ~r1_tarski(k2_xboole_0(A_26, B_24), C_25))), inference(superposition, [status(thm), theory('equality')], [c_2, c_78])).
% 1.87/1.21  tff(c_105, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_17, c_92])).
% 1.87/1.21  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.21  tff(c_228, plain, (![A_34, C_35, B_36]: (r1_tarski(k1_tarski(A_34), C_35) | ~r1_tarski(k2_tarski(A_34, B_36), C_35))), inference(superposition, [status(thm), theory('equality')], [c_8, c_78])).
% 1.87/1.21  tff(c_238, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_105, c_228])).
% 1.87/1.21  tff(c_10, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.21  tff(c_241, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_238, c_10])).
% 1.87/1.21  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_241])).
% 1.87/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  Inference rules
% 1.87/1.21  ----------------------
% 1.87/1.21  #Ref     : 0
% 1.87/1.21  #Sup     : 59
% 1.87/1.21  #Fact    : 0
% 1.87/1.21  #Define  : 0
% 1.87/1.21  #Split   : 0
% 1.87/1.21  #Chain   : 0
% 1.87/1.21  #Close   : 0
% 1.87/1.21  
% 1.87/1.21  Ordering : KBO
% 1.87/1.21  
% 1.87/1.21  Simplification rules
% 1.87/1.21  ----------------------
% 1.87/1.21  #Subsume      : 4
% 1.87/1.21  #Demod        : 14
% 1.87/1.21  #Tautology    : 32
% 1.87/1.21  #SimpNegUnit  : 1
% 1.87/1.21  #BackRed      : 0
% 1.87/1.21  
% 1.87/1.21  #Partial instantiations: 0
% 1.87/1.21  #Strategies tried      : 1
% 1.87/1.21  
% 1.87/1.21  Timing (in seconds)
% 1.87/1.21  ----------------------
% 1.87/1.22  Preprocessing        : 0.26
% 1.87/1.22  Parsing              : 0.14
% 1.87/1.22  CNF conversion       : 0.02
% 1.87/1.22  Main loop            : 0.19
% 1.87/1.22  Inferencing          : 0.07
% 1.87/1.22  Reduction            : 0.08
% 1.87/1.22  Demodulation         : 0.07
% 1.87/1.22  BG Simplification    : 0.01
% 1.87/1.22  Subsumption          : 0.03
% 1.87/1.22  Abstraction          : 0.01
% 1.87/1.22  MUC search           : 0.00
% 1.87/1.22  Cooper               : 0.00
% 1.87/1.22  Total                : 0.48
% 1.87/1.22  Index Insertion      : 0.00
% 1.87/1.22  Index Deletion       : 0.00
% 1.87/1.22  Index Matching       : 0.00
% 1.87/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

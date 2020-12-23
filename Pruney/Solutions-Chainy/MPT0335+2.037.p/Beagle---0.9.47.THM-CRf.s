%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:58 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  47 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_16,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_271,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(k1_tarski(A_30),B_31) = k1_tarski(A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1178,plain,(
    ! [B_42,A_43] :
      ( k3_xboole_0(B_42,k1_tarski(A_43)) = k1_tarski(A_43)
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_2])).

tff(c_20,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_89])).

tff(c_116,plain,(
    ! [A_24,B_25,C_26] : k3_xboole_0(k3_xboole_0(A_24,B_25),C_26) = k3_xboole_0(A_24,k3_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    ! [C_27] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_27)) = k3_xboole_0('#skF_1',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_116])).

tff(c_182,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_162])).

tff(c_1214,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_182])).

tff(c_1269,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1214])).

tff(c_1271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.05/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/2.01  
% 4.05/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/2.02  %$ r2_hidden > r1_tarski > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.05/2.02  
% 4.05/2.02  %Foreground sorts:
% 4.05/2.02  
% 4.05/2.02  
% 4.05/2.02  %Background operators:
% 4.05/2.02  
% 4.05/2.02  
% 4.05/2.02  %Foreground operators:
% 4.05/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.05/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.05/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.05/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.05/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.05/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.05/2.02  tff('#skF_2', type, '#skF_2': $i).
% 4.05/2.02  tff('#skF_3', type, '#skF_3': $i).
% 4.05/2.02  tff('#skF_1', type, '#skF_1': $i).
% 4.05/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.05/2.02  tff('#skF_4', type, '#skF_4': $i).
% 4.05/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.05/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.05/2.02  
% 4.05/2.03  tff(f_50, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 4.05/2.03  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.05/2.03  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.05/2.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.05/2.03  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.05/2.03  tff(c_16, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.05/2.03  tff(c_18, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.05/2.03  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.05/2.03  tff(c_89, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/2.03  tff(c_271, plain, (![A_30, B_31]: (k3_xboole_0(k1_tarski(A_30), B_31)=k1_tarski(A_30) | ~r2_hidden(A_30, B_31))), inference(resolution, [status(thm)], [c_14, c_89])).
% 4.05/2.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.05/2.03  tff(c_1178, plain, (![B_42, A_43]: (k3_xboole_0(B_42, k1_tarski(A_43))=k1_tarski(A_43) | ~r2_hidden(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_271, c_2])).
% 4.05/2.03  tff(c_20, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.05/2.03  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.05/2.03  tff(c_97, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_89])).
% 4.05/2.03  tff(c_116, plain, (![A_24, B_25, C_26]: (k3_xboole_0(k3_xboole_0(A_24, B_25), C_26)=k3_xboole_0(A_24, k3_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.05/2.03  tff(c_162, plain, (![C_27]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_27))=k3_xboole_0('#skF_1', C_27))), inference(superposition, [status(thm), theory('equality')], [c_97, c_116])).
% 4.05/2.03  tff(c_182, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_162])).
% 4.05/2.03  tff(c_1214, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1178, c_182])).
% 4.05/2.03  tff(c_1269, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1214])).
% 4.05/2.03  tff(c_1271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_1269])).
% 4.05/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/2.03  
% 4.05/2.03  Inference rules
% 4.05/2.03  ----------------------
% 4.05/2.03  #Ref     : 0
% 4.05/2.03  #Sup     : 313
% 4.05/2.03  #Fact    : 0
% 4.05/2.03  #Define  : 0
% 4.05/2.03  #Split   : 0
% 4.05/2.03  #Chain   : 0
% 4.05/2.03  #Close   : 0
% 4.05/2.03  
% 4.05/2.03  Ordering : KBO
% 4.05/2.03  
% 4.05/2.03  Simplification rules
% 4.05/2.03  ----------------------
% 4.05/2.03  #Subsume      : 21
% 4.05/2.03  #Demod        : 196
% 4.05/2.03  #Tautology    : 131
% 4.05/2.03  #SimpNegUnit  : 1
% 4.05/2.03  #BackRed      : 1
% 4.05/2.03  
% 4.05/2.03  #Partial instantiations: 0
% 4.05/2.03  #Strategies tried      : 1
% 4.05/2.03  
% 4.05/2.03  Timing (in seconds)
% 4.05/2.03  ----------------------
% 4.05/2.04  Preprocessing        : 0.44
% 4.05/2.04  Parsing              : 0.23
% 4.05/2.04  CNF conversion       : 0.03
% 4.05/2.04  Main loop            : 0.75
% 4.05/2.04  Inferencing          : 0.23
% 4.05/2.04  Reduction            : 0.36
% 4.05/2.04  Demodulation         : 0.31
% 4.05/2.04  BG Simplification    : 0.03
% 4.05/2.04  Subsumption          : 0.09
% 4.05/2.04  Abstraction          : 0.04
% 4.05/2.04  MUC search           : 0.00
% 4.05/2.04  Cooper               : 0.00
% 4.05/2.04  Total                : 1.23
% 4.05/2.04  Index Insertion      : 0.00
% 4.05/2.04  Index Deletion       : 0.00
% 4.05/2.04  Index Matching       : 0.00
% 4.05/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------

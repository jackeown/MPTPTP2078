%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:50 EST 2020

% Result     : Theorem 10.81s
% Output     : CNFRefutation 10.81s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  49 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k4_xboole_0(A,B),C)
       => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_16])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [C_11,B_10,A_9] :
      ( r1_tarski(k4_xboole_0(C_11,B_10),k4_xboole_0(C_11,A_9))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_tarski(A_29,C_30)
      | ~ r1_tarski(B_31,C_30)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1616,plain,(
    ! [A_99,C_100,B_101,A_102] :
      ( r1_tarski(A_99,k2_xboole_0(C_100,B_101))
      | ~ r1_tarski(A_99,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_25319,plain,(
    ! [B_541,C_540,C_543,A_544,B_542] :
      ( r1_tarski(k4_xboole_0(C_543,B_542),k2_xboole_0(C_540,B_541))
      | ~ r1_tarski(k4_xboole_0(C_543,A_544),B_541)
      | ~ r1_tarski(A_544,B_542) ) ),
    inference(resolution,[status(thm)],[c_10,c_1616])).

tff(c_25597,plain,(
    ! [B_545,C_546] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_545),k2_xboole_0(C_546,'#skF_3'))
      | ~ r1_tarski('#skF_2',B_545) ) ),
    inference(resolution,[status(thm)],[c_18,c_25319])).

tff(c_191,plain,(
    ! [C_47,B_48,A_49] :
      ( r1_tarski(k4_xboole_0(C_47,B_48),k4_xboole_0(C_47,A_49))
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_231,plain,(
    ! [C_47,B_48] :
      ( k4_xboole_0(C_47,B_48) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_47,B_48),B_48) ) ),
    inference(resolution,[status(thm)],[c_191,c_12])).

tff(c_25850,plain,(
    ! [C_548] :
      ( k4_xboole_0('#skF_1',k2_xboole_0(C_548,'#skF_3')) = k1_xboole_0
      | ~ r1_tarski('#skF_2',k2_xboole_0(C_548,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_25597,c_231])).

tff(c_25913,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_25850])).

tff(c_25932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_25913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.81/4.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.81/4.58  
% 10.81/4.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.81/4.58  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.81/4.58  
% 10.81/4.58  %Foreground sorts:
% 10.81/4.58  
% 10.81/4.58  
% 10.81/4.58  %Background operators:
% 10.81/4.58  
% 10.81/4.58  
% 10.81/4.58  %Foreground operators:
% 10.81/4.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.81/4.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.81/4.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.81/4.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.81/4.58  tff('#skF_2', type, '#skF_2': $i).
% 10.81/4.58  tff('#skF_3', type, '#skF_3': $i).
% 10.81/4.58  tff('#skF_1', type, '#skF_1': $i).
% 10.81/4.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.81/4.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.81/4.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.81/4.58  
% 10.81/4.59  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.81/4.59  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 10.81/4.59  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.81/4.59  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 10.81/4.59  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 10.81/4.59  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.81/4.59  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 10.81/4.59  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | k4_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.81/4.59  tff(c_16, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.81/4.59  tff(c_24, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_16])).
% 10.81/4.59  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.81/4.59  tff(c_18, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.81/4.59  tff(c_10, plain, (![C_11, B_10, A_9]: (r1_tarski(k4_xboole_0(C_11, B_10), k4_xboole_0(C_11, A_9)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.81/4.59  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.81/4.59  tff(c_79, plain, (![A_29, C_30, B_31]: (r1_tarski(A_29, C_30) | ~r1_tarski(B_31, C_30) | ~r1_tarski(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.81/4.59  tff(c_1616, plain, (![A_99, C_100, B_101, A_102]: (r1_tarski(A_99, k2_xboole_0(C_100, B_101)) | ~r1_tarski(A_99, A_102) | ~r1_tarski(A_102, B_101))), inference(resolution, [status(thm)], [c_6, c_79])).
% 10.81/4.59  tff(c_25319, plain, (![B_541, C_540, C_543, A_544, B_542]: (r1_tarski(k4_xboole_0(C_543, B_542), k2_xboole_0(C_540, B_541)) | ~r1_tarski(k4_xboole_0(C_543, A_544), B_541) | ~r1_tarski(A_544, B_542))), inference(resolution, [status(thm)], [c_10, c_1616])).
% 10.81/4.59  tff(c_25597, plain, (![B_545, C_546]: (r1_tarski(k4_xboole_0('#skF_1', B_545), k2_xboole_0(C_546, '#skF_3')) | ~r1_tarski('#skF_2', B_545))), inference(resolution, [status(thm)], [c_18, c_25319])).
% 10.81/4.59  tff(c_191, plain, (![C_47, B_48, A_49]: (r1_tarski(k4_xboole_0(C_47, B_48), k4_xboole_0(C_47, A_49)) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.81/4.59  tff(c_12, plain, (![A_12, B_13]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k4_xboole_0(B_13, A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.81/4.59  tff(c_231, plain, (![C_47, B_48]: (k4_xboole_0(C_47, B_48)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_47, B_48), B_48))), inference(resolution, [status(thm)], [c_191, c_12])).
% 10.81/4.59  tff(c_25850, plain, (![C_548]: (k4_xboole_0('#skF_1', k2_xboole_0(C_548, '#skF_3'))=k1_xboole_0 | ~r1_tarski('#skF_2', k2_xboole_0(C_548, '#skF_3')))), inference(resolution, [status(thm)], [c_25597, c_231])).
% 10.81/4.59  tff(c_25913, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_25850])).
% 10.81/4.59  tff(c_25932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_25913])).
% 10.81/4.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.81/4.59  
% 10.81/4.59  Inference rules
% 10.81/4.59  ----------------------
% 10.81/4.59  #Ref     : 0
% 10.81/4.59  #Sup     : 6629
% 10.81/4.59  #Fact    : 0
% 10.81/4.59  #Define  : 0
% 10.81/4.59  #Split   : 7
% 10.81/4.59  #Chain   : 0
% 10.81/4.59  #Close   : 0
% 10.81/4.59  
% 10.81/4.59  Ordering : KBO
% 10.81/4.59  
% 10.81/4.59  Simplification rules
% 10.81/4.59  ----------------------
% 10.81/4.59  #Subsume      : 1529
% 10.81/4.59  #Demod        : 3170
% 10.81/4.59  #Tautology    : 3146
% 10.81/4.59  #SimpNegUnit  : 23
% 10.81/4.59  #BackRed      : 1
% 10.81/4.59  
% 10.81/4.59  #Partial instantiations: 0
% 10.81/4.59  #Strategies tried      : 1
% 10.81/4.59  
% 10.81/4.59  Timing (in seconds)
% 10.81/4.59  ----------------------
% 10.81/4.59  Preprocessing        : 0.29
% 10.81/4.59  Parsing              : 0.16
% 10.81/4.59  CNF conversion       : 0.02
% 10.81/4.59  Main loop            : 3.48
% 10.81/4.59  Inferencing          : 0.70
% 10.81/4.59  Reduction            : 1.19
% 10.81/4.59  Demodulation         : 0.89
% 10.81/4.59  BG Simplification    : 0.08
% 10.81/4.59  Subsumption          : 1.32
% 10.81/4.59  Abstraction          : 0.09
% 10.81/4.59  MUC search           : 0.00
% 10.81/4.59  Cooper               : 0.00
% 10.81/4.59  Total                : 3.79
% 10.81/4.59  Index Insertion      : 0.00
% 10.81/4.59  Index Deletion       : 0.00
% 10.81/4.59  Index Matching       : 0.00
% 10.81/4.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:59 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  43 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_16,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_132,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),k3_xboole_0(A_27,B_28))
      | r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_141,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(B_2,A_1))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_132])).

tff(c_14,plain,(
    r1_xboole_0(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_17,plain,(
    r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_18,plain,(
    ! [B_14,A_15] :
      ( r1_xboole_0(B_14,A_15)
      | ~ r1_xboole_0(A_15,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_17,c_18])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,k3_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_74])).

tff(c_102,plain,(
    ! [A_25,B_26] : k3_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_334,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,k3_xboole_0(A_43,B_44))
      | ~ r2_hidden(C_45,k3_xboole_0(A_43,B_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_351,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_21,c_334])).

tff(c_355,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_351])).

tff(c_363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.98/1.23  
% 1.98/1.23  %Foreground sorts:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Background operators:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Foreground operators:
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.23  
% 1.98/1.24  tff(f_56, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 1.98/1.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.98/1.24  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.98/1.24  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.98/1.24  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.98/1.24  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.98/1.24  tff(c_16, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.24  tff(c_132, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), k3_xboole_0(A_27, B_28)) | r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.24  tff(c_141, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(B_2, A_1)) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_132])).
% 1.98/1.24  tff(c_14, plain, (r1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.24  tff(c_17, plain, (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 1.98/1.24  tff(c_18, plain, (![B_14, A_15]: (r1_xboole_0(B_14, A_15) | ~r1_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.24  tff(c_21, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_17, c_18])).
% 1.98/1.24  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.24  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.24  tff(c_74, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.24  tff(c_89, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, k3_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_74])).
% 1.98/1.24  tff(c_102, plain, (![A_25, B_26]: (k3_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89])).
% 1.98/1.24  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.24  tff(c_334, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, k3_xboole_0(A_43, B_44)) | ~r2_hidden(C_45, k3_xboole_0(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 1.98/1.24  tff(c_351, plain, (![C_46]: (~r2_hidden(C_46, k3_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_21, c_334])).
% 1.98/1.24  tff(c_355, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_141, c_351])).
% 1.98/1.24  tff(c_363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_355])).
% 1.98/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  Inference rules
% 1.98/1.24  ----------------------
% 1.98/1.24  #Ref     : 0
% 1.98/1.24  #Sup     : 90
% 1.98/1.24  #Fact    : 0
% 1.98/1.24  #Define  : 0
% 1.98/1.24  #Split   : 0
% 1.98/1.24  #Chain   : 0
% 1.98/1.24  #Close   : 0
% 1.98/1.24  
% 1.98/1.24  Ordering : KBO
% 1.98/1.24  
% 1.98/1.24  Simplification rules
% 1.98/1.24  ----------------------
% 1.98/1.24  #Subsume      : 15
% 1.98/1.24  #Demod        : 48
% 1.98/1.24  #Tautology    : 43
% 1.98/1.24  #SimpNegUnit  : 1
% 1.98/1.24  #BackRed      : 0
% 1.98/1.24  
% 1.98/1.24  #Partial instantiations: 0
% 1.98/1.24  #Strategies tried      : 1
% 1.98/1.24  
% 1.98/1.24  Timing (in seconds)
% 1.98/1.24  ----------------------
% 1.98/1.24  Preprocessing        : 0.26
% 1.98/1.24  Parsing              : 0.14
% 1.98/1.24  CNF conversion       : 0.02
% 1.98/1.24  Main loop            : 0.22
% 1.98/1.24  Inferencing          : 0.08
% 1.98/1.24  Reduction            : 0.09
% 1.98/1.24  Demodulation         : 0.08
% 1.98/1.24  BG Simplification    : 0.01
% 1.98/1.24  Subsumption          : 0.03
% 1.98/1.24  Abstraction          : 0.01
% 1.98/1.24  MUC search           : 0.00
% 1.98/1.24  Cooper               : 0.00
% 1.98/1.24  Total                : 0.50
% 1.98/1.24  Index Insertion      : 0.00
% 1.98/1.24  Index Deletion       : 0.00
% 1.98/1.24  Index Matching       : 0.00
% 1.98/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

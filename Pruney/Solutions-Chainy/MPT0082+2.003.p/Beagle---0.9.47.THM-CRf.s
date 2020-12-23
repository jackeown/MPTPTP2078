%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:59 EST 2020

% Result     : Theorem 8.51s
% Output     : CNFRefutation 8.51s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  39 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_65,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_69,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_22])).

tff(c_20,plain,(
    r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_123,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_xboole_0(A_11,B_12)
      | ~ r1_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_177,plain,(
    ! [A_32,A_33,B_34] :
      ( r1_xboole_0(A_32,k3_xboole_0(A_33,B_34))
      | ~ r1_xboole_0(A_32,A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_18])).

tff(c_367,plain,(
    ! [A_48,B_49,A_50] :
      ( r1_xboole_0(A_48,k3_xboole_0(B_49,A_50))
      | ~ r1_xboole_0(A_48,A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10383,plain,(
    ! [A_210,B_211,A_212] :
      ( k3_xboole_0(A_210,k3_xboole_0(B_211,A_212)) = k1_xboole_0
      | ~ r1_xboole_0(A_210,A_212) ) ),
    inference(resolution,[status(thm)],[c_367,c_4])).

tff(c_12522,plain,(
    ! [B_229,A_230] :
      ( k3_xboole_0(B_229,A_230) = k1_xboole_0
      | ~ r1_xboole_0(k3_xboole_0(B_229,A_230),A_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_10383])).

tff(c_12706,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_12522])).

tff(c_12761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_12706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.51/3.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.02  
% 8.51/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.02  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 8.51/3.02  
% 8.51/3.02  %Foreground sorts:
% 8.51/3.02  
% 8.51/3.02  
% 8.51/3.02  %Background operators:
% 8.51/3.02  
% 8.51/3.02  
% 8.51/3.02  %Foreground operators:
% 8.51/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.51/3.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.51/3.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.51/3.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.51/3.02  tff('#skF_2', type, '#skF_2': $i).
% 8.51/3.02  tff('#skF_1', type, '#skF_1': $i).
% 8.51/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.51/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.51/3.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.51/3.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.51/3.02  
% 8.51/3.03  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.51/3.03  tff(f_60, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 8.51/3.03  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.51/3.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.51/3.03  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.51/3.03  tff(f_53, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.51/3.03  tff(c_65, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.51/3.03  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.51/3.03  tff(c_69, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_22])).
% 8.51/3.03  tff(c_20, plain, (r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.51/3.03  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.51/3.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.51/3.03  tff(c_123, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.51/3.03  tff(c_18, plain, (![A_11, B_12, C_13]: (r1_xboole_0(A_11, B_12) | ~r1_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.51/3.03  tff(c_177, plain, (![A_32, A_33, B_34]: (r1_xboole_0(A_32, k3_xboole_0(A_33, B_34)) | ~r1_xboole_0(A_32, A_33))), inference(superposition, [status(thm), theory('equality')], [c_123, c_18])).
% 8.51/3.03  tff(c_367, plain, (![A_48, B_49, A_50]: (r1_xboole_0(A_48, k3_xboole_0(B_49, A_50)) | ~r1_xboole_0(A_48, A_50))), inference(superposition, [status(thm), theory('equality')], [c_2, c_177])).
% 8.51/3.03  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.51/3.03  tff(c_10383, plain, (![A_210, B_211, A_212]: (k3_xboole_0(A_210, k3_xboole_0(B_211, A_212))=k1_xboole_0 | ~r1_xboole_0(A_210, A_212))), inference(resolution, [status(thm)], [c_367, c_4])).
% 8.51/3.03  tff(c_12522, plain, (![B_229, A_230]: (k3_xboole_0(B_229, A_230)=k1_xboole_0 | ~r1_xboole_0(k3_xboole_0(B_229, A_230), A_230))), inference(superposition, [status(thm), theory('equality')], [c_8, c_10383])).
% 8.51/3.03  tff(c_12706, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_12522])).
% 8.51/3.03  tff(c_12761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_12706])).
% 8.51/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.03  
% 8.51/3.03  Inference rules
% 8.51/3.03  ----------------------
% 8.51/3.03  #Ref     : 1
% 8.51/3.03  #Sup     : 3237
% 8.51/3.03  #Fact    : 0
% 8.51/3.03  #Define  : 0
% 8.51/3.03  #Split   : 6
% 8.51/3.03  #Chain   : 0
% 8.51/3.03  #Close   : 0
% 8.51/3.03  
% 8.51/3.03  Ordering : KBO
% 8.51/3.03  
% 8.51/3.03  Simplification rules
% 8.51/3.03  ----------------------
% 8.51/3.03  #Subsume      : 1145
% 8.51/3.03  #Demod        : 1381
% 8.51/3.03  #Tautology    : 1066
% 8.51/3.03  #SimpNegUnit  : 18
% 8.51/3.03  #BackRed      : 5
% 8.51/3.03  
% 8.51/3.03  #Partial instantiations: 0
% 8.51/3.03  #Strategies tried      : 1
% 8.51/3.03  
% 8.51/3.03  Timing (in seconds)
% 8.51/3.03  ----------------------
% 8.51/3.03  Preprocessing        : 0.32
% 8.51/3.03  Parsing              : 0.18
% 8.51/3.03  CNF conversion       : 0.02
% 8.51/3.03  Main loop            : 1.92
% 8.51/3.03  Inferencing          : 0.50
% 8.51/3.03  Reduction            : 0.79
% 8.51/3.03  Demodulation         : 0.63
% 8.51/3.03  BG Simplification    : 0.05
% 8.51/3.03  Subsumption          : 0.47
% 8.51/3.03  Abstraction          : 0.06
% 8.51/3.03  MUC search           : 0.00
% 8.51/3.03  Cooper               : 0.00
% 8.51/3.03  Total                : 2.26
% 8.51/3.03  Index Insertion      : 0.00
% 8.51/3.03  Index Deletion       : 0.00
% 8.51/3.03  Index Matching       : 0.00
% 8.51/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------

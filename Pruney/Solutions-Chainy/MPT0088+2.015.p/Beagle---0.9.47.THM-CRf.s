%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:21 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_12,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [B_17,A_18,C_19] : k4_xboole_0(k3_xboole_0(B_17,A_18),C_19) = k3_xboole_0(A_18,k4_xboole_0(B_17,C_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k3_xboole_0(A_5,B_6),C_7) = k3_xboole_0(A_5,k4_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [B_17,A_18,C_19] : k3_xboole_0(B_17,k4_xboole_0(A_18,C_19)) = k3_xboole_0(A_18,k4_xboole_0(B_17,C_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8])).

tff(c_46,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_10])).

tff(c_151,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_50])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.13  
% 1.71/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.14  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.71/1.14  
% 1.71/1.14  %Foreground sorts:
% 1.71/1.14  
% 1.71/1.14  
% 1.71/1.14  %Background operators:
% 1.71/1.14  
% 1.71/1.14  
% 1.71/1.14  %Foreground operators:
% 1.71/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.14  
% 1.71/1.15  tff(f_38, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 1.71/1.15  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.71/1.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.71/1.15  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.71/1.15  tff(c_12, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.71/1.15  tff(c_51, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.15  tff(c_59, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_51])).
% 1.71/1.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.15  tff(c_64, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.15  tff(c_82, plain, (![B_17, A_18, C_19]: (k4_xboole_0(k3_xboole_0(B_17, A_18), C_19)=k3_xboole_0(A_18, k4_xboole_0(B_17, C_19)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 1.71/1.15  tff(c_8, plain, (![A_5, B_6, C_7]: (k4_xboole_0(k3_xboole_0(A_5, B_6), C_7)=k3_xboole_0(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.15  tff(c_88, plain, (![B_17, A_18, C_19]: (k3_xboole_0(B_17, k4_xboole_0(A_18, C_19))=k3_xboole_0(A_18, k4_xboole_0(B_17, C_19)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8])).
% 1.71/1.15  tff(c_46, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.15  tff(c_10, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.71/1.15  tff(c_50, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_10])).
% 1.71/1.15  tff(c_151, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_88, c_50])).
% 1.71/1.15  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_151])).
% 1.71/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.15  
% 1.71/1.15  Inference rules
% 1.71/1.15  ----------------------
% 1.71/1.15  #Ref     : 0
% 1.71/1.15  #Sup     : 37
% 1.71/1.15  #Fact    : 0
% 1.71/1.15  #Define  : 0
% 1.71/1.15  #Split   : 0
% 1.71/1.15  #Chain   : 0
% 1.71/1.15  #Close   : 0
% 1.71/1.15  
% 1.71/1.15  Ordering : KBO
% 1.71/1.15  
% 1.71/1.15  Simplification rules
% 1.71/1.15  ----------------------
% 1.71/1.15  #Subsume      : 0
% 1.71/1.15  #Demod        : 5
% 1.71/1.15  #Tautology    : 22
% 1.71/1.15  #SimpNegUnit  : 0
% 1.71/1.15  #BackRed      : 1
% 1.71/1.15  
% 1.71/1.15  #Partial instantiations: 0
% 1.71/1.15  #Strategies tried      : 1
% 1.71/1.15  
% 1.71/1.15  Timing (in seconds)
% 1.71/1.15  ----------------------
% 1.71/1.15  Preprocessing        : 0.27
% 1.71/1.15  Parsing              : 0.14
% 1.71/1.15  CNF conversion       : 0.01
% 1.71/1.15  Main loop            : 0.15
% 1.71/1.15  Inferencing          : 0.06
% 1.71/1.15  Reduction            : 0.06
% 1.71/1.15  Demodulation         : 0.05
% 1.71/1.15  BG Simplification    : 0.01
% 1.71/1.15  Subsumption          : 0.02
% 1.71/1.15  Abstraction          : 0.01
% 1.71/1.15  MUC search           : 0.00
% 1.71/1.15  Cooper               : 0.00
% 1.71/1.15  Total                : 0.45
% 1.71/1.15  Index Insertion      : 0.00
% 1.71/1.15  Index Deletion       : 0.00
% 1.71/1.15  Index Matching       : 0.00
% 1.71/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

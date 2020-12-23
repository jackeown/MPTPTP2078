%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:08 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [A_24,B_25,C_26] : k4_xboole_0(k3_xboole_0(A_24,B_25),C_26) = k3_xboole_0(A_24,k4_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    ! [A_5,B_6] : k4_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_29])).

tff(c_70,plain,(
    ! [C_29,B_30] : k3_xboole_0(C_29,k4_xboole_0(B_30,C_29)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_37])).

tff(c_89,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),k5_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_16])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:12:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.23  
% 1.84/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.23  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.84/1.23  
% 1.84/1.23  %Foreground sorts:
% 1.84/1.23  
% 1.84/1.23  
% 1.84/1.23  %Background operators:
% 1.84/1.23  
% 1.84/1.23  
% 1.84/1.23  %Foreground operators:
% 1.84/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.84/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.23  
% 1.92/1.24  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 1.92/1.24  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.92/1.24  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.92/1.24  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.92/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.92/1.24  tff(f_42, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_xboole_1)).
% 1.92/1.24  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.24  tff(c_45, plain, (![A_24, B_25, C_26]: (k4_xboole_0(k3_xboole_0(A_24, B_25), C_26)=k3_xboole_0(A_24, k4_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.24  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.24  tff(c_29, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.24  tff(c_37, plain, (![A_5, B_6]: (k4_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_29])).
% 1.92/1.24  tff(c_70, plain, (![C_29, B_30]: (k3_xboole_0(C_29, k4_xboole_0(B_30, C_29))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_45, c_37])).
% 1.92/1.24  tff(c_89, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), k5_xboole_0(A_3, B_4))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_70])).
% 1.92/1.24  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.24  tff(c_16, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.24  tff(c_22, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_16])).
% 1.92/1.24  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_22])).
% 1.92/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.24  
% 1.92/1.24  Inference rules
% 1.92/1.24  ----------------------
% 1.92/1.24  #Ref     : 0
% 1.92/1.24  #Sup     : 42
% 1.92/1.24  #Fact    : 0
% 1.92/1.24  #Define  : 0
% 1.92/1.24  #Split   : 0
% 1.92/1.24  #Chain   : 0
% 1.92/1.24  #Close   : 0
% 1.92/1.24  
% 1.92/1.24  Ordering : KBO
% 1.92/1.24  
% 1.92/1.24  Simplification rules
% 1.92/1.24  ----------------------
% 1.92/1.24  #Subsume      : 0
% 1.92/1.24  #Demod        : 18
% 1.92/1.24  #Tautology    : 27
% 1.92/1.24  #SimpNegUnit  : 0
% 1.92/1.24  #BackRed      : 1
% 1.92/1.24  
% 1.92/1.24  #Partial instantiations: 0
% 1.92/1.24  #Strategies tried      : 1
% 1.92/1.24  
% 1.92/1.24  Timing (in seconds)
% 1.92/1.24  ----------------------
% 1.92/1.25  Preprocessing        : 0.31
% 1.92/1.25  Parsing              : 0.16
% 1.92/1.25  CNF conversion       : 0.02
% 1.92/1.25  Main loop            : 0.14
% 1.92/1.25  Inferencing          : 0.06
% 1.92/1.25  Reduction            : 0.04
% 1.92/1.25  Demodulation         : 0.03
% 1.92/1.25  BG Simplification    : 0.01
% 1.92/1.25  Subsumption          : 0.02
% 1.92/1.25  Abstraction          : 0.01
% 1.92/1.25  MUC search           : 0.00
% 1.92/1.25  Cooper               : 0.00
% 1.92/1.25  Total                : 0.48
% 1.92/1.25  Index Insertion      : 0.00
% 1.92/1.25  Index Deletion       : 0.00
% 1.92/1.25  Index Matching       : 0.00
% 1.92/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

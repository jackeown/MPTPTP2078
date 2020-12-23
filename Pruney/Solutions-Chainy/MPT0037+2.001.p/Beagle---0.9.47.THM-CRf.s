%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:41 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :   16 (  21 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => k2_xboole_0(A,k3_xboole_0(C,B)) = k3_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_124,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_124])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_8])).

tff(c_148,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k3_xboole_0(A_22,B_23),k3_xboole_0(A_22,C_24)) = k3_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_261,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k3_xboole_0(A_26,B_27),k3_xboole_0(B_27,C_28)) = k3_xboole_0(B_27,k2_xboole_0(A_26,C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_148])).

tff(c_290,plain,(
    ! [C_28] : k3_xboole_0('#skF_2',k2_xboole_0('#skF_1',C_28)) = k2_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_261])).

tff(c_12,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_1798,plain,(
    k2_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_15])).

tff(c_1801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.53  
% 3.41/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.53  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.41/1.53  
% 3.41/1.53  %Foreground sorts:
% 3.41/1.53  
% 3.41/1.53  
% 3.41/1.53  %Background operators:
% 3.41/1.53  
% 3.41/1.53  
% 3.41/1.53  %Foreground operators:
% 3.41/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.41/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.41/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.41/1.53  
% 3.53/1.54  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.53/1.54  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => (k2_xboole_0(A, k3_xboole_0(C, B)) = k3_xboole_0(k2_xboole_0(A, C), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_xboole_1)).
% 3.53/1.54  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.53/1.54  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.53/1.54  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 3.53/1.54  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.53/1.54  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.53/1.54  tff(c_124, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.53/1.54  tff(c_128, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_124])).
% 3.53/1.54  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.54  tff(c_135, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_128, c_8])).
% 3.53/1.54  tff(c_148, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k3_xboole_0(A_22, B_23), k3_xboole_0(A_22, C_24))=k3_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.54  tff(c_261, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k3_xboole_0(B_27, C_28))=k3_xboole_0(B_27, k2_xboole_0(A_26, C_28)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_148])).
% 3.53/1.54  tff(c_290, plain, (![C_28]: (k3_xboole_0('#skF_2', k2_xboole_0('#skF_1', C_28))=k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_28)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_261])).
% 3.53/1.54  tff(c_12, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.53/1.54  tff(c_15, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_3'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 3.53/1.54  tff(c_1798, plain, (k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_15])).
% 3.53/1.54  tff(c_1801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_1798])).
% 3.53/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.54  
% 3.53/1.54  Inference rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Ref     : 0
% 3.53/1.54  #Sup     : 455
% 3.53/1.54  #Fact    : 0
% 3.53/1.54  #Define  : 0
% 3.53/1.54  #Split   : 0
% 3.53/1.54  #Chain   : 0
% 3.53/1.54  #Close   : 0
% 3.53/1.54  
% 3.53/1.54  Ordering : KBO
% 3.53/1.54  
% 3.53/1.54  Simplification rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Subsume      : 8
% 3.53/1.54  #Demod        : 328
% 3.53/1.54  #Tautology    : 266
% 3.53/1.54  #SimpNegUnit  : 0
% 3.53/1.54  #BackRed      : 5
% 3.53/1.54  
% 3.53/1.54  #Partial instantiations: 0
% 3.53/1.54  #Strategies tried      : 1
% 3.53/1.54  
% 3.53/1.54  Timing (in seconds)
% 3.53/1.54  ----------------------
% 3.53/1.54  Preprocessing        : 0.27
% 3.53/1.54  Parsing              : 0.14
% 3.53/1.54  CNF conversion       : 0.02
% 3.53/1.54  Main loop            : 0.52
% 3.53/1.54  Inferencing          : 0.17
% 3.53/1.54  Reduction            : 0.23
% 3.53/1.54  Demodulation         : 0.19
% 3.53/1.54  BG Simplification    : 0.02
% 3.53/1.54  Subsumption          : 0.07
% 3.53/1.54  Abstraction          : 0.03
% 3.53/1.54  MUC search           : 0.00
% 3.53/1.54  Cooper               : 0.00
% 3.53/1.54  Total                : 0.81
% 3.53/1.54  Index Insertion      : 0.00
% 3.53/1.54  Index Deletion       : 0.00
% 3.53/1.54  Index Matching       : 0.00
% 3.53/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

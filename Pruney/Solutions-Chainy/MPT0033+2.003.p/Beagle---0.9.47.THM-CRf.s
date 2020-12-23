%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:37 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  30 expanded)
%              Number of equality atoms :   12 (  15 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_83,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_83])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_10])).

tff(c_306,plain,(
    ! [A_33,B_34,C_35] : k3_xboole_0(k3_xboole_0(A_33,B_34),C_35) = k3_xboole_0(A_33,k3_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_684,plain,(
    ! [C_46] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_46)) = k3_xboole_0('#skF_1',C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_306])).

tff(c_17,plain,(
    ! [B_14,A_15] : k3_xboole_0(B_14,A_15) = k3_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [B_14,A_15] : r1_tarski(k3_xboole_0(B_14,A_15),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_8])).

tff(c_1904,plain,(
    ! [C_66] : r1_tarski(k3_xboole_0('#skF_1',C_66),k3_xboole_0('#skF_2',C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_32])).

tff(c_1962,plain,(
    ! [B_2] : r1_tarski(k3_xboole_0('#skF_1',B_2),k3_xboole_0(B_2,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1904])).

tff(c_12,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_2252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1962,c_15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.64  
% 3.82/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.64  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.82/1.64  
% 3.82/1.64  %Foreground sorts:
% 3.82/1.64  
% 3.82/1.64  
% 3.82/1.64  %Background operators:
% 3.82/1.64  
% 3.82/1.64  
% 3.82/1.64  %Foreground operators:
% 3.82/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.82/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.82/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.82/1.64  
% 3.82/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.82/1.65  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_xboole_1)).
% 3.82/1.65  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.82/1.65  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.82/1.65  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.82/1.65  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.82/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.82/1.65  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.82/1.65  tff(c_83, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.65  tff(c_103, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_83])).
% 3.82/1.65  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/1.65  tff(c_110, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_103, c_10])).
% 3.82/1.65  tff(c_306, plain, (![A_33, B_34, C_35]: (k3_xboole_0(k3_xboole_0(A_33, B_34), C_35)=k3_xboole_0(A_33, k3_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.65  tff(c_684, plain, (![C_46]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_46))=k3_xboole_0('#skF_1', C_46))), inference(superposition, [status(thm), theory('equality')], [c_110, c_306])).
% 3.82/1.65  tff(c_17, plain, (![B_14, A_15]: (k3_xboole_0(B_14, A_15)=k3_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.82/1.65  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.82/1.65  tff(c_32, plain, (![B_14, A_15]: (r1_tarski(k3_xboole_0(B_14, A_15), A_15))), inference(superposition, [status(thm), theory('equality')], [c_17, c_8])).
% 3.82/1.65  tff(c_1904, plain, (![C_66]: (r1_tarski(k3_xboole_0('#skF_1', C_66), k3_xboole_0('#skF_2', C_66)))), inference(superposition, [status(thm), theory('equality')], [c_684, c_32])).
% 3.82/1.65  tff(c_1962, plain, (![B_2]: (r1_tarski(k3_xboole_0('#skF_1', B_2), k3_xboole_0(B_2, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1904])).
% 3.82/1.65  tff(c_12, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.82/1.65  tff(c_15, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 3.82/1.65  tff(c_2252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1962, c_15])).
% 3.82/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.65  
% 3.82/1.65  Inference rules
% 3.82/1.65  ----------------------
% 3.82/1.65  #Ref     : 0
% 3.82/1.65  #Sup     : 572
% 3.82/1.65  #Fact    : 0
% 3.82/1.65  #Define  : 0
% 3.82/1.65  #Split   : 0
% 3.82/1.65  #Chain   : 0
% 3.82/1.65  #Close   : 0
% 3.82/1.65  
% 3.82/1.65  Ordering : KBO
% 3.82/1.65  
% 3.82/1.65  Simplification rules
% 3.82/1.65  ----------------------
% 3.82/1.65  #Subsume      : 12
% 3.82/1.65  #Demod        : 360
% 3.82/1.65  #Tautology    : 282
% 3.82/1.65  #SimpNegUnit  : 0
% 3.82/1.65  #BackRed      : 1
% 3.82/1.65  
% 3.82/1.65  #Partial instantiations: 0
% 3.82/1.65  #Strategies tried      : 1
% 3.82/1.65  
% 3.82/1.65  Timing (in seconds)
% 3.82/1.65  ----------------------
% 3.82/1.65  Preprocessing        : 0.25
% 3.82/1.65  Parsing              : 0.14
% 3.82/1.66  CNF conversion       : 0.01
% 3.82/1.66  Main loop            : 0.65
% 3.82/1.66  Inferencing          : 0.18
% 3.82/1.66  Reduction            : 0.32
% 3.82/1.66  Demodulation         : 0.27
% 3.82/1.66  BG Simplification    : 0.02
% 3.82/1.66  Subsumption          : 0.09
% 3.82/1.66  Abstraction          : 0.04
% 3.82/1.66  MUC search           : 0.00
% 3.82/1.66  Cooper               : 0.00
% 3.82/1.66  Total                : 0.92
% 3.82/1.66  Index Insertion      : 0.00
% 3.82/1.66  Index Deletion       : 0.00
% 3.82/1.66  Index Matching       : 0.00
% 3.82/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------

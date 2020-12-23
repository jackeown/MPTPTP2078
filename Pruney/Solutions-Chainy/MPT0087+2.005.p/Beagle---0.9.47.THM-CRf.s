%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:17 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  40 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_16,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_292,plain,(
    ! [A_40,B_41] : k2_xboole_0(A_40,k4_xboole_0(B_41,A_40)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_312,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),k4_xboole_0(A_8,B_9)) = k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_292])).

tff(c_321,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_312])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_124,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_124])).

tff(c_150,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_411,plain,(
    ! [A_46,B_47,C_48] : k2_xboole_0(k4_xboole_0(A_46,B_47),k3_xboole_0(A_46,C_48)) = k4_xboole_0(A_46,k4_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1954,plain,(
    ! [A_79,C_80,B_81] : k2_xboole_0(k3_xboole_0(A_79,C_80),k4_xboole_0(A_79,B_81)) = k4_xboole_0(A_79,k4_xboole_0(B_81,C_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_411])).

tff(c_2029,plain,(
    ! [C_80] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_80)) = k2_xboole_0(k3_xboole_0('#skF_1',C_80),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_1954])).

tff(c_2079,plain,(
    ! [C_82] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_82)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_2,c_2029])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2145,plain,(
    ! [C_82] : r1_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2079,c_20])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.49  
% 3.02/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.50  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.02/1.50  
% 3.02/1.50  %Foreground sorts:
% 3.02/1.50  
% 3.02/1.50  
% 3.02/1.50  %Background operators:
% 3.02/1.50  
% 3.02/1.50  
% 3.02/1.50  %Foreground operators:
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.50  
% 3.02/1.51  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.02/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.02/1.51  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.02/1.51  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.02/1.51  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.02/1.51  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 3.02/1.51  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.02/1.51  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.02/1.51  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.02/1.51  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.51  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.51  tff(c_292, plain, (![A_40, B_41]: (k2_xboole_0(A_40, k4_xboole_0(B_41, A_40))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.51  tff(c_312, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k4_xboole_0(A_8, B_9))=k2_xboole_0(k3_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_292])).
% 3.02/1.51  tff(c_321, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_312])).
% 3.02/1.51  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.51  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.02/1.51  tff(c_77, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.51  tff(c_93, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_77])).
% 3.02/1.51  tff(c_124, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.51  tff(c_145, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_124])).
% 3.02/1.51  tff(c_150, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_145])).
% 3.02/1.51  tff(c_411, plain, (![A_46, B_47, C_48]: (k2_xboole_0(k4_xboole_0(A_46, B_47), k3_xboole_0(A_46, C_48))=k4_xboole_0(A_46, k4_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.51  tff(c_1954, plain, (![A_79, C_80, B_81]: (k2_xboole_0(k3_xboole_0(A_79, C_80), k4_xboole_0(A_79, B_81))=k4_xboole_0(A_79, k4_xboole_0(B_81, C_80)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_411])).
% 3.02/1.51  tff(c_2029, plain, (![C_80]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_80))=k2_xboole_0(k3_xboole_0('#skF_1', C_80), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_1954])).
% 3.02/1.51  tff(c_2079, plain, (![C_82]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_82))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_2, c_2029])).
% 3.02/1.51  tff(c_20, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.02/1.51  tff(c_2145, plain, (![C_82]: (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_82)))), inference(superposition, [status(thm), theory('equality')], [c_2079, c_20])).
% 3.02/1.51  tff(c_22, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.02/1.51  tff(c_2185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2145, c_22])).
% 3.02/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.51  
% 3.02/1.51  Inference rules
% 3.02/1.51  ----------------------
% 3.02/1.51  #Ref     : 0
% 3.02/1.51  #Sup     : 523
% 3.02/1.51  #Fact    : 0
% 3.02/1.51  #Define  : 0
% 3.02/1.51  #Split   : 0
% 3.02/1.51  #Chain   : 0
% 3.02/1.51  #Close   : 0
% 3.02/1.51  
% 3.02/1.51  Ordering : KBO
% 3.02/1.51  
% 3.02/1.51  Simplification rules
% 3.02/1.51  ----------------------
% 3.02/1.51  #Subsume      : 0
% 3.02/1.51  #Demod        : 646
% 3.02/1.51  #Tautology    : 421
% 3.02/1.51  #SimpNegUnit  : 0
% 3.02/1.51  #BackRed      : 1
% 3.02/1.51  
% 3.02/1.51  #Partial instantiations: 0
% 3.02/1.51  #Strategies tried      : 1
% 3.02/1.51  
% 3.02/1.51  Timing (in seconds)
% 3.02/1.51  ----------------------
% 3.02/1.51  Preprocessing        : 0.26
% 3.02/1.51  Parsing              : 0.15
% 3.02/1.51  CNF conversion       : 0.01
% 3.02/1.51  Main loop            : 0.48
% 3.02/1.51  Inferencing          : 0.16
% 3.02/1.51  Reduction            : 0.22
% 3.02/1.51  Demodulation         : 0.18
% 3.02/1.51  BG Simplification    : 0.02
% 3.02/1.51  Subsumption          : 0.06
% 3.02/1.51  Abstraction          : 0.03
% 3.02/1.51  MUC search           : 0.00
% 3.02/1.51  Cooper               : 0.00
% 3.02/1.51  Total                : 0.77
% 3.02/1.51  Index Insertion      : 0.00
% 3.02/1.51  Index Deletion       : 0.00
% 3.02/1.51  Index Matching       : 0.00
% 3.02/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

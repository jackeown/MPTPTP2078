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
% DateTime   : Thu Dec  3 09:44:12 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   30 (  38 expanded)
%              Number of equality atoms :   25 (  32 expanded)
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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [B_14,A_15] : k2_xboole_0(B_14,A_15) = k2_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_8])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_145,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_145])).

tff(c_177,plain,(
    ! [A_25,B_26,C_27] : k4_xboole_0(k4_xboole_0(A_25,B_26),C_27) = k4_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_203,plain,(
    ! [C_27] : k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),C_27) = k4_xboole_0('#skF_1',k2_xboole_0(k1_xboole_0,C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_177])).

tff(c_257,plain,(
    ! [C_30] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_30)) = k4_xboole_0('#skF_1',C_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45,c_203])).

tff(c_317,plain,(
    ! [B_32] : k4_xboole_0('#skF_1',k2_xboole_0(B_32,'#skF_2')) = k4_xboole_0('#skF_1',B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_257])).

tff(c_330,plain,(
    ! [B_32] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',B_32)) = k3_xboole_0('#skF_1',k2_xboole_0(B_32,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_14])).

tff(c_353,plain,(
    ! [B_32] : k3_xboole_0('#skF_1',k2_xboole_0(B_32,'#skF_2')) = k3_xboole_0('#skF_1',B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_330])).

tff(c_16,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:31:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.27  
% 1.92/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.28  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.92/1.28  
% 1.92/1.28  %Foreground sorts:
% 1.92/1.28  
% 1.92/1.28  
% 1.92/1.28  %Background operators:
% 1.92/1.28  
% 1.92/1.28  
% 1.92/1.28  %Foreground operators:
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.28  
% 1.92/1.29  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.92/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.92/1.29  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.92/1.29  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.92/1.29  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 1.92/1.29  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.92/1.29  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.92/1.29  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.29  tff(c_10, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.29  tff(c_29, plain, (![B_14, A_15]: (k2_xboole_0(B_14, A_15)=k2_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.29  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.29  tff(c_45, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, A_15)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_29, c_8])).
% 1.92/1.29  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.92/1.29  tff(c_117, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.29  tff(c_125, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_117])).
% 1.92/1.29  tff(c_145, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.29  tff(c_157, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_125, c_145])).
% 1.92/1.29  tff(c_177, plain, (![A_25, B_26, C_27]: (k4_xboole_0(k4_xboole_0(A_25, B_26), C_27)=k4_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.29  tff(c_203, plain, (![C_27]: (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), C_27)=k4_xboole_0('#skF_1', k2_xboole_0(k1_xboole_0, C_27)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_177])).
% 1.92/1.29  tff(c_257, plain, (![C_30]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_30))=k4_xboole_0('#skF_1', C_30))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_45, c_203])).
% 1.92/1.29  tff(c_317, plain, (![B_32]: (k4_xboole_0('#skF_1', k2_xboole_0(B_32, '#skF_2'))=k4_xboole_0('#skF_1', B_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_257])).
% 1.92/1.29  tff(c_330, plain, (![B_32]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', B_32))=k3_xboole_0('#skF_1', k2_xboole_0(B_32, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_317, c_14])).
% 1.92/1.29  tff(c_353, plain, (![B_32]: (k3_xboole_0('#skF_1', k2_xboole_0(B_32, '#skF_2'))=k3_xboole_0('#skF_1', B_32))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_330])).
% 1.92/1.29  tff(c_16, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.92/1.29  tff(c_19, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.92/1.29  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_19])).
% 1.92/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.29  
% 1.92/1.29  Inference rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Ref     : 0
% 1.92/1.29  #Sup     : 82
% 1.92/1.29  #Fact    : 0
% 1.92/1.29  #Define  : 0
% 1.92/1.29  #Split   : 0
% 1.92/1.29  #Chain   : 0
% 1.92/1.29  #Close   : 0
% 1.92/1.29  
% 1.92/1.29  Ordering : KBO
% 1.92/1.29  
% 1.92/1.29  Simplification rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Subsume      : 0
% 1.92/1.29  #Demod        : 50
% 1.92/1.29  #Tautology    : 58
% 1.92/1.29  #SimpNegUnit  : 0
% 1.92/1.29  #BackRed      : 1
% 1.92/1.29  
% 1.92/1.29  #Partial instantiations: 0
% 1.92/1.29  #Strategies tried      : 1
% 1.92/1.29  
% 1.92/1.29  Timing (in seconds)
% 1.92/1.29  ----------------------
% 1.92/1.29  Preprocessing        : 0.28
% 1.92/1.29  Parsing              : 0.15
% 1.92/1.29  CNF conversion       : 0.02
% 1.92/1.29  Main loop            : 0.21
% 1.92/1.29  Inferencing          : 0.07
% 1.92/1.29  Reduction            : 0.09
% 1.92/1.29  Demodulation         : 0.07
% 1.92/1.29  BG Simplification    : 0.01
% 1.92/1.29  Subsumption          : 0.02
% 1.92/1.29  Abstraction          : 0.01
% 1.92/1.29  MUC search           : 0.00
% 1.92/1.29  Cooper               : 0.00
% 1.92/1.29  Total                : 0.51
% 1.92/1.29  Index Insertion      : 0.00
% 1.92/1.29  Index Deletion       : 0.00
% 1.92/1.29  Index Matching       : 0.00
% 1.92/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

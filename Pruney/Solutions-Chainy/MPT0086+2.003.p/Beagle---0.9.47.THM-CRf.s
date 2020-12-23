%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:13 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  34 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_91])).

tff(c_113,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_109])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [A_25,B_26] : k4_xboole_0(k2_xboole_0(A_25,B_26),B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_114])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_429,plain,(
    ! [A_36,B_37] : k4_xboole_0(k2_xboole_0(A_36,B_37),A_36) = k4_xboole_0(B_37,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_114])).

tff(c_468,plain,(
    ! [B_7,A_6] : k4_xboole_0(k4_xboole_0(B_7,A_6),A_6) = k4_xboole_0(k2_xboole_0(A_6,B_7),A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_429])).

tff(c_494,plain,(
    ! [B_38,A_39] : k4_xboole_0(k4_xboole_0(B_38,A_39),A_39) = k4_xboole_0(B_38,A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_468])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_503,plain,(
    ! [B_38,A_39] : k4_xboole_0(k4_xboole_0(B_38,A_39),k4_xboole_0(B_38,A_39)) = k3_xboole_0(k4_xboole_0(B_38,A_39),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_16])).

tff(c_541,plain,(
    ! [B_38,A_39] : k3_xboole_0(k4_xboole_0(B_38,A_39),A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_503])).

tff(c_68,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_18])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.02/1.27  
% 2.02/1.27  %Foreground sorts:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Background operators:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Foreground operators:
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.27  
% 2.02/1.28  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.02/1.28  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.02/1.28  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.02/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.02/1.28  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.02/1.28  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.02/1.28  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.02/1.28  tff(f_44, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.02/1.28  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.28  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.28  tff(c_91, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.28  tff(c_109, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_91])).
% 2.02/1.28  tff(c_113, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_109])).
% 2.02/1.28  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.28  tff(c_114, plain, (![A_25, B_26]: (k4_xboole_0(k2_xboole_0(A_25, B_26), B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.28  tff(c_139, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_114])).
% 2.02/1.28  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.28  tff(c_429, plain, (![A_36, B_37]: (k4_xboole_0(k2_xboole_0(A_36, B_37), A_36)=k4_xboole_0(B_37, A_36))), inference(superposition, [status(thm), theory('equality')], [c_2, c_114])).
% 2.02/1.28  tff(c_468, plain, (![B_7, A_6]: (k4_xboole_0(k4_xboole_0(B_7, A_6), A_6)=k4_xboole_0(k2_xboole_0(A_6, B_7), A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_429])).
% 2.02/1.28  tff(c_494, plain, (![B_38, A_39]: (k4_xboole_0(k4_xboole_0(B_38, A_39), A_39)=k4_xboole_0(B_38, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_468])).
% 2.02/1.28  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.28  tff(c_503, plain, (![B_38, A_39]: (k4_xboole_0(k4_xboole_0(B_38, A_39), k4_xboole_0(B_38, A_39))=k3_xboole_0(k4_xboole_0(B_38, A_39), A_39))), inference(superposition, [status(thm), theory('equality')], [c_494, c_16])).
% 2.02/1.28  tff(c_541, plain, (![B_38, A_39]: (k3_xboole_0(k4_xboole_0(B_38, A_39), A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_503])).
% 2.02/1.28  tff(c_68, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.28  tff(c_18, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.28  tff(c_72, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_18])).
% 2.02/1.28  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_541, c_72])).
% 2.02/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.28  
% 2.02/1.28  Inference rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Ref     : 0
% 2.02/1.28  #Sup     : 125
% 2.02/1.28  #Fact    : 0
% 2.02/1.28  #Define  : 0
% 2.02/1.28  #Split   : 0
% 2.02/1.28  #Chain   : 0
% 2.02/1.28  #Close   : 0
% 2.02/1.28  
% 2.02/1.28  Ordering : KBO
% 2.02/1.28  
% 2.02/1.28  Simplification rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Subsume      : 0
% 2.02/1.28  #Demod        : 89
% 2.02/1.28  #Tautology    : 99
% 2.02/1.28  #SimpNegUnit  : 0
% 2.02/1.28  #BackRed      : 1
% 2.02/1.28  
% 2.02/1.28  #Partial instantiations: 0
% 2.02/1.28  #Strategies tried      : 1
% 2.02/1.28  
% 2.02/1.28  Timing (in seconds)
% 2.02/1.28  ----------------------
% 2.02/1.28  Preprocessing        : 0.26
% 2.02/1.28  Parsing              : 0.15
% 2.02/1.28  CNF conversion       : 0.01
% 2.02/1.28  Main loop            : 0.22
% 2.02/1.28  Inferencing          : 0.08
% 2.02/1.28  Reduction            : 0.08
% 2.02/1.28  Demodulation         : 0.07
% 2.02/1.28  BG Simplification    : 0.01
% 2.02/1.28  Subsumption          : 0.03
% 2.02/1.28  Abstraction          : 0.01
% 2.02/1.28  MUC search           : 0.00
% 2.02/1.28  Cooper               : 0.00
% 2.02/1.28  Total                : 0.51
% 2.02/1.28  Index Insertion      : 0.00
% 2.02/1.29  Index Deletion       : 0.00
% 2.02/1.29  Index Matching       : 0.00
% 2.02/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

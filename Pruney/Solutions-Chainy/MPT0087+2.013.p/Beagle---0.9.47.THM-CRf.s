%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:18 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  38 expanded)
%              Number of equality atoms :   26 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(k4_xboole_0(A_33,B_34),C_35) = k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_100,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_226,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(B_34,k4_xboole_0(A_33,B_34))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_100])).

tff(c_283,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(B_37,A_36)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_226])).

tff(c_321,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_283])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_48])).

tff(c_164,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(k3_xboole_0(A_30,B_31),C_32) = k3_xboole_0(A_30,k4_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_202,plain,(
    ! [C_32] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_32)) = k4_xboole_0(k1_xboole_0,C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_164])).

tff(c_409,plain,(
    ! [C_32] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_32)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_202])).

tff(c_57,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_20])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.59  
% 2.45/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.59  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.59  
% 2.45/1.59  %Foreground sorts:
% 2.45/1.59  
% 2.45/1.59  
% 2.45/1.59  %Background operators:
% 2.45/1.59  
% 2.45/1.59  
% 2.45/1.59  %Foreground operators:
% 2.45/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.59  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.59  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.59  
% 2.45/1.61  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.45/1.61  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.45/1.61  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.45/1.61  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.45/1.61  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.45/1.61  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.45/1.61  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 2.45/1.61  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.45/1.61  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.45/1.61  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.61  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.61  tff(c_216, plain, (![A_33, B_34, C_35]: (k4_xboole_0(k4_xboole_0(A_33, B_34), C_35)=k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.61  tff(c_8, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.61  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.61  tff(c_79, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.61  tff(c_97, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_79])).
% 2.45/1.61  tff(c_100, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_97])).
% 2.45/1.61  tff(c_226, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k4_xboole_0(A_33, B_34)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_100])).
% 2.45/1.61  tff(c_283, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(B_37, A_36))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_226])).
% 2.45/1.61  tff(c_321, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_283])).
% 2.45/1.61  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.45/1.61  tff(c_48, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.61  tff(c_52, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_48])).
% 2.45/1.61  tff(c_164, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k3_xboole_0(A_30, B_31), C_32)=k3_xboole_0(A_30, k4_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.61  tff(c_202, plain, (![C_32]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_32))=k4_xboole_0(k1_xboole_0, C_32))), inference(superposition, [status(thm), theory('equality')], [c_52, c_164])).
% 2.45/1.61  tff(c_409, plain, (![C_32]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_32))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_321, c_202])).
% 2.45/1.61  tff(c_57, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.61  tff(c_20, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.45/1.61  tff(c_65, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_57, c_20])).
% 2.45/1.61  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_409, c_65])).
% 2.45/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.61  
% 2.45/1.61  Inference rules
% 2.45/1.61  ----------------------
% 2.45/1.61  #Ref     : 0
% 2.45/1.61  #Sup     : 95
% 2.45/1.61  #Fact    : 0
% 2.45/1.61  #Define  : 0
% 2.45/1.61  #Split   : 0
% 2.45/1.61  #Chain   : 0
% 2.45/1.61  #Close   : 0
% 2.45/1.61  
% 2.45/1.61  Ordering : KBO
% 2.45/1.61  
% 2.45/1.61  Simplification rules
% 2.45/1.61  ----------------------
% 2.45/1.61  #Subsume      : 0
% 2.45/1.61  #Demod        : 33
% 2.45/1.61  #Tautology    : 55
% 2.45/1.61  #SimpNegUnit  : 0
% 2.45/1.61  #BackRed      : 1
% 2.45/1.61  
% 2.45/1.61  #Partial instantiations: 0
% 2.45/1.61  #Strategies tried      : 1
% 2.45/1.61  
% 2.45/1.61  Timing (in seconds)
% 2.45/1.61  ----------------------
% 2.45/1.61  Preprocessing        : 0.46
% 2.45/1.61  Parsing              : 0.24
% 2.45/1.61  CNF conversion       : 0.03
% 2.45/1.61  Main loop            : 0.31
% 2.45/1.61  Inferencing          : 0.12
% 2.45/1.61  Reduction            : 0.11
% 2.45/1.61  Demodulation         : 0.09
% 2.45/1.61  BG Simplification    : 0.02
% 2.45/1.61  Subsumption          : 0.04
% 2.45/1.61  Abstraction          : 0.02
% 2.45/1.61  MUC search           : 0.00
% 2.45/1.61  Cooper               : 0.00
% 2.45/1.61  Total                : 0.82
% 2.45/1.61  Index Insertion      : 0.00
% 2.45/1.62  Index Deletion       : 0.00
% 2.45/1.62  Index Matching       : 0.00
% 2.45/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------

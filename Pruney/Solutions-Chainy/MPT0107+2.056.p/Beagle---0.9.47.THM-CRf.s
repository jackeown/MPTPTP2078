%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:00 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   26 (  34 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_595,plain,(
    ! [A_48,B_49,C_50] : k3_xboole_0(k4_xboole_0(A_48,B_49),k4_xboole_0(A_48,C_50)) = k4_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_651,plain,(
    ! [A_4,B_49] : k4_xboole_0(A_4,k2_xboole_0(B_49,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_4,B_49),A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_595])).

tff(c_1592,plain,(
    ! [A_73,B_74] : k3_xboole_0(k4_xboole_0(A_73,B_74),A_73) = k4_xboole_0(A_73,B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_651])).

tff(c_1639,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(k3_xboole_0(A_12,B_13),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1592])).

tff(c_1943,plain,(
    ! [A_82,B_83] : k3_xboole_0(k3_xboole_0(A_82,B_83),A_82) = k3_xboole_0(A_82,B_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1639])).

tff(c_1963,plain,(
    ! [A_82,B_83] : k4_xboole_0(k3_xboole_0(A_82,B_83),k3_xboole_0(A_82,B_83)) = k4_xboole_0(k3_xboole_0(A_82,B_83),A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_1943,c_12])).

tff(c_2030,plain,(
    ! [A_84,B_85] : k4_xboole_0(k3_xboole_0(A_84,B_85),A_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1963])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2060,plain,(
    ! [A_84,B_85] : k2_xboole_0(k4_xboole_0(A_84,k3_xboole_0(A_84,B_85)),k1_xboole_0) = k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2030,c_2])).

tff(c_2128,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4,c_2060])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.90  
% 4.73/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.91  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.73/1.91  
% 4.73/1.91  %Foreground sorts:
% 4.73/1.91  
% 4.73/1.91  
% 4.73/1.91  %Background operators:
% 4.73/1.91  
% 4.73/1.91  
% 4.73/1.91  %Foreground operators:
% 4.73/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.73/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.73/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.73/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.73/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.73/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.73/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.73/1.91  
% 4.73/1.92  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.73/1.92  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.73/1.92  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.73/1.92  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.73/1.92  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.73/1.92  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 4.73/1.92  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.73/1.92  tff(f_48, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.73/1.92  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.73/1.92  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.73/1.92  tff(c_58, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.73/1.92  tff(c_68, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_58])).
% 4.73/1.92  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.73/1.92  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.73/1.92  tff(c_595, plain, (![A_48, B_49, C_50]: (k3_xboole_0(k4_xboole_0(A_48, B_49), k4_xboole_0(A_48, C_50))=k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.73/1.92  tff(c_651, plain, (![A_4, B_49]: (k4_xboole_0(A_4, k2_xboole_0(B_49, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_4, B_49), A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_595])).
% 4.73/1.92  tff(c_1592, plain, (![A_73, B_74]: (k3_xboole_0(k4_xboole_0(A_73, B_74), A_73)=k4_xboole_0(A_73, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_651])).
% 4.73/1.92  tff(c_1639, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(k3_xboole_0(A_12, B_13), A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1592])).
% 4.73/1.92  tff(c_1943, plain, (![A_82, B_83]: (k3_xboole_0(k3_xboole_0(A_82, B_83), A_82)=k3_xboole_0(A_82, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1639])).
% 4.73/1.92  tff(c_1963, plain, (![A_82, B_83]: (k4_xboole_0(k3_xboole_0(A_82, B_83), k3_xboole_0(A_82, B_83))=k4_xboole_0(k3_xboole_0(A_82, B_83), A_82))), inference(superposition, [status(thm), theory('equality')], [c_1943, c_12])).
% 4.73/1.92  tff(c_2030, plain, (![A_84, B_85]: (k4_xboole_0(k3_xboole_0(A_84, B_85), A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1963])).
% 4.73/1.92  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.73/1.92  tff(c_2060, plain, (![A_84, B_85]: (k2_xboole_0(k4_xboole_0(A_84, k3_xboole_0(A_84, B_85)), k1_xboole_0)=k5_xboole_0(A_84, k3_xboole_0(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_2030, c_2])).
% 4.73/1.92  tff(c_2128, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4, c_2060])).
% 4.73/1.92  tff(c_22, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.73/1.92  tff(c_6294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2128, c_22])).
% 4.73/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.92  
% 4.73/1.92  Inference rules
% 4.73/1.92  ----------------------
% 4.73/1.92  #Ref     : 0
% 4.73/1.92  #Sup     : 1512
% 4.73/1.92  #Fact    : 0
% 4.73/1.92  #Define  : 0
% 4.73/1.92  #Split   : 0
% 4.73/1.92  #Chain   : 0
% 4.73/1.92  #Close   : 0
% 4.73/1.92  
% 4.73/1.92  Ordering : KBO
% 4.73/1.92  
% 4.73/1.92  Simplification rules
% 4.73/1.92  ----------------------
% 4.73/1.92  #Subsume      : 0
% 4.73/1.92  #Demod        : 1522
% 4.73/1.92  #Tautology    : 1154
% 4.73/1.92  #SimpNegUnit  : 0
% 4.73/1.92  #BackRed      : 1
% 4.73/1.92  
% 4.73/1.92  #Partial instantiations: 0
% 4.73/1.92  #Strategies tried      : 1
% 4.73/1.92  
% 4.73/1.92  Timing (in seconds)
% 4.98/1.92  ----------------------
% 4.98/1.92  Preprocessing        : 0.27
% 4.98/1.92  Parsing              : 0.15
% 4.98/1.92  CNF conversion       : 0.02
% 4.98/1.92  Main loop            : 0.87
% 4.98/1.92  Inferencing          : 0.30
% 4.98/1.92  Reduction            : 0.38
% 4.98/1.92  Demodulation         : 0.31
% 4.98/1.92  BG Simplification    : 0.03
% 4.98/1.92  Subsumption          : 0.11
% 4.98/1.92  Abstraction          : 0.06
% 4.98/1.92  MUC search           : 0.00
% 4.98/1.92  Cooper               : 0.00
% 4.98/1.92  Total                : 1.17
% 4.98/1.92  Index Insertion      : 0.00
% 4.98/1.92  Index Deletion       : 0.00
% 4.98/1.92  Index Matching       : 0.00
% 4.98/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------

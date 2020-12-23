%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:48 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   28 (  42 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),k3_xboole_0(A_7,B_8)) = k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_292,plain,(
    ! [A_37,B_38] : k2_xboole_0(k4_xboole_0(A_37,B_38),k3_xboole_0(A_37,B_38)) = k2_xboole_0(A_37,k4_xboole_0(A_37,B_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_301,plain,(
    ! [A_37,B_38] : k2_xboole_0(k3_xboole_0(A_37,B_38),k4_xboole_0(A_37,B_38)) = k2_xboole_0(A_37,k4_xboole_0(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_2])).

tff(c_325,plain,(
    ! [A_37,B_38] : k2_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_301])).

tff(c_216,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k4_xboole_0(A_30,B_31),k3_xboole_0(A_30,C_32)) = k4_xboole_0(A_30,k4_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_383,plain,(
    ! [A_42,C_43,B_44] : k2_xboole_0(k3_xboole_0(A_42,C_43),k4_xboole_0(A_42,B_44)) = k4_xboole_0(A_42,k4_xboole_0(B_44,C_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_216])).

tff(c_442,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(B_48,B_48)) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_10])).

tff(c_510,plain,(
    ! [B_49] : k3_xboole_0(B_49,B_49) = B_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_8])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)) = k4_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_528,plain,(
    ! [B_49,B_12] : k4_xboole_0(B_49,k4_xboole_0(B_12,B_49)) = k2_xboole_0(k4_xboole_0(B_49,B_12),B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_12])).

tff(c_559,plain,(
    ! [B_51,B_52] : k4_xboole_0(B_51,k4_xboole_0(B_52,B_51)) = B_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_2,c_528])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_593,plain,(
    ! [B_51,B_52] : k2_xboole_0(B_51,k4_xboole_0(k4_xboole_0(B_52,B_51),B_51)) = k5_xboole_0(B_51,k4_xboole_0(B_52,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_4])).

tff(c_641,plain,(
    ! [B_51,B_52] : k5_xboole_0(B_51,k4_xboole_0(B_52,B_51)) = k2_xboole_0(B_51,B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_593])).

tff(c_14,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.45  
% 2.82/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.45  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 2.82/1.45  
% 2.82/1.45  %Foreground sorts:
% 2.82/1.45  
% 2.82/1.45  
% 2.82/1.45  %Background operators:
% 2.82/1.45  
% 2.82/1.45  
% 2.82/1.45  %Foreground operators:
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.82/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.45  
% 2.82/1.46  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.82/1.46  tff(f_35, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.82/1.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.82/1.46  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.82/1.46  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.82/1.46  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.82/1.46  tff(f_40, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.82/1.46  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.46  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.46  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.82/1.46  tff(c_75, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.46  tff(c_84, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), k3_xboole_0(A_7, B_8))=k2_xboole_0(k4_xboole_0(A_7, B_8), A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_75])).
% 2.82/1.46  tff(c_292, plain, (![A_37, B_38]: (k2_xboole_0(k4_xboole_0(A_37, B_38), k3_xboole_0(A_37, B_38))=k2_xboole_0(A_37, k4_xboole_0(A_37, B_38)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_84])).
% 2.82/1.46  tff(c_301, plain, (![A_37, B_38]: (k2_xboole_0(k3_xboole_0(A_37, B_38), k4_xboole_0(A_37, B_38))=k2_xboole_0(A_37, k4_xboole_0(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_292, c_2])).
% 2.82/1.46  tff(c_325, plain, (![A_37, B_38]: (k2_xboole_0(A_37, k4_xboole_0(A_37, B_38))=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_301])).
% 2.82/1.46  tff(c_216, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k3_xboole_0(A_30, C_32))=k4_xboole_0(A_30, k4_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.46  tff(c_383, plain, (![A_42, C_43, B_44]: (k2_xboole_0(k3_xboole_0(A_42, C_43), k4_xboole_0(A_42, B_44))=k4_xboole_0(A_42, k4_xboole_0(B_44, C_43)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_216])).
% 2.82/1.46  tff(c_442, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(B_48, B_48))=A_47)), inference(superposition, [status(thm), theory('equality')], [c_383, c_10])).
% 2.82/1.46  tff(c_510, plain, (![B_49]: (k3_xboole_0(B_49, B_49)=B_49)), inference(superposition, [status(thm), theory('equality')], [c_442, c_8])).
% 2.82/1.46  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13))=k4_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.46  tff(c_528, plain, (![B_49, B_12]: (k4_xboole_0(B_49, k4_xboole_0(B_12, B_49))=k2_xboole_0(k4_xboole_0(B_49, B_12), B_49))), inference(superposition, [status(thm), theory('equality')], [c_510, c_12])).
% 2.82/1.46  tff(c_559, plain, (![B_51, B_52]: (k4_xboole_0(B_51, k4_xboole_0(B_52, B_51))=B_51)), inference(demodulation, [status(thm), theory('equality')], [c_325, c_2, c_528])).
% 2.82/1.46  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.82/1.46  tff(c_593, plain, (![B_51, B_52]: (k2_xboole_0(B_51, k4_xboole_0(k4_xboole_0(B_52, B_51), B_51))=k5_xboole_0(B_51, k4_xboole_0(B_52, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_559, c_4])).
% 2.82/1.46  tff(c_641, plain, (![B_51, B_52]: (k5_xboole_0(B_51, k4_xboole_0(B_52, B_51))=k2_xboole_0(B_51, B_52))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_593])).
% 2.82/1.46  tff(c_14, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.82/1.46  tff(c_1440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_14])).
% 2.82/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.46  
% 2.82/1.46  Inference rules
% 2.82/1.46  ----------------------
% 2.82/1.46  #Ref     : 0
% 2.82/1.46  #Sup     : 353
% 2.82/1.46  #Fact    : 0
% 2.82/1.46  #Define  : 0
% 2.82/1.46  #Split   : 0
% 2.82/1.46  #Chain   : 0
% 2.82/1.46  #Close   : 0
% 2.82/1.46  
% 2.82/1.46  Ordering : KBO
% 2.82/1.46  
% 2.82/1.46  Simplification rules
% 2.82/1.46  ----------------------
% 2.82/1.46  #Subsume      : 2
% 2.82/1.46  #Demod        : 221
% 2.82/1.46  #Tautology    : 207
% 2.82/1.46  #SimpNegUnit  : 0
% 2.82/1.46  #BackRed      : 3
% 2.82/1.46  
% 2.82/1.46  #Partial instantiations: 0
% 2.82/1.46  #Strategies tried      : 1
% 2.82/1.46  
% 2.82/1.46  Timing (in seconds)
% 2.82/1.46  ----------------------
% 2.82/1.46  Preprocessing        : 0.26
% 2.82/1.46  Parsing              : 0.14
% 2.82/1.46  CNF conversion       : 0.02
% 2.82/1.46  Main loop            : 0.44
% 2.82/1.46  Inferencing          : 0.15
% 2.82/1.46  Reduction            : 0.18
% 2.82/1.46  Demodulation         : 0.15
% 2.82/1.46  BG Simplification    : 0.02
% 2.82/1.46  Subsumption          : 0.06
% 2.82/1.46  Abstraction          : 0.02
% 2.82/1.46  MUC search           : 0.00
% 2.82/1.46  Cooper               : 0.00
% 2.82/1.46  Total                : 0.73
% 2.82/1.46  Index Insertion      : 0.00
% 2.82/1.46  Index Deletion       : 0.00
% 2.82/1.46  Index Matching       : 0.00
% 2.82/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

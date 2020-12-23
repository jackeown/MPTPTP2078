%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:48 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   42 (  75 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   32 (  65 expanded)
%              Number of equality atoms :   31 (  64 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [B_21,A_22] : k2_xboole_0(B_21,A_22) = k2_xboole_0(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_22] : k2_xboole_0(k1_xboole_0,A_22) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_6])).

tff(c_124,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_331,plain,(
    ! [A_37,B_38] : k2_xboole_0(k4_xboole_0(A_37,B_38),k4_xboole_0(B_38,A_37)) = k5_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_367,plain,(
    ! [B_8,A_7] : k2_xboole_0(k4_xboole_0(B_8,k2_xboole_0(A_7,B_8)),k4_xboole_0(A_7,B_8)) = k5_xboole_0(B_8,k2_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_331])).

tff(c_409,plain,(
    ! [B_8,A_7] : k5_xboole_0(B_8,k2_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_134,c_367])).

tff(c_131,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_124])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_403,plain,(
    ! [A_6] : k2_xboole_0(k4_xboole_0(k1_xboole_0,A_6),A_6) = k5_xboole_0(k1_xboole_0,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_331])).

tff(c_419,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_131,c_403])).

tff(c_140,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_124])).

tff(c_382,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,A_5)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_331])).

tff(c_420,plain,(
    ! [A_39] : k5_xboole_0(A_39,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_55,c_382])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k5_xboole_0(k5_xboole_0(A_14,B_15),C_16) = k5_xboole_0(A_14,k5_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_425,plain,(
    ! [A_39,C_16] : k5_xboole_0(A_39,k5_xboole_0(A_39,C_16)) = k5_xboole_0(k1_xboole_0,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_16])).

tff(c_2458,plain,(
    ! [A_85,C_86] : k5_xboole_0(A_85,k5_xboole_0(A_85,C_86)) = C_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_425])).

tff(c_2514,plain,(
    ! [B_8,A_7] : k5_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_2458])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3465,plain,(
    k2_xboole_0('#skF_2','#skF_1') != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2514,c_20])).

tff(c_3468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.64  
% 3.87/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.64  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.87/1.64  
% 3.87/1.64  %Foreground sorts:
% 3.87/1.64  
% 3.87/1.64  
% 3.87/1.64  %Background operators:
% 3.87/1.64  
% 3.87/1.64  
% 3.87/1.64  %Foreground operators:
% 3.87/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.87/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.87/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.87/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.87/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.87/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.87/1.64  
% 3.87/1.65  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.87/1.65  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.87/1.65  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.87/1.65  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.87/1.65  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.87/1.65  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.87/1.65  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.87/1.65  tff(f_46, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.87/1.65  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.65  tff(c_39, plain, (![B_21, A_22]: (k2_xboole_0(B_21, A_22)=k2_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.65  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.65  tff(c_55, plain, (![A_22]: (k2_xboole_0(k1_xboole_0, A_22)=A_22)), inference(superposition, [status(thm), theory('equality')], [c_39, c_6])).
% 3.87/1.65  tff(c_124, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.87/1.65  tff(c_134, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 3.87/1.65  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.65  tff(c_331, plain, (![A_37, B_38]: (k2_xboole_0(k4_xboole_0(A_37, B_38), k4_xboole_0(B_38, A_37))=k5_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.87/1.65  tff(c_367, plain, (![B_8, A_7]: (k2_xboole_0(k4_xboole_0(B_8, k2_xboole_0(A_7, B_8)), k4_xboole_0(A_7, B_8))=k5_xboole_0(B_8, k2_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_331])).
% 3.87/1.65  tff(c_409, plain, (![B_8, A_7]: (k5_xboole_0(B_8, k2_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_134, c_367])).
% 3.87/1.65  tff(c_131, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_55, c_124])).
% 3.87/1.65  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.65  tff(c_403, plain, (![A_6]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, A_6), A_6)=k5_xboole_0(k1_xboole_0, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_331])).
% 3.87/1.65  tff(c_419, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_55, c_131, c_403])).
% 3.87/1.65  tff(c_140, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_124])).
% 3.87/1.65  tff(c_382, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, A_5))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_140, c_331])).
% 3.87/1.65  tff(c_420, plain, (![A_39]: (k5_xboole_0(A_39, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_55, c_382])).
% 3.87/1.65  tff(c_16, plain, (![A_14, B_15, C_16]: (k5_xboole_0(k5_xboole_0(A_14, B_15), C_16)=k5_xboole_0(A_14, k5_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.87/1.65  tff(c_425, plain, (![A_39, C_16]: (k5_xboole_0(A_39, k5_xboole_0(A_39, C_16))=k5_xboole_0(k1_xboole_0, C_16))), inference(superposition, [status(thm), theory('equality')], [c_420, c_16])).
% 3.87/1.65  tff(c_2458, plain, (![A_85, C_86]: (k5_xboole_0(A_85, k5_xboole_0(A_85, C_86))=C_86)), inference(demodulation, [status(thm), theory('equality')], [c_419, c_425])).
% 3.87/1.65  tff(c_2514, plain, (![B_8, A_7]: (k5_xboole_0(B_8, k4_xboole_0(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_409, c_2458])).
% 3.87/1.65  tff(c_20, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.87/1.65  tff(c_3465, plain, (k2_xboole_0('#skF_2', '#skF_1')!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2514, c_20])).
% 3.87/1.65  tff(c_3468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3465])).
% 3.87/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.65  
% 3.87/1.65  Inference rules
% 3.87/1.65  ----------------------
% 3.87/1.65  #Ref     : 0
% 3.87/1.65  #Sup     : 859
% 3.87/1.65  #Fact    : 0
% 3.87/1.65  #Define  : 0
% 3.87/1.65  #Split   : 0
% 3.87/1.65  #Chain   : 0
% 3.87/1.65  #Close   : 0
% 3.87/1.65  
% 3.87/1.65  Ordering : KBO
% 3.87/1.65  
% 3.87/1.65  Simplification rules
% 3.87/1.65  ----------------------
% 3.87/1.65  #Subsume      : 9
% 3.87/1.65  #Demod        : 682
% 3.87/1.65  #Tautology    : 563
% 3.87/1.65  #SimpNegUnit  : 0
% 3.87/1.65  #BackRed      : 6
% 3.87/1.65  
% 3.87/1.65  #Partial instantiations: 0
% 3.87/1.65  #Strategies tried      : 1
% 3.87/1.65  
% 3.87/1.65  Timing (in seconds)
% 3.87/1.65  ----------------------
% 3.87/1.65  Preprocessing        : 0.26
% 3.87/1.65  Parsing              : 0.15
% 3.87/1.65  CNF conversion       : 0.02
% 3.87/1.65  Main loop            : 0.63
% 3.87/1.65  Inferencing          : 0.20
% 3.87/1.65  Reduction            : 0.29
% 3.87/1.65  Demodulation         : 0.24
% 3.87/1.65  BG Simplification    : 0.02
% 3.87/1.65  Subsumption          : 0.08
% 3.87/1.65  Abstraction          : 0.03
% 3.87/1.65  MUC search           : 0.00
% 3.87/1.65  Cooper               : 0.00
% 3.87/1.65  Total                : 0.91
% 3.87/1.65  Index Insertion      : 0.00
% 3.87/1.65  Index Deletion       : 0.00
% 3.87/1.65  Index Matching       : 0.00
% 3.87/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:45:07 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  40 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_213,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_184])).

tff(c_222,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_213])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_197,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_184])).

tff(c_469,plain,(
    ! [A_46,B_47] : k3_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_197])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_134,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_146,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_134])).

tff(c_475,plain,(
    ! [A_46,B_47] : k4_xboole_0(k4_xboole_0(A_46,B_47),k4_xboole_0(A_46,B_47)) = k4_xboole_0(k4_xboole_0(A_46,B_47),A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_146])).

tff(c_531,plain,(
    ! [A_48,B_49] : k4_xboole_0(k4_xboole_0(A_48,B_49),A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_475])).

tff(c_590,plain,(
    ! [A_50,B_51] : k4_xboole_0(k3_xboole_0(A_50,B_51),A_50) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_531])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k3_xboole_0(A_15,B_16),C_17) = k3_xboole_0(A_15,k4_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_863,plain,(
    ! [A_60,B_61] : k3_xboole_0(A_60,k4_xboole_0(B_61,A_60)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_20])).

tff(c_907,plain,(
    ! [A_5,B_6] : k3_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_863])).

tff(c_124,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_128,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_24])).

tff(c_4552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:02:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.78  
% 4.18/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.78  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.18/1.78  
% 4.18/1.78  %Foreground sorts:
% 4.18/1.78  
% 4.18/1.78  
% 4.18/1.78  %Background operators:
% 4.18/1.78  
% 4.18/1.78  
% 4.18/1.78  %Foreground operators:
% 4.18/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.18/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.18/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.18/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.18/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.18/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.18/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.18/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.18/1.78  
% 4.18/1.79  tff(f_33, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 4.18/1.79  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.18/1.79  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.18/1.79  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.18/1.79  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.18/1.79  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.18/1.79  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.18/1.79  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.18/1.79  tff(f_50, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_xboole_1)).
% 4.18/1.79  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.18/1.79  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.18/1.79  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.18/1.79  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.18/1.79  tff(c_184, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.18/1.79  tff(c_213, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_184])).
% 4.18/1.79  tff(c_222, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_213])).
% 4.18/1.79  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.18/1.79  tff(c_197, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k3_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_184])).
% 4.18/1.79  tff(c_469, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_197])).
% 4.18/1.79  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.18/1.79  tff(c_134, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.18/1.79  tff(c_146, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_134])).
% 4.18/1.79  tff(c_475, plain, (![A_46, B_47]: (k4_xboole_0(k4_xboole_0(A_46, B_47), k4_xboole_0(A_46, B_47))=k4_xboole_0(k4_xboole_0(A_46, B_47), A_46))), inference(superposition, [status(thm), theory('equality')], [c_469, c_146])).
% 4.18/1.79  tff(c_531, plain, (![A_48, B_49]: (k4_xboole_0(k4_xboole_0(A_48, B_49), A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_475])).
% 4.18/1.79  tff(c_590, plain, (![A_50, B_51]: (k4_xboole_0(k3_xboole_0(A_50, B_51), A_50)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_531])).
% 4.18/1.79  tff(c_20, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k3_xboole_0(A_15, B_16), C_17)=k3_xboole_0(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.18/1.79  tff(c_863, plain, (![A_60, B_61]: (k3_xboole_0(A_60, k4_xboole_0(B_61, A_60))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_590, c_20])).
% 4.18/1.79  tff(c_907, plain, (![A_5, B_6]: (k3_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_863])).
% 4.18/1.79  tff(c_124, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.18/1.79  tff(c_24, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.18/1.79  tff(c_128, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_24])).
% 4.18/1.79  tff(c_4552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_907, c_128])).
% 4.18/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.79  
% 4.18/1.79  Inference rules
% 4.18/1.79  ----------------------
% 4.18/1.79  #Ref     : 0
% 4.18/1.79  #Sup     : 1133
% 4.18/1.79  #Fact    : 0
% 4.18/1.79  #Define  : 0
% 4.18/1.79  #Split   : 0
% 4.18/1.79  #Chain   : 0
% 4.18/1.79  #Close   : 0
% 4.18/1.79  
% 4.18/1.79  Ordering : KBO
% 4.18/1.79  
% 4.18/1.79  Simplification rules
% 4.18/1.79  ----------------------
% 4.18/1.79  #Subsume      : 4
% 4.18/1.79  #Demod        : 1236
% 4.18/1.79  #Tautology    : 776
% 4.18/1.79  #SimpNegUnit  : 0
% 4.18/1.79  #BackRed      : 1
% 4.18/1.79  
% 4.18/1.79  #Partial instantiations: 0
% 4.18/1.79  #Strategies tried      : 1
% 4.18/1.79  
% 4.18/1.79  Timing (in seconds)
% 4.18/1.79  ----------------------
% 4.18/1.79  Preprocessing        : 0.28
% 4.18/1.79  Parsing              : 0.15
% 4.18/1.79  CNF conversion       : 0.02
% 4.18/1.79  Main loop            : 0.74
% 4.18/1.79  Inferencing          : 0.23
% 4.18/1.79  Reduction            : 0.35
% 4.18/1.79  Demodulation         : 0.29
% 4.18/1.79  BG Simplification    : 0.03
% 4.18/1.79  Subsumption          : 0.10
% 4.18/1.80  Abstraction          : 0.04
% 4.18/1.80  MUC search           : 0.00
% 4.18/1.80  Cooper               : 0.00
% 4.18/1.80  Total                : 1.05
% 4.18/1.80  Index Insertion      : 0.00
% 4.18/1.80  Index Deletion       : 0.00
% 4.18/1.80  Index Matching       : 0.00
% 4.18/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------

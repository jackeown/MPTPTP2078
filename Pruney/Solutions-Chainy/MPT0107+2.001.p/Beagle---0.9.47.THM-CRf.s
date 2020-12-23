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
% DateTime   : Thu Dec  3 09:44:52 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   35 (  41 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_38,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k5_xboole_0(B_6,A_5) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_368,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_377,plain,(
    ! [A_43,B_44] : k5_xboole_0(k3_xboole_0(A_43,B_44),k4_xboole_0(A_43,B_44)) = k2_xboole_0(k3_xboole_0(A_43,B_44),A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_26])).

tff(c_897,plain,(
    ! [A_60,B_61] : k5_xboole_0(k3_xboole_0(A_60,B_61),k4_xboole_0(A_60,B_61)) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_377])).

tff(c_1007,plain,(
    ! [A_64,B_65] : k5_xboole_0(k3_xboole_0(A_64,B_65),k4_xboole_0(B_65,A_64)) = B_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_897])).

tff(c_118,plain,(
    ! [B_29,A_30] : k5_xboole_0(B_29,A_30) = k5_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_20,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_1') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20])).

tff(c_134,plain,(
    ! [A_30] : k5_xboole_0('#skF_1',A_30) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_76])).

tff(c_24,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_75,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24])).

tff(c_464,plain,(
    ! [A_49,B_50,C_51] : k5_xboole_0(k5_xboole_0(A_49,B_50),C_51) = k5_xboole_0(A_49,k5_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_528,plain,(
    ! [A_18,C_51] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_51)) = k5_xboole_0('#skF_1',C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_464])).

tff(c_541,plain,(
    ! [A_18,C_51] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_51)) = C_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_528])).

tff(c_1581,plain,(
    ! [A_75,B_76] : k5_xboole_0(k3_xboole_0(A_75,B_76),B_76) = k4_xboole_0(B_76,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_1007,c_541])).

tff(c_1650,plain,(
    ! [B_6,A_75] : k5_xboole_0(B_6,k3_xboole_0(A_75,B_6)) = k4_xboole_0(B_6,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1581])).

tff(c_28,plain,(
    k5_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_29,plain,(
    k5_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_2880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.65  
% 3.73/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.65  %$ v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.73/1.65  
% 3.73/1.65  %Foreground sorts:
% 3.73/1.65  
% 3.73/1.65  
% 3.73/1.65  %Background operators:
% 3.73/1.65  
% 3.73/1.65  
% 3.73/1.65  %Foreground operators:
% 3.73/1.65  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.73/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.73/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.73/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.73/1.65  
% 3.73/1.67  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.73/1.67  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.73/1.67  tff(f_40, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.73/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.73/1.67  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.73/1.67  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.73/1.67  tff(f_38, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 3.73/1.67  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.73/1.67  tff(f_46, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.73/1.67  tff(f_50, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.73/1.67  tff(f_48, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.73/1.67  tff(f_55, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.73/1.67  tff(c_6, plain, (![B_6, A_5]: (k5_xboole_0(B_6, A_5)=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.73/1.67  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.73/1.67  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.73/1.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.73/1.67  tff(c_368, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.73/1.67  tff(c_26, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.73/1.67  tff(c_377, plain, (![A_43, B_44]: (k5_xboole_0(k3_xboole_0(A_43, B_44), k4_xboole_0(A_43, B_44))=k2_xboole_0(k3_xboole_0(A_43, B_44), A_43))), inference(superposition, [status(thm), theory('equality')], [c_368, c_26])).
% 3.73/1.67  tff(c_897, plain, (![A_60, B_61]: (k5_xboole_0(k3_xboole_0(A_60, B_61), k4_xboole_0(A_60, B_61))=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_377])).
% 3.73/1.67  tff(c_1007, plain, (![A_64, B_65]: (k5_xboole_0(k3_xboole_0(A_64, B_65), k4_xboole_0(B_65, A_64))=B_65)), inference(superposition, [status(thm), theory('equality')], [c_4, c_897])).
% 3.73/1.67  tff(c_118, plain, (![B_29, A_30]: (k5_xboole_0(B_29, A_30)=k5_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.73/1.67  tff(c_12, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.73/1.67  tff(c_60, plain, (![A_23]: (k1_xboole_0=A_23 | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.73/1.67  tff(c_64, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_12, c_60])).
% 3.73/1.67  tff(c_20, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.73/1.67  tff(c_76, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_1')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20])).
% 3.73/1.67  tff(c_134, plain, (![A_30]: (k5_xboole_0('#skF_1', A_30)=A_30)), inference(superposition, [status(thm), theory('equality')], [c_118, c_76])).
% 3.73/1.67  tff(c_24, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.73/1.67  tff(c_75, plain, (![A_18]: (k5_xboole_0(A_18, A_18)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24])).
% 3.73/1.67  tff(c_464, plain, (![A_49, B_50, C_51]: (k5_xboole_0(k5_xboole_0(A_49, B_50), C_51)=k5_xboole_0(A_49, k5_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.67  tff(c_528, plain, (![A_18, C_51]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_51))=k5_xboole_0('#skF_1', C_51))), inference(superposition, [status(thm), theory('equality')], [c_75, c_464])).
% 3.73/1.67  tff(c_541, plain, (![A_18, C_51]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_51))=C_51)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_528])).
% 3.73/1.67  tff(c_1581, plain, (![A_75, B_76]: (k5_xboole_0(k3_xboole_0(A_75, B_76), B_76)=k4_xboole_0(B_76, A_75))), inference(superposition, [status(thm), theory('equality')], [c_1007, c_541])).
% 3.73/1.67  tff(c_1650, plain, (![B_6, A_75]: (k5_xboole_0(B_6, k3_xboole_0(A_75, B_6))=k4_xboole_0(B_6, A_75))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1581])).
% 3.73/1.67  tff(c_28, plain, (k5_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.73/1.67  tff(c_29, plain, (k5_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28])).
% 3.73/1.67  tff(c_2880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1650, c_29])).
% 3.73/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.67  
% 3.73/1.67  Inference rules
% 3.73/1.67  ----------------------
% 3.73/1.67  #Ref     : 0
% 3.73/1.67  #Sup     : 701
% 3.73/1.67  #Fact    : 0
% 3.73/1.67  #Define  : 0
% 3.73/1.67  #Split   : 0
% 3.73/1.67  #Chain   : 0
% 3.73/1.67  #Close   : 0
% 3.73/1.67  
% 3.73/1.67  Ordering : KBO
% 3.73/1.67  
% 3.73/1.67  Simplification rules
% 3.73/1.67  ----------------------
% 3.73/1.67  #Subsume      : 23
% 3.73/1.67  #Demod        : 508
% 3.73/1.67  #Tautology    : 446
% 3.73/1.67  #SimpNegUnit  : 0
% 3.73/1.67  #BackRed      : 8
% 3.73/1.67  
% 3.73/1.67  #Partial instantiations: 0
% 3.73/1.67  #Strategies tried      : 1
% 3.73/1.67  
% 3.73/1.67  Timing (in seconds)
% 3.73/1.67  ----------------------
% 3.73/1.67  Preprocessing        : 0.30
% 3.73/1.67  Parsing              : 0.16
% 3.73/1.67  CNF conversion       : 0.01
% 3.73/1.67  Main loop            : 0.60
% 3.73/1.67  Inferencing          : 0.18
% 3.73/1.67  Reduction            : 0.28
% 3.73/1.67  Demodulation         : 0.23
% 3.73/1.67  BG Simplification    : 0.03
% 3.73/1.67  Subsumption          : 0.07
% 3.73/1.67  Abstraction          : 0.03
% 3.73/1.67  MUC search           : 0.00
% 3.73/1.67  Cooper               : 0.00
% 3.73/1.67  Total                : 0.92
% 3.73/1.67  Index Insertion      : 0.00
% 3.73/1.67  Index Deletion       : 0.00
% 3.73/1.67  Index Matching       : 0.00
% 3.73/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------

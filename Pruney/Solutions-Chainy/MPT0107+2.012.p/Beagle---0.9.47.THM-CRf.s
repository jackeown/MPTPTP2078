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
% DateTime   : Thu Dec  3 09:44:54 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   35 (  50 expanded)
%              Number of equality atoms :   34 (  49 expanded)
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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,k4_xboole_0(A_23,B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_14])).

tff(c_1577,plain,(
    ! [A_23,B_24] : k3_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_125])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_37,plain,(
    ! [B_20,A_21] : k2_xboole_0(B_20,A_21) = k2_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_53,plain,(
    ! [A_21] : k2_xboole_0(k1_xboole_0,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_6])).

tff(c_217,plain,(
    ! [A_31,B_32] : k4_xboole_0(k2_xboole_0(A_31,B_32),B_32) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_232,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k4_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_217])).

tff(c_245,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_232])).

tff(c_350,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k4_xboole_0(A_36,B_37),C_38) = k4_xboole_0(A_36,k2_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_386,plain,(
    ! [A_21,C_38] : k4_xboole_0(A_21,k2_xboole_0(A_21,C_38)) = k4_xboole_0(k1_xboole_0,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_350])).

tff(c_443,plain,(
    ! [A_40,C_41] : k4_xboole_0(A_40,k2_xboole_0(A_40,C_41)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_386])).

tff(c_476,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_443])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_580,plain,(
    ! [A_45,B_46] : k2_xboole_0(k4_xboole_0(A_45,B_46),k4_xboole_0(B_46,A_45)) = k5_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1131,plain,(
    ! [B_59,A_60] : k2_xboole_0(k4_xboole_0(B_59,A_60),k4_xboole_0(A_60,B_59)) = k5_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_2])).

tff(c_1229,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(k4_xboole_0(A_13,B_14),A_13),k3_xboole_0(A_13,B_14)) = k5_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1131])).

tff(c_2565,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k4_xboole_0(A_90,B_91)) = k3_xboole_0(A_90,B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_476,c_2,c_10,c_1229])).

tff(c_2632,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2565])).

tff(c_2653,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1577,c_2632])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:09:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/2.04  
% 4.66/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/2.04  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.66/2.04  
% 4.66/2.04  %Foreground sorts:
% 4.66/2.04  
% 4.66/2.04  
% 4.66/2.04  %Background operators:
% 4.66/2.04  
% 4.66/2.04  
% 4.66/2.04  %Foreground operators:
% 4.66/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.66/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.66/2.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.66/2.04  tff('#skF_2', type, '#skF_2': $i).
% 4.66/2.04  tff('#skF_1', type, '#skF_1': $i).
% 4.66/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.66/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.66/2.04  
% 4.66/2.05  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.66/2.05  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.66/2.05  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.66/2.05  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.66/2.05  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.66/2.05  tff(f_33, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.66/2.05  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.66/2.05  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.66/2.05  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.66/2.05  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.66/2.05  tff(c_122, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/2.05  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/2.05  tff(c_125, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k3_xboole_0(A_23, k4_xboole_0(A_23, B_24)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_14])).
% 4.66/2.05  tff(c_1577, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_125])).
% 4.66/2.05  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/2.05  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.66/2.05  tff(c_16, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.66/2.05  tff(c_37, plain, (![B_20, A_21]: (k2_xboole_0(B_20, A_21)=k2_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.66/2.05  tff(c_53, plain, (![A_21]: (k2_xboole_0(k1_xboole_0, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_37, c_6])).
% 4.66/2.05  tff(c_217, plain, (![A_31, B_32]: (k4_xboole_0(k2_xboole_0(A_31, B_32), B_32)=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.66/2.05  tff(c_232, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k4_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_53, c_217])).
% 4.66/2.05  tff(c_245, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_232])).
% 4.66/2.05  tff(c_350, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k4_xboole_0(A_36, B_37), C_38)=k4_xboole_0(A_36, k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.66/2.05  tff(c_386, plain, (![A_21, C_38]: (k4_xboole_0(A_21, k2_xboole_0(A_21, C_38))=k4_xboole_0(k1_xboole_0, C_38))), inference(superposition, [status(thm), theory('equality')], [c_245, c_350])).
% 4.66/2.05  tff(c_443, plain, (![A_40, C_41]: (k4_xboole_0(A_40, k2_xboole_0(A_40, C_41))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_386])).
% 4.66/2.05  tff(c_476, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_443])).
% 4.66/2.05  tff(c_10, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.66/2.05  tff(c_580, plain, (![A_45, B_46]: (k2_xboole_0(k4_xboole_0(A_45, B_46), k4_xboole_0(B_46, A_45))=k5_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.66/2.05  tff(c_1131, plain, (![B_59, A_60]: (k2_xboole_0(k4_xboole_0(B_59, A_60), k4_xboole_0(A_60, B_59))=k5_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_580, c_2])).
% 4.66/2.05  tff(c_1229, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(k4_xboole_0(A_13, B_14), A_13), k3_xboole_0(A_13, B_14))=k5_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1131])).
% 4.66/2.05  tff(c_2565, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k4_xboole_0(A_90, B_91))=k3_xboole_0(A_90, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_476, c_2, c_10, c_1229])).
% 4.66/2.05  tff(c_2632, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k3_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2565])).
% 4.66/2.05  tff(c_2653, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_1577, c_2632])).
% 4.66/2.05  tff(c_20, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.66/2.05  tff(c_6352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2653, c_20])).
% 4.66/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/2.05  
% 4.66/2.05  Inference rules
% 4.66/2.05  ----------------------
% 4.66/2.05  #Ref     : 0
% 4.66/2.05  #Sup     : 1565
% 4.66/2.05  #Fact    : 0
% 4.66/2.05  #Define  : 0
% 4.66/2.05  #Split   : 0
% 4.66/2.05  #Chain   : 0
% 4.66/2.05  #Close   : 0
% 4.66/2.05  
% 4.66/2.05  Ordering : KBO
% 4.66/2.05  
% 4.66/2.05  Simplification rules
% 4.66/2.06  ----------------------
% 4.66/2.06  #Subsume      : 6
% 4.66/2.06  #Demod        : 1824
% 4.66/2.06  #Tautology    : 1067
% 4.66/2.06  #SimpNegUnit  : 0
% 4.66/2.06  #BackRed      : 5
% 4.66/2.06  
% 4.66/2.06  #Partial instantiations: 0
% 4.66/2.06  #Strategies tried      : 1
% 4.66/2.06  
% 4.66/2.06  Timing (in seconds)
% 4.66/2.06  ----------------------
% 4.66/2.06  Preprocessing        : 0.26
% 4.66/2.06  Parsing              : 0.14
% 4.66/2.06  CNF conversion       : 0.01
% 4.66/2.06  Main loop            : 1.04
% 4.66/2.06  Inferencing          : 0.30
% 4.66/2.06  Reduction            : 0.52
% 4.66/2.06  Demodulation         : 0.44
% 4.66/2.06  BG Simplification    : 0.03
% 4.66/2.06  Subsumption          : 0.13
% 4.66/2.06  Abstraction          : 0.06
% 4.66/2.06  MUC search           : 0.00
% 4.66/2.06  Cooper               : 0.00
% 4.66/2.06  Total                : 1.33
% 4.66/2.06  Index Insertion      : 0.00
% 4.66/2.06  Index Deletion       : 0.00
% 4.66/2.06  Index Matching       : 0.00
% 4.66/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------

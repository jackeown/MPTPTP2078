%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:58 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  44 expanded)
%              Number of equality atoms :   31 (  43 expanded)
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

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_47,plain,(
    ! [B_20,A_21] : k5_xboole_0(B_20,A_21) = k5_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [A_21] : k5_xboole_0(k1_xboole_0,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_311,plain,(
    ! [A_37,B_38,C_39] : k5_xboole_0(k5_xboole_0(A_37,B_38),C_39) = k5_xboole_0(A_37,k5_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_375,plain,(
    ! [A_13,C_39] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_39)) = k5_xboole_0(k1_xboole_0,C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_311])).

tff(c_389,plain,(
    ! [A_40,C_41] : k5_xboole_0(A_40,k5_xboole_0(A_40,C_41)) = C_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_375])).

tff(c_432,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_389])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_187,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_208,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,k3_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_187])).

tff(c_213,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_208])).

tff(c_630,plain,(
    ! [A_46,B_47] : k5_xboole_0(k5_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1739,plain,(
    ! [B_66,A_67] : k5_xboole_0(k5_xboole_0(B_66,A_67),k3_xboole_0(A_67,B_66)) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_630])).

tff(c_1844,plain,(
    ! [A_5,B_6] : k5_xboole_0(k5_xboole_0(k3_xboole_0(A_5,B_6),A_5),k3_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_1739])).

tff(c_1887,plain,(
    ! [A_68,B_69] : k2_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_2,c_2,c_1844])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1903,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k3_xboole_0(A_68,k3_xboole_0(A_68,B_69))) = k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1887,c_4])).

tff(c_1925,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_1903])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1925,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.93  
% 4.86/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.93  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.86/1.93  
% 4.86/1.93  %Foreground sorts:
% 4.86/1.93  
% 4.86/1.93  
% 4.86/1.93  %Background operators:
% 4.86/1.93  
% 4.86/1.93  
% 4.86/1.93  %Foreground operators:
% 4.86/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.86/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.86/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.86/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.86/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.86/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.86/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.86/1.93  
% 4.86/1.94  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.86/1.94  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.86/1.94  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.86/1.94  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.86/1.94  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.86/1.94  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.86/1.94  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.86/1.94  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 4.86/1.94  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.86/1.94  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.86/1.94  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.86/1.94  tff(c_47, plain, (![B_20, A_21]: (k5_xboole_0(B_20, A_21)=k5_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.86/1.94  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.86/1.94  tff(c_63, plain, (![A_21]: (k5_xboole_0(k1_xboole_0, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_47, c_10])).
% 4.86/1.94  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.86/1.94  tff(c_311, plain, (![A_37, B_38, C_39]: (k5_xboole_0(k5_xboole_0(A_37, B_38), C_39)=k5_xboole_0(A_37, k5_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.86/1.94  tff(c_375, plain, (![A_13, C_39]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_39))=k5_xboole_0(k1_xboole_0, C_39))), inference(superposition, [status(thm), theory('equality')], [c_14, c_311])).
% 4.86/1.94  tff(c_389, plain, (![A_40, C_41]: (k5_xboole_0(A_40, k5_xboole_0(A_40, C_41))=C_41)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_375])).
% 4.86/1.94  tff(c_432, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_389])).
% 4.86/1.94  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.86/1.94  tff(c_187, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.86/1.94  tff(c_208, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, k3_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_187])).
% 4.86/1.94  tff(c_213, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_208])).
% 4.86/1.94  tff(c_630, plain, (![A_46, B_47]: (k5_xboole_0(k5_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.86/1.94  tff(c_1739, plain, (![B_66, A_67]: (k5_xboole_0(k5_xboole_0(B_66, A_67), k3_xboole_0(A_67, B_66))=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_2, c_630])).
% 4.86/1.94  tff(c_1844, plain, (![A_5, B_6]: (k5_xboole_0(k5_xboole_0(k3_xboole_0(A_5, B_6), A_5), k3_xboole_0(A_5, B_6))=k2_xboole_0(A_5, k3_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_1739])).
% 4.86/1.94  tff(c_1887, plain, (![A_68, B_69]: (k2_xboole_0(A_68, k3_xboole_0(A_68, B_69))=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_432, c_2, c_2, c_1844])).
% 4.86/1.94  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.86/1.94  tff(c_1903, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k3_xboole_0(A_68, k3_xboole_0(A_68, B_69)))=k5_xboole_0(A_68, k3_xboole_0(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_1887, c_4])).
% 4.86/1.94  tff(c_1925, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_1903])).
% 4.86/1.94  tff(c_20, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.86/1.94  tff(c_5449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1925, c_20])).
% 4.86/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.94  
% 4.86/1.94  Inference rules
% 4.86/1.94  ----------------------
% 4.86/1.94  #Ref     : 0
% 4.86/1.94  #Sup     : 1374
% 4.86/1.94  #Fact    : 0
% 4.86/1.94  #Define  : 0
% 4.86/1.94  #Split   : 0
% 4.86/1.94  #Chain   : 0
% 4.86/1.94  #Close   : 0
% 4.86/1.94  
% 4.86/1.94  Ordering : KBO
% 4.86/1.94  
% 4.86/1.94  Simplification rules
% 4.86/1.94  ----------------------
% 4.86/1.94  #Subsume      : 28
% 4.86/1.94  #Demod        : 1370
% 4.86/1.94  #Tautology    : 831
% 4.86/1.94  #SimpNegUnit  : 0
% 4.86/1.94  #BackRed      : 14
% 4.86/1.94  
% 4.86/1.94  #Partial instantiations: 0
% 4.86/1.94  #Strategies tried      : 1
% 4.86/1.94  
% 4.86/1.94  Timing (in seconds)
% 4.86/1.94  ----------------------
% 4.86/1.94  Preprocessing        : 0.26
% 4.86/1.94  Parsing              : 0.15
% 4.86/1.94  CNF conversion       : 0.02
% 4.86/1.94  Main loop            : 0.91
% 4.86/1.94  Inferencing          : 0.27
% 4.86/1.94  Reduction            : 0.44
% 4.86/1.95  Demodulation         : 0.38
% 4.86/1.95  BG Simplification    : 0.04
% 4.86/1.95  Subsumption          : 0.11
% 4.86/1.95  Abstraction          : 0.05
% 4.86/1.95  MUC search           : 0.00
% 4.86/1.95  Cooper               : 0.00
% 4.86/1.95  Total                : 1.20
% 4.86/1.95  Index Insertion      : 0.00
% 4.86/1.95  Index Deletion       : 0.00
% 4.86/1.95  Index Matching       : 0.00
% 4.86/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------

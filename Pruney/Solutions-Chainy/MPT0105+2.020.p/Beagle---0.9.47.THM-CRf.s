%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:50 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   35 (  46 expanded)
%              Number of equality atoms :   34 (  45 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_483,plain,(
    ! [A_45,B_46,C_47] : k4_xboole_0(k3_xboole_0(A_45,B_46),C_47) = k3_xboole_0(A_45,k4_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(k4_xboole_0(A_30,B_31),C_32) = k4_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(B_34,k1_xboole_0)) = k4_xboole_0(A_33,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_6])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [B_34] : k4_xboole_0(B_34,B_34) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_10])).

tff(c_1048,plain,(
    ! [A_60,B_61] : k3_xboole_0(A_60,k4_xboole_0(B_61,k3_xboole_0(A_60,B_61))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_194])).

tff(c_1085,plain,(
    ! [A_60] : k3_xboole_0(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1048])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2860,plain,(
    ! [B_98,A_99,C_100] : k4_xboole_0(k3_xboole_0(B_98,A_99),C_100) = k3_xboole_0(A_99,k4_xboole_0(B_98,C_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_483])).

tff(c_3157,plain,(
    ! [B_104,A_105,C_106] : k3_xboole_0(B_104,k4_xboole_0(A_105,C_106)) = k3_xboole_0(A_105,k4_xboole_0(B_104,C_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2860])).

tff(c_3394,plain,(
    ! [B_34,B_104] : k3_xboole_0(B_34,k4_xboole_0(B_104,B_34)) = k3_xboole_0(B_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_3157])).

tff(c_3502,plain,(
    ! [B_107,B_108] : k3_xboole_0(B_107,k4_xboole_0(B_108,B_107)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_3394])).

tff(c_349,plain,(
    ! [A_40,B_41] : k5_xboole_0(k5_xboole_0(A_40,B_41),k3_xboole_0(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_361,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k5_xboole_0(B_41,k3_xboole_0(A_40,B_41))) = k2_xboole_0(A_40,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_18])).

tff(c_3522,plain,(
    ! [B_107,B_108] : k5_xboole_0(B_107,k5_xboole_0(k4_xboole_0(B_108,B_107),k1_xboole_0)) = k2_xboole_0(B_107,k4_xboole_0(B_108,B_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3502,c_361])).

tff(c_3610,plain,(
    ! [B_107,B_108] : k5_xboole_0(B_107,k4_xboole_0(B_108,B_107)) = k2_xboole_0(B_107,B_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16,c_3522])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_9373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3610,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.25  
% 6.06/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.26  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 6.06/2.26  
% 6.06/2.26  %Foreground sorts:
% 6.06/2.26  
% 6.06/2.26  
% 6.06/2.26  %Background operators:
% 6.06/2.26  
% 6.06/2.26  
% 6.06/2.26  %Foreground operators:
% 6.06/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.06/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.06/2.26  tff('#skF_2', type, '#skF_2': $i).
% 6.06/2.26  tff('#skF_1', type, '#skF_1': $i).
% 6.06/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.06/2.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.06/2.26  
% 6.06/2.27  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.06/2.27  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.06/2.27  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 6.06/2.27  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.06/2.27  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.06/2.27  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.06/2.27  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.06/2.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.06/2.27  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.06/2.27  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.06/2.27  tff(f_48, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.06/2.27  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.06/2.27  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.06/2.27  tff(c_14, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.06/2.27  tff(c_483, plain, (![A_45, B_46, C_47]: (k4_xboole_0(k3_xboole_0(A_45, B_46), C_47)=k3_xboole_0(A_45, k4_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.06/2.27  tff(c_130, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k4_xboole_0(A_30, B_31), C_32)=k4_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.06/2.27  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.06/2.27  tff(c_177, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k1_xboole_0))=k4_xboole_0(A_33, B_34))), inference(superposition, [status(thm), theory('equality')], [c_130, c_6])).
% 6.06/2.27  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.06/2.27  tff(c_194, plain, (![B_34]: (k4_xboole_0(B_34, B_34)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_177, c_10])).
% 6.06/2.27  tff(c_1048, plain, (![A_60, B_61]: (k3_xboole_0(A_60, k4_xboole_0(B_61, k3_xboole_0(A_60, B_61)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_483, c_194])).
% 6.06/2.27  tff(c_1085, plain, (![A_60]: (k3_xboole_0(A_60, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1048])).
% 6.06/2.27  tff(c_12, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.06/2.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.06/2.27  tff(c_2860, plain, (![B_98, A_99, C_100]: (k4_xboole_0(k3_xboole_0(B_98, A_99), C_100)=k3_xboole_0(A_99, k4_xboole_0(B_98, C_100)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_483])).
% 6.06/2.27  tff(c_3157, plain, (![B_104, A_105, C_106]: (k3_xboole_0(B_104, k4_xboole_0(A_105, C_106))=k3_xboole_0(A_105, k4_xboole_0(B_104, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2860])).
% 6.06/2.27  tff(c_3394, plain, (![B_34, B_104]: (k3_xboole_0(B_34, k4_xboole_0(B_104, B_34))=k3_xboole_0(B_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_3157])).
% 6.06/2.27  tff(c_3502, plain, (![B_107, B_108]: (k3_xboole_0(B_107, k4_xboole_0(B_108, B_107))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_3394])).
% 6.06/2.27  tff(c_349, plain, (![A_40, B_41]: (k5_xboole_0(k5_xboole_0(A_40, B_41), k3_xboole_0(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.06/2.27  tff(c_18, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.06/2.27  tff(c_361, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k5_xboole_0(B_41, k3_xboole_0(A_40, B_41)))=k2_xboole_0(A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_349, c_18])).
% 6.06/2.27  tff(c_3522, plain, (![B_107, B_108]: (k5_xboole_0(B_107, k5_xboole_0(k4_xboole_0(B_108, B_107), k1_xboole_0))=k2_xboole_0(B_107, k4_xboole_0(B_108, B_107)))), inference(superposition, [status(thm), theory('equality')], [c_3502, c_361])).
% 6.06/2.27  tff(c_3610, plain, (![B_107, B_108]: (k5_xboole_0(B_107, k4_xboole_0(B_108, B_107))=k2_xboole_0(B_107, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16, c_3522])).
% 6.06/2.27  tff(c_22, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.06/2.27  tff(c_9373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3610, c_22])).
% 6.06/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.27  
% 6.06/2.27  Inference rules
% 6.06/2.27  ----------------------
% 6.06/2.27  #Ref     : 0
% 6.06/2.27  #Sup     : 2266
% 6.06/2.27  #Fact    : 0
% 6.06/2.27  #Define  : 0
% 6.06/2.27  #Split   : 0
% 6.06/2.27  #Chain   : 0
% 6.06/2.27  #Close   : 0
% 6.06/2.27  
% 6.06/2.27  Ordering : KBO
% 6.06/2.27  
% 6.06/2.27  Simplification rules
% 6.06/2.27  ----------------------
% 6.06/2.27  #Subsume      : 8
% 6.06/2.27  #Demod        : 2276
% 6.06/2.27  #Tautology    : 1605
% 6.06/2.27  #SimpNegUnit  : 0
% 6.06/2.27  #BackRed      : 10
% 6.06/2.27  
% 6.06/2.27  #Partial instantiations: 0
% 6.06/2.27  #Strategies tried      : 1
% 6.06/2.27  
% 6.06/2.27  Timing (in seconds)
% 6.06/2.27  ----------------------
% 6.06/2.27  Preprocessing        : 0.29
% 6.06/2.27  Parsing              : 0.15
% 6.06/2.27  CNF conversion       : 0.02
% 6.06/2.27  Main loop            : 1.21
% 6.06/2.27  Inferencing          : 0.34
% 6.06/2.27  Reduction            : 0.60
% 6.06/2.27  Demodulation         : 0.50
% 6.06/2.27  BG Simplification    : 0.04
% 6.06/2.27  Subsumption          : 0.16
% 6.06/2.27  Abstraction          : 0.08
% 6.06/2.27  MUC search           : 0.00
% 6.06/2.27  Cooper               : 0.00
% 6.06/2.27  Total                : 1.53
% 6.06/2.27  Index Insertion      : 0.00
% 6.06/2.27  Index Deletion       : 0.00
% 6.06/2.27  Index Matching       : 0.00
% 6.06/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

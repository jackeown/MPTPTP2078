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
% DateTime   : Thu Dec  3 09:47:09 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   44 (  74 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  59 expanded)
%              Number of equality atoms :   28 (  58 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k5_enumset1(A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(c_20,plain,(
    ! [B_33,A_32,C_34] : k1_enumset1(B_33,A_32,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_675,plain,(
    ! [B_75,A_77,C_79,D_78,E_76] : k2_xboole_0(k2_tarski(A_77,B_75),k1_enumset1(C_79,D_78,E_76)) = k3_enumset1(A_77,B_75,C_79,D_78,E_76) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1448,plain,(
    ! [A_124,C_126,B_125,A_127,B_128] : k2_xboole_0(k2_tarski(A_124,B_128),k1_enumset1(B_125,A_127,C_126)) = k3_enumset1(A_124,B_128,A_127,B_125,C_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_675])).

tff(c_18,plain,(
    ! [A_29,C_31,B_30] : k1_enumset1(A_29,C_31,B_30) = k1_enumset1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_699,plain,(
    ! [A_29,B_75,A_77,C_31,B_30] : k2_xboole_0(k2_tarski(A_77,B_75),k1_enumset1(A_29,C_31,B_30)) = k3_enumset1(A_77,B_75,A_29,B_30,C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_675])).

tff(c_3127,plain,(
    ! [C_176,A_174,A_177,B_175,B_173] : k3_enumset1(A_174,B_173,B_175,C_176,A_177) = k3_enumset1(A_174,B_173,A_177,B_175,C_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_1448,c_699])).

tff(c_16,plain,(
    ! [A_25,B_26,C_27,D_28] : k5_enumset1(A_25,A_25,A_25,A_25,B_26,C_27,D_28) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_504,plain,(
    ! [C_67,B_68,E_70,A_71,D_69] : k5_enumset1(A_71,A_71,A_71,B_68,C_67,D_69,E_70) = k3_enumset1(A_71,B_68,C_67,D_69,E_70) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_517,plain,(
    ! [A_25,B_26,C_27,D_28] : k3_enumset1(A_25,A_25,B_26,C_27,D_28) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_504])).

tff(c_3316,plain,(
    ! [B_178,A_179,B_180,C_181] : k3_enumset1(B_178,B_178,A_179,B_180,C_181) = k2_enumset1(B_178,B_180,C_181,A_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_3127,c_517])).

tff(c_972,plain,(
    ! [C_102,B_103,A_99,A_101,B_100] : k2_xboole_0(k2_tarski(A_99,B_103),k1_enumset1(A_101,C_102,B_100)) = k3_enumset1(A_99,B_103,A_101,B_100,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_675])).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k2_xboole_0(k2_tarski(A_10,B_11),k1_enumset1(C_12,D_13,E_14)) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1051,plain,(
    ! [B_111,A_108,B_110,A_109,C_107] : k3_enumset1(A_109,B_111,A_108,C_107,B_110) = k3_enumset1(A_109,B_111,A_108,B_110,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_8])).

tff(c_1117,plain,(
    ! [A_25,B_26,D_28,C_27] : k3_enumset1(A_25,A_25,B_26,D_28,C_27) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_1051])).

tff(c_3338,plain,(
    ! [B_178,B_180,C_181,A_179] : k2_enumset1(B_178,B_180,C_181,A_179) = k2_enumset1(B_178,A_179,C_181,B_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_3316,c_1117])).

tff(c_1648,plain,(
    ! [A_138,B_139,D_140,C_141] : k3_enumset1(A_138,A_138,B_139,D_140,C_141) = k2_enumset1(A_138,B_139,C_141,D_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_1051])).

tff(c_1676,plain,(
    ! [A_138,B_139,D_140,C_141] : k2_enumset1(A_138,B_139,D_140,C_141) = k2_enumset1(A_138,B_139,C_141,D_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_1648,c_517])).

tff(c_6,plain,(
    ! [C_8,B_7,D_9,A_6] : k2_enumset1(C_8,B_7,D_9,A_6) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22])).

tff(c_1718,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_23])).

tff(c_3433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3338,c_1718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.86  
% 4.61/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.87  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.61/1.87  
% 4.61/1.87  %Foreground sorts:
% 4.61/1.87  
% 4.61/1.87  
% 4.61/1.87  %Background operators:
% 4.61/1.87  
% 4.61/1.87  
% 4.61/1.87  %Foreground operators:
% 4.61/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.61/1.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.61/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.61/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.61/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.61/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.61/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.61/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.61/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.61/1.87  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.61/1.87  
% 4.61/1.88  tff(f_45, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 4.61/1.88  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 4.61/1.88  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 4.61/1.88  tff(f_41, axiom, (![A, B, C, D]: (k5_enumset1(A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_enumset1)).
% 4.61/1.88  tff(f_39, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 4.61/1.88  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 4.61/1.88  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 4.61/1.88  tff(c_20, plain, (![B_33, A_32, C_34]: (k1_enumset1(B_33, A_32, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.61/1.88  tff(c_675, plain, (![B_75, A_77, C_79, D_78, E_76]: (k2_xboole_0(k2_tarski(A_77, B_75), k1_enumset1(C_79, D_78, E_76))=k3_enumset1(A_77, B_75, C_79, D_78, E_76))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.61/1.88  tff(c_1448, plain, (![A_124, C_126, B_125, A_127, B_128]: (k2_xboole_0(k2_tarski(A_124, B_128), k1_enumset1(B_125, A_127, C_126))=k3_enumset1(A_124, B_128, A_127, B_125, C_126))), inference(superposition, [status(thm), theory('equality')], [c_20, c_675])).
% 4.61/1.88  tff(c_18, plain, (![A_29, C_31, B_30]: (k1_enumset1(A_29, C_31, B_30)=k1_enumset1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.61/1.88  tff(c_699, plain, (![A_29, B_75, A_77, C_31, B_30]: (k2_xboole_0(k2_tarski(A_77, B_75), k1_enumset1(A_29, C_31, B_30))=k3_enumset1(A_77, B_75, A_29, B_30, C_31))), inference(superposition, [status(thm), theory('equality')], [c_18, c_675])).
% 4.61/1.88  tff(c_3127, plain, (![C_176, A_174, A_177, B_175, B_173]: (k3_enumset1(A_174, B_173, B_175, C_176, A_177)=k3_enumset1(A_174, B_173, A_177, B_175, C_176))), inference(superposition, [status(thm), theory('equality')], [c_1448, c_699])).
% 4.61/1.88  tff(c_16, plain, (![A_25, B_26, C_27, D_28]: (k5_enumset1(A_25, A_25, A_25, A_25, B_26, C_27, D_28)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.61/1.88  tff(c_504, plain, (![C_67, B_68, E_70, A_71, D_69]: (k5_enumset1(A_71, A_71, A_71, B_68, C_67, D_69, E_70)=k3_enumset1(A_71, B_68, C_67, D_69, E_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.61/1.88  tff(c_517, plain, (![A_25, B_26, C_27, D_28]: (k3_enumset1(A_25, A_25, B_26, C_27, D_28)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(superposition, [status(thm), theory('equality')], [c_16, c_504])).
% 4.61/1.88  tff(c_3316, plain, (![B_178, A_179, B_180, C_181]: (k3_enumset1(B_178, B_178, A_179, B_180, C_181)=k2_enumset1(B_178, B_180, C_181, A_179))), inference(superposition, [status(thm), theory('equality')], [c_3127, c_517])).
% 4.61/1.88  tff(c_972, plain, (![C_102, B_103, A_99, A_101, B_100]: (k2_xboole_0(k2_tarski(A_99, B_103), k1_enumset1(A_101, C_102, B_100))=k3_enumset1(A_99, B_103, A_101, B_100, C_102))), inference(superposition, [status(thm), theory('equality')], [c_18, c_675])).
% 4.61/1.88  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k2_xboole_0(k2_tarski(A_10, B_11), k1_enumset1(C_12, D_13, E_14))=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.61/1.88  tff(c_1051, plain, (![B_111, A_108, B_110, A_109, C_107]: (k3_enumset1(A_109, B_111, A_108, C_107, B_110)=k3_enumset1(A_109, B_111, A_108, B_110, C_107))), inference(superposition, [status(thm), theory('equality')], [c_972, c_8])).
% 4.61/1.88  tff(c_1117, plain, (![A_25, B_26, D_28, C_27]: (k3_enumset1(A_25, A_25, B_26, D_28, C_27)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(superposition, [status(thm), theory('equality')], [c_517, c_1051])).
% 4.61/1.88  tff(c_3338, plain, (![B_178, B_180, C_181, A_179]: (k2_enumset1(B_178, B_180, C_181, A_179)=k2_enumset1(B_178, A_179, C_181, B_180))), inference(superposition, [status(thm), theory('equality')], [c_3316, c_1117])).
% 4.61/1.88  tff(c_1648, plain, (![A_138, B_139, D_140, C_141]: (k3_enumset1(A_138, A_138, B_139, D_140, C_141)=k2_enumset1(A_138, B_139, C_141, D_140))), inference(superposition, [status(thm), theory('equality')], [c_517, c_1051])).
% 4.61/1.88  tff(c_1676, plain, (![A_138, B_139, D_140, C_141]: (k2_enumset1(A_138, B_139, D_140, C_141)=k2_enumset1(A_138, B_139, C_141, D_140))), inference(superposition, [status(thm), theory('equality')], [c_1648, c_517])).
% 4.61/1.88  tff(c_6, plain, (![C_8, B_7, D_9, A_6]: (k2_enumset1(C_8, B_7, D_9, A_6)=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.88  tff(c_22, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.61/1.88  tff(c_23, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22])).
% 4.61/1.88  tff(c_1718, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1676, c_23])).
% 4.61/1.88  tff(c_3433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3338, c_1718])).
% 4.61/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.88  
% 4.61/1.88  Inference rules
% 4.61/1.88  ----------------------
% 4.61/1.88  #Ref     : 0
% 4.61/1.88  #Sup     : 830
% 4.61/1.88  #Fact    : 0
% 4.61/1.88  #Define  : 0
% 4.61/1.88  #Split   : 0
% 4.61/1.88  #Chain   : 0
% 4.61/1.88  #Close   : 0
% 4.61/1.88  
% 4.61/1.88  Ordering : KBO
% 4.61/1.88  
% 4.61/1.88  Simplification rules
% 4.61/1.88  ----------------------
% 4.61/1.88  #Subsume      : 142
% 4.61/1.88  #Demod        : 499
% 4.61/1.88  #Tautology    : 560
% 4.61/1.88  #SimpNegUnit  : 0
% 4.61/1.88  #BackRed      : 2
% 4.61/1.88  
% 4.61/1.88  #Partial instantiations: 0
% 4.61/1.88  #Strategies tried      : 1
% 4.61/1.88  
% 4.61/1.88  Timing (in seconds)
% 4.61/1.88  ----------------------
% 4.61/1.88  Preprocessing        : 0.32
% 4.61/1.88  Parsing              : 0.17
% 4.61/1.88  CNF conversion       : 0.02
% 4.61/1.88  Main loop            : 0.77
% 4.61/1.88  Inferencing          : 0.26
% 4.61/1.88  Reduction            : 0.35
% 4.61/1.88  Demodulation         : 0.31
% 4.61/1.88  BG Simplification    : 0.03
% 4.61/1.88  Subsumption          : 0.09
% 4.61/1.88  Abstraction          : 0.04
% 4.61/1.88  MUC search           : 0.00
% 4.61/1.88  Cooper               : 0.00
% 4.61/1.88  Total                : 1.11
% 4.61/1.88  Index Insertion      : 0.00
% 4.61/1.88  Index Deletion       : 0.00
% 4.61/1.88  Index Matching       : 0.00
% 4.61/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:54 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 110 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   29 (  94 expanded)
%              Number of equality atoms :   28 (  93 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_4,plain,(
    ! [A_4,B_5,D_7,C_6] : k2_enumset1(A_4,B_5,D_7,C_6) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_8,C_10,D_11,B_9] : k2_enumset1(A_8,C_10,D_11,B_9) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] : k1_enumset1(B_2,C_3,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_187,plain,(
    ! [A_75,B_76,D_77,C_78] : k2_enumset1(A_75,B_76,D_77,C_78) = k2_enumset1(A_75,B_76,C_78,D_77) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_203,plain,(
    ! [B_76,D_77,C_78] : k2_enumset1(B_76,B_76,D_77,C_78) = k1_enumset1(B_76,C_78,D_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_18])).

tff(c_22,plain,(
    ! [C_46,E_48,A_44,B_45,D_47] : k4_enumset1(A_44,A_44,B_45,C_46,D_47,E_48) = k3_enumset1(A_44,B_45,C_46,D_47,E_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_858,plain,(
    ! [C_121,F_120,A_117,D_119,B_116,E_118] : k2_xboole_0(k3_enumset1(A_117,B_116,C_121,D_119,E_118),k1_tarski(F_120)) = k4_enumset1(A_117,B_116,C_121,D_119,E_118,F_120) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_867,plain,(
    ! [C_42,F_120,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,F_120) = k2_xboole_0(k2_enumset1(A_40,B_41,C_42,D_43),k1_tarski(F_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_858])).

tff(c_1561,plain,(
    ! [C_161,A_159,B_163,D_160,F_162] : k2_xboole_0(k2_enumset1(A_159,B_163,C_161,D_160),k1_tarski(F_162)) = k3_enumset1(A_159,B_163,C_161,D_160,F_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_867])).

tff(c_1600,plain,(
    ! [B_76,D_77,C_78,F_162] : k3_enumset1(B_76,B_76,D_77,C_78,F_162) = k2_xboole_0(k1_enumset1(B_76,C_78,D_77),k1_tarski(F_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_1561])).

tff(c_1614,plain,(
    ! [B_164,C_165,D_166,F_167] : k2_xboole_0(k1_enumset1(B_164,C_165,D_166),k1_tarski(F_167)) = k2_enumset1(B_164,D_166,C_165,F_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1600])).

tff(c_2309,plain,(
    ! [B_208,C_209,A_210,F_211] : k2_xboole_0(k1_enumset1(B_208,C_209,A_210),k1_tarski(F_211)) = k2_enumset1(A_210,C_209,B_208,F_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1614])).

tff(c_1612,plain,(
    ! [B_76,C_78,D_77,F_162] : k2_xboole_0(k1_enumset1(B_76,C_78,D_77),k1_tarski(F_162)) = k2_enumset1(B_76,D_77,C_78,F_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1600])).

tff(c_2315,plain,(
    ! [B_208,A_210,C_209,F_211] : k2_enumset1(B_208,A_210,C_209,F_211) = k2_enumset1(A_210,C_209,B_208,F_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_2309,c_1612])).

tff(c_28,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_28])).

tff(c_30,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_29])).

tff(c_2363,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2315,c_2315,c_30])).

tff(c_2366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_4,c_2363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:36:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.67  
% 3.89/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.68  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.89/1.68  
% 3.89/1.68  %Foreground sorts:
% 3.89/1.68  
% 3.89/1.68  
% 3.89/1.68  %Background operators:
% 3.89/1.68  
% 3.89/1.68  
% 3.89/1.68  %Foreground operators:
% 3.89/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.89/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.89/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.89/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.89/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.89/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.89/1.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.89/1.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.89/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.89/1.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.89/1.68  
% 3.89/1.69  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 3.89/1.69  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 3.89/1.69  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 3.89/1.69  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.89/1.69  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.89/1.69  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.89/1.69  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 3.89/1.69  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 3.89/1.69  tff(c_4, plain, (![A_4, B_5, D_7, C_6]: (k2_enumset1(A_4, B_5, D_7, C_6)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.89/1.69  tff(c_6, plain, (![A_8, C_10, D_11, B_9]: (k2_enumset1(A_8, C_10, D_11, B_9)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.69  tff(c_2, plain, (![B_2, C_3, A_1]: (k1_enumset1(B_2, C_3, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.89/1.69  tff(c_20, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.89/1.69  tff(c_187, plain, (![A_75, B_76, D_77, C_78]: (k2_enumset1(A_75, B_76, D_77, C_78)=k2_enumset1(A_75, B_76, C_78, D_77))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.89/1.69  tff(c_18, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.69  tff(c_203, plain, (![B_76, D_77, C_78]: (k2_enumset1(B_76, B_76, D_77, C_78)=k1_enumset1(B_76, C_78, D_77))), inference(superposition, [status(thm), theory('equality')], [c_187, c_18])).
% 3.89/1.69  tff(c_22, plain, (![C_46, E_48, A_44, B_45, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, E_48)=k3_enumset1(A_44, B_45, C_46, D_47, E_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.89/1.69  tff(c_858, plain, (![C_121, F_120, A_117, D_119, B_116, E_118]: (k2_xboole_0(k3_enumset1(A_117, B_116, C_121, D_119, E_118), k1_tarski(F_120))=k4_enumset1(A_117, B_116, C_121, D_119, E_118, F_120))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.89/1.69  tff(c_867, plain, (![C_42, F_120, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, F_120)=k2_xboole_0(k2_enumset1(A_40, B_41, C_42, D_43), k1_tarski(F_120)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_858])).
% 3.89/1.69  tff(c_1561, plain, (![C_161, A_159, B_163, D_160, F_162]: (k2_xboole_0(k2_enumset1(A_159, B_163, C_161, D_160), k1_tarski(F_162))=k3_enumset1(A_159, B_163, C_161, D_160, F_162))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_867])).
% 3.89/1.69  tff(c_1600, plain, (![B_76, D_77, C_78, F_162]: (k3_enumset1(B_76, B_76, D_77, C_78, F_162)=k2_xboole_0(k1_enumset1(B_76, C_78, D_77), k1_tarski(F_162)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_1561])).
% 3.89/1.69  tff(c_1614, plain, (![B_164, C_165, D_166, F_167]: (k2_xboole_0(k1_enumset1(B_164, C_165, D_166), k1_tarski(F_167))=k2_enumset1(B_164, D_166, C_165, F_167))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1600])).
% 3.89/1.69  tff(c_2309, plain, (![B_208, C_209, A_210, F_211]: (k2_xboole_0(k1_enumset1(B_208, C_209, A_210), k1_tarski(F_211))=k2_enumset1(A_210, C_209, B_208, F_211))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1614])).
% 3.89/1.69  tff(c_1612, plain, (![B_76, C_78, D_77, F_162]: (k2_xboole_0(k1_enumset1(B_76, C_78, D_77), k1_tarski(F_162))=k2_enumset1(B_76, D_77, C_78, F_162))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1600])).
% 3.89/1.69  tff(c_2315, plain, (![B_208, A_210, C_209, F_211]: (k2_enumset1(B_208, A_210, C_209, F_211)=k2_enumset1(A_210, C_209, B_208, F_211))), inference(superposition, [status(thm), theory('equality')], [c_2309, c_1612])).
% 3.89/1.69  tff(c_28, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.89/1.69  tff(c_29, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_28])).
% 3.89/1.69  tff(c_30, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_29])).
% 3.89/1.69  tff(c_2363, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2315, c_2315, c_30])).
% 3.89/1.69  tff(c_2366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_4, c_2363])).
% 3.89/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.69  
% 3.89/1.69  Inference rules
% 3.89/1.69  ----------------------
% 3.89/1.69  #Ref     : 0
% 3.89/1.69  #Sup     : 586
% 3.89/1.69  #Fact    : 0
% 3.89/1.69  #Define  : 0
% 3.89/1.69  #Split   : 0
% 3.89/1.69  #Chain   : 0
% 3.89/1.69  #Close   : 0
% 3.89/1.69  
% 3.89/1.69  Ordering : KBO
% 3.89/1.69  
% 3.89/1.69  Simplification rules
% 3.89/1.69  ----------------------
% 3.89/1.69  #Subsume      : 119
% 3.89/1.69  #Demod        : 338
% 3.89/1.69  #Tautology    : 347
% 3.89/1.69  #SimpNegUnit  : 0
% 3.89/1.69  #BackRed      : 1
% 3.89/1.69  
% 3.89/1.69  #Partial instantiations: 0
% 3.89/1.69  #Strategies tried      : 1
% 3.89/1.69  
% 3.89/1.69  Timing (in seconds)
% 3.89/1.69  ----------------------
% 3.89/1.69  Preprocessing        : 0.30
% 3.89/1.69  Parsing              : 0.16
% 3.89/1.69  CNF conversion       : 0.02
% 3.89/1.69  Main loop            : 0.58
% 3.89/1.69  Inferencing          : 0.20
% 3.89/1.69  Reduction            : 0.26
% 3.89/1.69  Demodulation         : 0.23
% 3.89/1.69  BG Simplification    : 0.03
% 3.89/1.69  Subsumption          : 0.07
% 3.89/1.69  Abstraction          : 0.04
% 3.89/1.69  MUC search           : 0.00
% 3.89/1.69  Cooper               : 0.00
% 3.89/1.69  Total                : 0.90
% 3.89/1.69  Index Insertion      : 0.00
% 3.89/1.69  Index Deletion       : 0.00
% 3.89/1.69  Index Matching       : 0.00
% 3.89/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------

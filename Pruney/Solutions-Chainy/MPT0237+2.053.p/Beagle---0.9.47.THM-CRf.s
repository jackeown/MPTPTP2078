%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:52 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :   30 (  38 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_6,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_14,B_15,C_16,D_17] : k3_enumset1(A_14,A_14,B_15,C_16,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k4_enumset1(A_18,A_18,B_19,C_20,D_21,E_22) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] : k5_enumset1(A_23,A_23,B_24,C_25,D_26,E_27,F_28) = k4_enumset1(A_23,B_24,C_25,D_26,E_27,F_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [B_59,A_61,G_56,E_57,F_55,C_60,D_58] : k2_xboole_0(k4_enumset1(A_61,B_59,C_60,D_58,E_57,F_55),k1_tarski(G_56)) = k5_enumset1(A_61,B_59,C_60,D_58,E_57,F_55,G_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [E_22,D_21,G_56,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,D_21,E_22,G_56) = k2_xboole_0(k3_enumset1(A_18,B_19,C_20,D_21,E_22),k1_tarski(G_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_103])).

tff(c_116,plain,(
    ! [D_66,B_67,G_64,E_65,C_63,A_62] : k2_xboole_0(k3_enumset1(A_62,B_67,C_63,D_66,E_65),k1_tarski(G_64)) = k4_enumset1(A_62,B_67,C_63,D_66,E_65,G_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_112])).

tff(c_125,plain,(
    ! [G_64,C_16,D_17,A_14,B_15] : k4_enumset1(A_14,A_14,B_15,C_16,D_17,G_64) = k2_xboole_0(k2_enumset1(A_14,B_15,C_16,D_17),k1_tarski(G_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_116])).

tff(c_129,plain,(
    ! [C_70,A_72,G_69,D_68,B_71] : k2_xboole_0(k2_enumset1(A_72,B_71,C_70,D_68),k1_tarski(G_69)) = k3_enumset1(A_72,B_71,C_70,D_68,G_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_125])).

tff(c_138,plain,(
    ! [A_11,B_12,C_13,G_69] : k3_enumset1(A_11,A_11,B_12,C_13,G_69) = k2_xboole_0(k1_enumset1(A_11,B_12,C_13),k1_tarski(G_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_129])).

tff(c_142,plain,(
    ! [A_73,B_74,C_75,G_76] : k2_xboole_0(k1_enumset1(A_73,B_74,C_75),k1_tarski(G_76)) = k2_enumset1(A_73,B_74,C_75,G_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138])).

tff(c_151,plain,(
    ! [A_9,B_10,G_76] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(G_76)) = k2_enumset1(A_9,A_9,B_10,G_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_142])).

tff(c_155,plain,(
    ! [A_77,B_78,G_79] : k2_xboole_0(k2_tarski(A_77,B_78),k1_tarski(G_79)) = k1_enumset1(A_77,B_78,G_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_164,plain,(
    ! [A_8,G_79] : k2_xboole_0(k1_tarski(A_8),k1_tarski(G_79)) = k1_enumset1(A_8,A_8,G_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_155])).

tff(c_167,plain,(
    ! [A_8,G_79] : k2_xboole_0(k1_tarski(A_8),k1_tarski(G_79)) = k2_tarski(A_8,G_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_16,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:39:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.16  
% 1.63/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.16  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.63/1.16  
% 1.63/1.16  %Foreground sorts:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Background operators:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Foreground operators:
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.63/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.63/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.63/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.63/1.16  
% 1.63/1.17  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.63/1.17  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.63/1.17  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.63/1.17  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.63/1.17  tff(f_37, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.63/1.17  tff(f_39, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.63/1.17  tff(f_27, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 1.63/1.17  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.63/1.17  tff(f_44, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 1.63/1.17  tff(c_6, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.17  tff(c_4, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.17  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.63/1.17  tff(c_10, plain, (![A_14, B_15, C_16, D_17]: (k3_enumset1(A_14, A_14, B_15, C_16, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.17  tff(c_12, plain, (![E_22, D_21, A_18, C_20, B_19]: (k4_enumset1(A_18, A_18, B_19, C_20, D_21, E_22)=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.17  tff(c_14, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (k5_enumset1(A_23, A_23, B_24, C_25, D_26, E_27, F_28)=k4_enumset1(A_23, B_24, C_25, D_26, E_27, F_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.17  tff(c_103, plain, (![B_59, A_61, G_56, E_57, F_55, C_60, D_58]: (k2_xboole_0(k4_enumset1(A_61, B_59, C_60, D_58, E_57, F_55), k1_tarski(G_56))=k5_enumset1(A_61, B_59, C_60, D_58, E_57, F_55, G_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.17  tff(c_112, plain, (![E_22, D_21, G_56, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, D_21, E_22, G_56)=k2_xboole_0(k3_enumset1(A_18, B_19, C_20, D_21, E_22), k1_tarski(G_56)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_103])).
% 1.63/1.17  tff(c_116, plain, (![D_66, B_67, G_64, E_65, C_63, A_62]: (k2_xboole_0(k3_enumset1(A_62, B_67, C_63, D_66, E_65), k1_tarski(G_64))=k4_enumset1(A_62, B_67, C_63, D_66, E_65, G_64))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_112])).
% 1.63/1.17  tff(c_125, plain, (![G_64, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, G_64)=k2_xboole_0(k2_enumset1(A_14, B_15, C_16, D_17), k1_tarski(G_64)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_116])).
% 1.63/1.17  tff(c_129, plain, (![C_70, A_72, G_69, D_68, B_71]: (k2_xboole_0(k2_enumset1(A_72, B_71, C_70, D_68), k1_tarski(G_69))=k3_enumset1(A_72, B_71, C_70, D_68, G_69))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_125])).
% 1.63/1.17  tff(c_138, plain, (![A_11, B_12, C_13, G_69]: (k3_enumset1(A_11, A_11, B_12, C_13, G_69)=k2_xboole_0(k1_enumset1(A_11, B_12, C_13), k1_tarski(G_69)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_129])).
% 1.63/1.17  tff(c_142, plain, (![A_73, B_74, C_75, G_76]: (k2_xboole_0(k1_enumset1(A_73, B_74, C_75), k1_tarski(G_76))=k2_enumset1(A_73, B_74, C_75, G_76))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138])).
% 1.89/1.17  tff(c_151, plain, (![A_9, B_10, G_76]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(G_76))=k2_enumset1(A_9, A_9, B_10, G_76))), inference(superposition, [status(thm), theory('equality')], [c_6, c_142])).
% 1.89/1.17  tff(c_155, plain, (![A_77, B_78, G_79]: (k2_xboole_0(k2_tarski(A_77, B_78), k1_tarski(G_79))=k1_enumset1(A_77, B_78, G_79))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_151])).
% 1.89/1.17  tff(c_164, plain, (![A_8, G_79]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(G_79))=k1_enumset1(A_8, A_8, G_79))), inference(superposition, [status(thm), theory('equality')], [c_4, c_155])).
% 1.89/1.17  tff(c_167, plain, (![A_8, G_79]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(G_79))=k2_tarski(A_8, G_79))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_164])).
% 1.89/1.17  tff(c_16, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.89/1.17  tff(c_18, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.17  tff(c_19, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 1.89/1.17  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_19])).
% 1.89/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  Inference rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Ref     : 0
% 1.89/1.17  #Sup     : 34
% 1.89/1.17  #Fact    : 0
% 1.89/1.17  #Define  : 0
% 1.89/1.17  #Split   : 0
% 1.89/1.17  #Chain   : 0
% 1.89/1.17  #Close   : 0
% 1.89/1.17  
% 1.89/1.17  Ordering : KBO
% 1.89/1.17  
% 1.89/1.17  Simplification rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Subsume      : 0
% 1.89/1.17  #Demod        : 7
% 1.89/1.17  #Tautology    : 28
% 1.89/1.17  #SimpNegUnit  : 0
% 1.89/1.17  #BackRed      : 1
% 1.89/1.17  
% 1.89/1.17  #Partial instantiations: 0
% 1.89/1.17  #Strategies tried      : 1
% 1.89/1.17  
% 1.89/1.17  Timing (in seconds)
% 1.89/1.17  ----------------------
% 1.89/1.18  Preprocessing        : 0.28
% 1.89/1.18  Parsing              : 0.15
% 1.89/1.18  CNF conversion       : 0.01
% 1.89/1.18  Main loop            : 0.12
% 1.89/1.18  Inferencing          : 0.06
% 1.89/1.18  Reduction            : 0.04
% 1.89/1.18  Demodulation         : 0.03
% 1.89/1.18  BG Simplification    : 0.01
% 1.89/1.18  Subsumption          : 0.01
% 1.89/1.18  Abstraction          : 0.01
% 1.89/1.18  MUC search           : 0.00
% 1.89/1.18  Cooper               : 0.00
% 1.89/1.18  Total                : 0.43
% 1.89/1.18  Index Insertion      : 0.00
% 1.89/1.18  Index Deletion       : 0.00
% 1.89/1.18  Index Matching       : 0.00
% 1.89/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

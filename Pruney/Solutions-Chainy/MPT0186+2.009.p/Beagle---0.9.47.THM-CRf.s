%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:48 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 298 expanded)
%              Number of leaves         :   23 ( 111 expanded)
%              Depth                    :   12
%              Number of atoms          :   37 ( 284 expanded)
%              Number of equality atoms :   36 ( 283 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_4,plain,(
    ! [A_4,B_5,D_7,C_6] : k2_enumset1(A_4,B_5,D_7,C_6) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_19,B_20,C_21,D_22] : k3_enumset1(A_19,A_19,B_20,C_21,D_22) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] : k1_enumset1(B_2,C_3,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] : k5_enumset1(A_28,A_28,B_29,C_30,D_31,E_32,F_33) = k4_enumset1(A_28,B_29,C_30,D_31,E_32,F_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_47,B_48,D_49,C_50] : k2_enumset1(A_47,B_48,D_49,C_50) = k2_enumset1(A_47,B_48,C_50,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_16,B_17,C_18] : k2_enumset1(A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [B_48,D_49,C_50] : k2_enumset1(B_48,B_48,D_49,C_50) = k1_enumset1(B_48,C_50,D_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_8])).

tff(c_16,plain,(
    ! [D_37,A_34,F_39,B_35,G_40,C_36,E_38] : k6_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,F_39,G_40) = k5_enumset1(A_34,B_35,C_36,D_37,E_38,F_39,G_40) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_419,plain,(
    ! [C_89,D_92,F_85,B_88,H_91,G_90,E_87,A_86] : k2_xboole_0(k3_enumset1(A_86,B_88,C_89,D_92,E_87),k1_enumset1(F_85,G_90,H_91)) = k6_enumset1(A_86,B_88,C_89,D_92,E_87,F_85,G_90,H_91) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_446,plain,(
    ! [A_19,F_85,H_91,G_90,C_21,D_22,B_20] : k6_enumset1(A_19,A_19,B_20,C_21,D_22,F_85,G_90,H_91) = k2_xboole_0(k2_enumset1(A_19,B_20,C_21,D_22),k1_enumset1(F_85,G_90,H_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_419])).

tff(c_457,plain,(
    ! [G_99,B_96,F_94,C_93,D_98,A_97,H_95] : k2_xboole_0(k2_enumset1(A_97,B_96,C_93,D_98),k1_enumset1(F_94,G_99,H_95)) = k5_enumset1(A_97,B_96,C_93,D_98,F_94,G_99,H_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_446])).

tff(c_484,plain,(
    ! [G_99,D_49,F_94,C_50,B_48,H_95] : k5_enumset1(B_48,B_48,D_49,C_50,F_94,G_99,H_95) = k2_xboole_0(k1_enumset1(B_48,C_50,D_49),k1_enumset1(F_94,G_99,H_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_457])).

tff(c_504,plain,(
    ! [H_100,C_102,B_103,F_105,D_101,G_104] : k2_xboole_0(k1_enumset1(B_103,C_102,D_101),k1_enumset1(F_105,G_104,H_100)) = k4_enumset1(B_103,D_101,C_102,F_105,G_104,H_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_484])).

tff(c_798,plain,(
    ! [C_140,A_141,C_136,D_137,B_138,B_139] : k2_xboole_0(k1_enumset1(B_138,C_136,D_137),k1_enumset1(A_141,B_139,C_140)) = k4_enumset1(B_138,D_137,C_136,B_139,C_140,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_504])).

tff(c_549,plain,(
    ! [H_100,B_2,C_3,A_1,F_105,G_104] : k2_xboole_0(k1_enumset1(B_2,C_3,A_1),k1_enumset1(F_105,G_104,H_100)) = k4_enumset1(A_1,C_3,B_2,F_105,G_104,H_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_504])).

tff(c_868,plain,(
    ! [B_144,C_143,D_147,A_142,C_145,B_146] : k4_enumset1(D_147,C_143,B_146,A_142,B_144,C_145) = k4_enumset1(B_146,D_147,C_143,B_144,C_145,A_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_798,c_549])).

tff(c_12,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] : k4_enumset1(A_23,A_23,B_24,C_25,D_26,E_27) = k3_enumset1(A_23,B_24,C_25,D_26,E_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_963,plain,(
    ! [B_148,D_150,C_152,C_149,A_151] : k4_enumset1(D_150,C_149,D_150,A_151,B_148,C_152) = k3_enumset1(D_150,C_149,B_148,C_152,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_12])).

tff(c_561,plain,(
    ! [C_110,H_109,A_111,G_106,B_108,F_107] : k2_xboole_0(k1_enumset1(B_108,C_110,A_111),k1_enumset1(F_107,G_106,H_109)) = k4_enumset1(A_111,C_110,B_108,F_107,G_106,H_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_504])).

tff(c_502,plain,(
    ! [G_99,D_49,F_94,C_50,B_48,H_95] : k2_xboole_0(k1_enumset1(B_48,C_50,D_49),k1_enumset1(F_94,G_99,H_95)) = k4_enumset1(B_48,D_49,C_50,F_94,G_99,H_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_484])).

tff(c_625,plain,(
    ! [C_115,H_113,A_116,G_112,F_117,B_114] : k4_enumset1(B_114,A_116,C_115,F_117,G_112,H_113) = k4_enumset1(A_116,C_115,B_114,F_117,G_112,H_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_502])).

tff(c_641,plain,(
    ! [C_115,H_113,G_112,F_117,B_114] : k4_enumset1(B_114,C_115,C_115,F_117,G_112,H_113) = k3_enumset1(C_115,B_114,F_117,G_112,H_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_12])).

tff(c_979,plain,(
    ! [D_150,B_148,C_152,A_151] : k3_enumset1(D_150,D_150,B_148,C_152,A_151) = k3_enumset1(D_150,D_150,A_151,B_148,C_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_963,c_641])).

tff(c_1022,plain,(
    ! [D_150,B_148,C_152,A_151] : k2_enumset1(D_150,B_148,C_152,A_151) = k2_enumset1(D_150,A_151,B_148,C_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_979])).

tff(c_18,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_18])).

tff(c_1028,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_1022,c_1022,c_19])).

tff(c_1031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:39:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.48  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.20/1.48  
% 3.20/1.48  %Foreground sorts:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Background operators:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Foreground operators:
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.48  
% 3.20/1.50  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 3.20/1.50  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.20/1.50  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 3.20/1.50  tff(f_39, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.20/1.50  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.20/1.50  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.20/1.50  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 3.20/1.50  tff(f_37, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.20/1.50  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 3.20/1.50  tff(c_4, plain, (![A_4, B_5, D_7, C_6]: (k2_enumset1(A_4, B_5, D_7, C_6)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.50  tff(c_10, plain, (![A_19, B_20, C_21, D_22]: (k3_enumset1(A_19, A_19, B_20, C_21, D_22)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.50  tff(c_2, plain, (![B_2, C_3, A_1]: (k1_enumset1(B_2, C_3, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.50  tff(c_14, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (k5_enumset1(A_28, A_28, B_29, C_30, D_31, E_32, F_33)=k4_enumset1(A_28, B_29, C_30, D_31, E_32, F_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.50  tff(c_58, plain, (![A_47, B_48, D_49, C_50]: (k2_enumset1(A_47, B_48, D_49, C_50)=k2_enumset1(A_47, B_48, C_50, D_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.50  tff(c_8, plain, (![A_16, B_17, C_18]: (k2_enumset1(A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.50  tff(c_74, plain, (![B_48, D_49, C_50]: (k2_enumset1(B_48, B_48, D_49, C_50)=k1_enumset1(B_48, C_50, D_49))), inference(superposition, [status(thm), theory('equality')], [c_58, c_8])).
% 3.20/1.50  tff(c_16, plain, (![D_37, A_34, F_39, B_35, G_40, C_36, E_38]: (k6_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, F_39, G_40)=k5_enumset1(A_34, B_35, C_36, D_37, E_38, F_39, G_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.50  tff(c_419, plain, (![C_89, D_92, F_85, B_88, H_91, G_90, E_87, A_86]: (k2_xboole_0(k3_enumset1(A_86, B_88, C_89, D_92, E_87), k1_enumset1(F_85, G_90, H_91))=k6_enumset1(A_86, B_88, C_89, D_92, E_87, F_85, G_90, H_91))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.50  tff(c_446, plain, (![A_19, F_85, H_91, G_90, C_21, D_22, B_20]: (k6_enumset1(A_19, A_19, B_20, C_21, D_22, F_85, G_90, H_91)=k2_xboole_0(k2_enumset1(A_19, B_20, C_21, D_22), k1_enumset1(F_85, G_90, H_91)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_419])).
% 3.20/1.50  tff(c_457, plain, (![G_99, B_96, F_94, C_93, D_98, A_97, H_95]: (k2_xboole_0(k2_enumset1(A_97, B_96, C_93, D_98), k1_enumset1(F_94, G_99, H_95))=k5_enumset1(A_97, B_96, C_93, D_98, F_94, G_99, H_95))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_446])).
% 3.20/1.50  tff(c_484, plain, (![G_99, D_49, F_94, C_50, B_48, H_95]: (k5_enumset1(B_48, B_48, D_49, C_50, F_94, G_99, H_95)=k2_xboole_0(k1_enumset1(B_48, C_50, D_49), k1_enumset1(F_94, G_99, H_95)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_457])).
% 3.20/1.50  tff(c_504, plain, (![H_100, C_102, B_103, F_105, D_101, G_104]: (k2_xboole_0(k1_enumset1(B_103, C_102, D_101), k1_enumset1(F_105, G_104, H_100))=k4_enumset1(B_103, D_101, C_102, F_105, G_104, H_100))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_484])).
% 3.20/1.50  tff(c_798, plain, (![C_140, A_141, C_136, D_137, B_138, B_139]: (k2_xboole_0(k1_enumset1(B_138, C_136, D_137), k1_enumset1(A_141, B_139, C_140))=k4_enumset1(B_138, D_137, C_136, B_139, C_140, A_141))), inference(superposition, [status(thm), theory('equality')], [c_2, c_504])).
% 3.20/1.50  tff(c_549, plain, (![H_100, B_2, C_3, A_1, F_105, G_104]: (k2_xboole_0(k1_enumset1(B_2, C_3, A_1), k1_enumset1(F_105, G_104, H_100))=k4_enumset1(A_1, C_3, B_2, F_105, G_104, H_100))), inference(superposition, [status(thm), theory('equality')], [c_2, c_504])).
% 3.20/1.50  tff(c_868, plain, (![B_144, C_143, D_147, A_142, C_145, B_146]: (k4_enumset1(D_147, C_143, B_146, A_142, B_144, C_145)=k4_enumset1(B_146, D_147, C_143, B_144, C_145, A_142))), inference(superposition, [status(thm), theory('equality')], [c_798, c_549])).
% 3.20/1.50  tff(c_12, plain, (![A_23, B_24, D_26, C_25, E_27]: (k4_enumset1(A_23, A_23, B_24, C_25, D_26, E_27)=k3_enumset1(A_23, B_24, C_25, D_26, E_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.50  tff(c_963, plain, (![B_148, D_150, C_152, C_149, A_151]: (k4_enumset1(D_150, C_149, D_150, A_151, B_148, C_152)=k3_enumset1(D_150, C_149, B_148, C_152, A_151))), inference(superposition, [status(thm), theory('equality')], [c_868, c_12])).
% 3.20/1.50  tff(c_561, plain, (![C_110, H_109, A_111, G_106, B_108, F_107]: (k2_xboole_0(k1_enumset1(B_108, C_110, A_111), k1_enumset1(F_107, G_106, H_109))=k4_enumset1(A_111, C_110, B_108, F_107, G_106, H_109))), inference(superposition, [status(thm), theory('equality')], [c_2, c_504])).
% 3.20/1.50  tff(c_502, plain, (![G_99, D_49, F_94, C_50, B_48, H_95]: (k2_xboole_0(k1_enumset1(B_48, C_50, D_49), k1_enumset1(F_94, G_99, H_95))=k4_enumset1(B_48, D_49, C_50, F_94, G_99, H_95))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_484])).
% 3.20/1.50  tff(c_625, plain, (![C_115, H_113, A_116, G_112, F_117, B_114]: (k4_enumset1(B_114, A_116, C_115, F_117, G_112, H_113)=k4_enumset1(A_116, C_115, B_114, F_117, G_112, H_113))), inference(superposition, [status(thm), theory('equality')], [c_561, c_502])).
% 3.20/1.50  tff(c_641, plain, (![C_115, H_113, G_112, F_117, B_114]: (k4_enumset1(B_114, C_115, C_115, F_117, G_112, H_113)=k3_enumset1(C_115, B_114, F_117, G_112, H_113))), inference(superposition, [status(thm), theory('equality')], [c_625, c_12])).
% 3.20/1.50  tff(c_979, plain, (![D_150, B_148, C_152, A_151]: (k3_enumset1(D_150, D_150, B_148, C_152, A_151)=k3_enumset1(D_150, D_150, A_151, B_148, C_152))), inference(superposition, [status(thm), theory('equality')], [c_963, c_641])).
% 3.20/1.50  tff(c_1022, plain, (![D_150, B_148, C_152, A_151]: (k2_enumset1(D_150, B_148, C_152, A_151)=k2_enumset1(D_150, A_151, B_148, C_152))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_979])).
% 3.20/1.50  tff(c_18, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.20/1.50  tff(c_19, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_18])).
% 3.20/1.50  tff(c_1028, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_1022, c_1022, c_19])).
% 3.20/1.50  tff(c_1031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_1028])).
% 3.20/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  Inference rules
% 3.20/1.50  ----------------------
% 3.20/1.50  #Ref     : 0
% 3.20/1.50  #Sup     : 282
% 3.20/1.50  #Fact    : 0
% 3.20/1.50  #Define  : 0
% 3.20/1.50  #Split   : 0
% 3.20/1.50  #Chain   : 0
% 3.20/1.50  #Close   : 0
% 3.20/1.50  
% 3.20/1.50  Ordering : KBO
% 3.20/1.50  
% 3.20/1.50  Simplification rules
% 3.20/1.50  ----------------------
% 3.20/1.50  #Subsume      : 60
% 3.20/1.50  #Demod        : 53
% 3.20/1.50  #Tautology    : 102
% 3.20/1.50  #SimpNegUnit  : 0
% 3.20/1.50  #BackRed      : 1
% 3.20/1.50  
% 3.20/1.50  #Partial instantiations: 0
% 3.20/1.50  #Strategies tried      : 1
% 3.20/1.50  
% 3.20/1.50  Timing (in seconds)
% 3.20/1.50  ----------------------
% 3.20/1.50  Preprocessing        : 0.30
% 3.20/1.50  Parsing              : 0.16
% 3.20/1.50  CNF conversion       : 0.02
% 3.20/1.50  Main loop            : 0.43
% 3.20/1.50  Inferencing          : 0.16
% 3.20/1.50  Reduction            : 0.18
% 3.20/1.50  Demodulation         : 0.15
% 3.20/1.50  BG Simplification    : 0.02
% 3.20/1.50  Subsumption          : 0.05
% 3.20/1.50  Abstraction          : 0.03
% 3.20/1.50  MUC search           : 0.00
% 3.20/1.50  Cooper               : 0.00
% 3.20/1.50  Total                : 0.75
% 3.20/1.50  Index Insertion      : 0.00
% 3.20/1.50  Index Deletion       : 0.00
% 3.20/1.50  Index Matching       : 0.00
% 3.20/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

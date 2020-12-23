%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:49 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   44 (  66 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :   28 (  50 expanded)
%              Number of equality atoms :   27 (  49 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_16,plain,(
    ! [B_37,A_36,C_38] : k1_enumset1(B_37,A_36,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] : k5_enumset1(A_23,A_23,B_24,C_25,D_26,E_27,F_28) = k4_enumset1(A_23,B_24,C_25,D_26,E_27,F_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [G_35,E_33,A_29,F_34,D_32,C_31,B_30] : k6_enumset1(A_29,A_29,B_30,C_31,D_32,E_33,F_34,G_35) = k5_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_14,B_15,C_16,D_17] : k3_enumset1(A_14,A_14,B_15,C_16,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    ! [C_75,H_74,F_72,E_70,G_69,A_73,D_71,B_76] : k2_xboole_0(k3_enumset1(A_73,B_76,C_75,D_71,E_70),k1_enumset1(F_72,G_69,H_74)) = k6_enumset1(A_73,B_76,C_75,D_71,E_70,F_72,G_69,H_74) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [H_74,F_72,C_16,G_69,D_17,A_14,B_15] : k6_enumset1(A_14,A_14,B_15,C_16,D_17,F_72,G_69,H_74) = k2_xboole_0(k2_enumset1(A_14,B_15,C_16,D_17),k1_enumset1(F_72,G_69,H_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_152,plain,(
    ! [G_87,D_85,F_86,H_91,B_89,C_88,A_90] : k2_xboole_0(k2_enumset1(A_90,B_89,C_88,D_85),k1_enumset1(F_86,G_87,H_91)) = k5_enumset1(A_90,B_89,C_88,D_85,F_86,G_87,H_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_115])).

tff(c_161,plain,(
    ! [G_87,F_86,H_91,B_12,A_11,C_13] : k5_enumset1(A_11,A_11,B_12,C_13,F_86,G_87,H_91) = k2_xboole_0(k1_enumset1(A_11,B_12,C_13),k1_enumset1(F_86,G_87,H_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_152])).

tff(c_171,plain,(
    ! [A_96,F_95,H_92,B_97,C_93,G_94] : k2_xboole_0(k1_enumset1(A_96,B_97,C_93),k1_enumset1(F_95,G_94,H_92)) = k4_enumset1(A_96,B_97,C_93,F_95,G_94,H_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_161])).

tff(c_255,plain,(
    ! [C_115,A_112,B_110,A_111,B_114,C_113] : k2_xboole_0(k1_enumset1(A_111,B_110,C_113),k1_enumset1(B_114,A_112,C_115)) = k4_enumset1(A_111,B_110,C_113,A_112,B_114,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_171])).

tff(c_180,plain,(
    ! [A_36,F_95,H_92,C_38,B_37,G_94] : k2_xboole_0(k1_enumset1(B_37,A_36,C_38),k1_enumset1(F_95,G_94,H_92)) = k4_enumset1(A_36,B_37,C_38,F_95,G_94,H_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_171])).

tff(c_290,plain,(
    ! [B_118,A_119,A_121,B_116,C_120,C_117] : k4_enumset1(B_118,A_119,C_117,B_116,A_121,C_120) = k4_enumset1(A_119,B_118,C_117,A_121,B_116,C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_180])).

tff(c_10,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k4_enumset1(A_18,A_18,B_19,C_20,D_21,E_22) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_361,plain,(
    ! [B_126,A_122,B_125,C_123,C_124] : k4_enumset1(B_126,B_126,C_124,B_125,A_122,C_123) = k3_enumset1(B_126,C_124,A_122,B_125,C_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_10])).

tff(c_394,plain,(
    ! [A_127,C_130,B_131,C_129,B_128] : k3_enumset1(B_131,C_130,B_128,A_127,C_129) = k3_enumset1(B_131,C_130,A_127,B_128,C_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_10])).

tff(c_453,plain,(
    ! [C_132,B_133,A_134,C_135] : k3_enumset1(C_132,C_132,B_133,A_134,C_135) = k2_enumset1(C_132,A_134,B_133,C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_8])).

tff(c_471,plain,(
    ! [C_132,B_133,A_134,C_135] : k2_enumset1(C_132,B_133,A_134,C_135) = k2_enumset1(C_132,A_134,B_133,C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_8])).

tff(c_18,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:22:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.79  
% 3.12/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.79  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.12/1.79  
% 3.12/1.79  %Foreground sorts:
% 3.12/1.79  
% 3.12/1.79  
% 3.12/1.79  %Background operators:
% 3.12/1.79  
% 3.12/1.79  
% 3.12/1.79  %Foreground operators:
% 3.12/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.12/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.12/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.79  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.79  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.79  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.79  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.79  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.79  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.79  
% 3.12/1.81  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 3.12/1.81  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.12/1.81  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.12/1.81  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.12/1.81  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.12/1.81  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 3.12/1.81  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.12/1.81  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 3.12/1.81  tff(c_16, plain, (![B_37, A_36, C_38]: (k1_enumset1(B_37, A_36, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.81  tff(c_12, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (k5_enumset1(A_23, A_23, B_24, C_25, D_26, E_27, F_28)=k4_enumset1(A_23, B_24, C_25, D_26, E_27, F_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.81  tff(c_6, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.81  tff(c_14, plain, (![G_35, E_33, A_29, F_34, D_32, C_31, B_30]: (k6_enumset1(A_29, A_29, B_30, C_31, D_32, E_33, F_34, G_35)=k5_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.81  tff(c_8, plain, (![A_14, B_15, C_16, D_17]: (k3_enumset1(A_14, A_14, B_15, C_16, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.81  tff(c_106, plain, (![C_75, H_74, F_72, E_70, G_69, A_73, D_71, B_76]: (k2_xboole_0(k3_enumset1(A_73, B_76, C_75, D_71, E_70), k1_enumset1(F_72, G_69, H_74))=k6_enumset1(A_73, B_76, C_75, D_71, E_70, F_72, G_69, H_74))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.81  tff(c_115, plain, (![H_74, F_72, C_16, G_69, D_17, A_14, B_15]: (k6_enumset1(A_14, A_14, B_15, C_16, D_17, F_72, G_69, H_74)=k2_xboole_0(k2_enumset1(A_14, B_15, C_16, D_17), k1_enumset1(F_72, G_69, H_74)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_106])).
% 3.12/1.81  tff(c_152, plain, (![G_87, D_85, F_86, H_91, B_89, C_88, A_90]: (k2_xboole_0(k2_enumset1(A_90, B_89, C_88, D_85), k1_enumset1(F_86, G_87, H_91))=k5_enumset1(A_90, B_89, C_88, D_85, F_86, G_87, H_91))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_115])).
% 3.12/1.81  tff(c_161, plain, (![G_87, F_86, H_91, B_12, A_11, C_13]: (k5_enumset1(A_11, A_11, B_12, C_13, F_86, G_87, H_91)=k2_xboole_0(k1_enumset1(A_11, B_12, C_13), k1_enumset1(F_86, G_87, H_91)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_152])).
% 3.12/1.81  tff(c_171, plain, (![A_96, F_95, H_92, B_97, C_93, G_94]: (k2_xboole_0(k1_enumset1(A_96, B_97, C_93), k1_enumset1(F_95, G_94, H_92))=k4_enumset1(A_96, B_97, C_93, F_95, G_94, H_92))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_161])).
% 3.12/1.81  tff(c_255, plain, (![C_115, A_112, B_110, A_111, B_114, C_113]: (k2_xboole_0(k1_enumset1(A_111, B_110, C_113), k1_enumset1(B_114, A_112, C_115))=k4_enumset1(A_111, B_110, C_113, A_112, B_114, C_115))), inference(superposition, [status(thm), theory('equality')], [c_16, c_171])).
% 3.12/1.81  tff(c_180, plain, (![A_36, F_95, H_92, C_38, B_37, G_94]: (k2_xboole_0(k1_enumset1(B_37, A_36, C_38), k1_enumset1(F_95, G_94, H_92))=k4_enumset1(A_36, B_37, C_38, F_95, G_94, H_92))), inference(superposition, [status(thm), theory('equality')], [c_16, c_171])).
% 3.12/1.81  tff(c_290, plain, (![B_118, A_119, A_121, B_116, C_120, C_117]: (k4_enumset1(B_118, A_119, C_117, B_116, A_121, C_120)=k4_enumset1(A_119, B_118, C_117, A_121, B_116, C_120))), inference(superposition, [status(thm), theory('equality')], [c_255, c_180])).
% 3.12/1.81  tff(c_10, plain, (![E_22, D_21, A_18, C_20, B_19]: (k4_enumset1(A_18, A_18, B_19, C_20, D_21, E_22)=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.81  tff(c_361, plain, (![B_126, A_122, B_125, C_123, C_124]: (k4_enumset1(B_126, B_126, C_124, B_125, A_122, C_123)=k3_enumset1(B_126, C_124, A_122, B_125, C_123))), inference(superposition, [status(thm), theory('equality')], [c_290, c_10])).
% 3.12/1.81  tff(c_394, plain, (![A_127, C_130, B_131, C_129, B_128]: (k3_enumset1(B_131, C_130, B_128, A_127, C_129)=k3_enumset1(B_131, C_130, A_127, B_128, C_129))), inference(superposition, [status(thm), theory('equality')], [c_361, c_10])).
% 3.12/1.81  tff(c_453, plain, (![C_132, B_133, A_134, C_135]: (k3_enumset1(C_132, C_132, B_133, A_134, C_135)=k2_enumset1(C_132, A_134, B_133, C_135))), inference(superposition, [status(thm), theory('equality')], [c_394, c_8])).
% 3.12/1.81  tff(c_471, plain, (![C_132, B_133, A_134, C_135]: (k2_enumset1(C_132, B_133, A_134, C_135)=k2_enumset1(C_132, A_134, B_133, C_135))), inference(superposition, [status(thm), theory('equality')], [c_453, c_8])).
% 3.12/1.81  tff(c_18, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.12/1.81  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_471, c_18])).
% 3.12/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.81  
% 3.12/1.81  Inference rules
% 3.12/1.81  ----------------------
% 3.12/1.81  #Ref     : 0
% 3.12/1.81  #Sup     : 123
% 3.12/1.81  #Fact    : 0
% 3.12/1.81  #Define  : 0
% 3.12/1.81  #Split   : 0
% 3.12/1.81  #Chain   : 0
% 3.12/1.81  #Close   : 0
% 3.12/1.81  
% 3.20/1.81  Ordering : KBO
% 3.20/1.81  
% 3.20/1.81  Simplification rules
% 3.20/1.81  ----------------------
% 3.20/1.81  #Subsume      : 1
% 3.20/1.81  #Demod        : 23
% 3.20/1.81  #Tautology    : 75
% 3.20/1.81  #SimpNegUnit  : 0
% 3.20/1.81  #BackRed      : 1
% 3.20/1.81  
% 3.20/1.81  #Partial instantiations: 0
% 3.20/1.81  #Strategies tried      : 1
% 3.20/1.81  
% 3.20/1.81  Timing (in seconds)
% 3.20/1.81  ----------------------
% 3.20/1.82  Preprocessing        : 0.45
% 3.20/1.82  Parsing              : 0.23
% 3.20/1.82  CNF conversion       : 0.03
% 3.20/1.82  Main loop            : 0.44
% 3.20/1.82  Inferencing          : 0.18
% 3.20/1.82  Reduction            : 0.16
% 3.20/1.82  Demodulation         : 0.13
% 3.20/1.82  BG Simplification    : 0.03
% 3.20/1.82  Subsumption          : 0.05
% 3.20/1.82  Abstraction          : 0.03
% 3.20/1.82  MUC search           : 0.00
% 3.20/1.82  Cooper               : 0.00
% 3.20/1.82  Total                : 0.94
% 3.20/1.82  Index Insertion      : 0.00
% 3.20/1.82  Index Deletion       : 0.00
% 3.20/1.82  Index Matching       : 0.00
% 3.20/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

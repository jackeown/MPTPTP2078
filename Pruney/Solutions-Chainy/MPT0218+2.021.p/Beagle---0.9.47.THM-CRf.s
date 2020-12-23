%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:49 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   44 (  44 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_12,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23,D_24] : k3_enumset1(A_21,A_21,B_22,C_23,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : k4_enumset1(A_25,A_25,B_26,C_27,D_28,E_29) = k3_enumset1(A_25,B_26,C_27,D_28,E_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35) = k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,C_38,B_37] : k6_enumset1(A_36,A_36,B_37,C_38,D_39,E_40,F_41,G_42) = k5_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    ! [E_83,B_78,D_77,C_79,H_84,G_81,F_82,A_80] : k2_xboole_0(k1_tarski(A_80),k5_enumset1(B_78,C_79,D_77,E_83,F_82,G_81,H_84)) = k6_enumset1(A_80,B_78,C_79,D_77,E_83,F_82,G_81,H_84) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [A_85,H_89,C_91,F_87,E_92,G_88,B_86,D_90] : r1_tarski(k1_tarski(A_85),k6_enumset1(A_85,B_86,C_91,D_90,E_92,F_87,G_88,H_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_126,plain,(
    ! [A_95,G_93,D_96,E_99,F_94,B_97,C_98] : r1_tarski(k1_tarski(A_95),k5_enumset1(A_95,B_97,C_98,D_96,E_99,F_94,G_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_122])).

tff(c_130,plain,(
    ! [E_104,F_102,B_101,A_103,D_105,C_100] : r1_tarski(k1_tarski(A_103),k4_enumset1(A_103,B_101,C_100,D_105,E_104,F_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_126])).

tff(c_172,plain,(
    ! [C_115,E_117,D_113,B_116,A_114] : r1_tarski(k1_tarski(A_114),k3_enumset1(A_114,B_116,C_115,D_113,E_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_130])).

tff(c_176,plain,(
    ! [A_118,B_119,C_120,D_121] : r1_tarski(k1_tarski(A_118),k2_enumset1(A_118,B_119,C_120,D_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_172])).

tff(c_180,plain,(
    ! [A_122,B_123,C_124] : r1_tarski(k1_tarski(A_122),k1_enumset1(A_122,B_123,C_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_176])).

tff(c_183,plain,(
    ! [A_16,B_17] : r1_tarski(k1_tarski(A_16),k2_tarski(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_180])).

tff(c_24,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:48:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.74  
% 2.24/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.74  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.24/1.74  
% 2.24/1.74  %Foreground sorts:
% 2.24/1.74  
% 2.24/1.74  
% 2.24/1.74  %Background operators:
% 2.24/1.74  
% 2.24/1.74  
% 2.24/1.74  %Foreground operators:
% 2.24/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.24/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.74  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.74  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.74  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.74  
% 2.38/1.78  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.38/1.78  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.38/1.78  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.38/1.78  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.38/1.78  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.38/1.78  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.38/1.78  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 2.38/1.78  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.38/1.78  tff(f_50, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.38/1.78  tff(c_12, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.78  tff(c_14, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.78  tff(c_16, plain, (![A_21, B_22, C_23, D_24]: (k3_enumset1(A_21, A_21, B_22, C_23, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.38/1.78  tff(c_18, plain, (![A_25, E_29, C_27, D_28, B_26]: (k4_enumset1(A_25, A_25, B_26, C_27, D_28, E_29)=k3_enumset1(A_25, B_26, C_27, D_28, E_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.78  tff(c_20, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35)=k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.38/1.78  tff(c_22, plain, (![F_41, G_42, D_39, A_36, E_40, C_38, B_37]: (k6_enumset1(A_36, A_36, B_37, C_38, D_39, E_40, F_41, G_42)=k5_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.38/1.78  tff(c_107, plain, (![E_83, B_78, D_77, C_79, H_84, G_81, F_82, A_80]: (k2_xboole_0(k1_tarski(A_80), k5_enumset1(B_78, C_79, D_77, E_83, F_82, G_81, H_84))=k6_enumset1(A_80, B_78, C_79, D_77, E_83, F_82, G_81, H_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.78  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.78  tff(c_122, plain, (![A_85, H_89, C_91, F_87, E_92, G_88, B_86, D_90]: (r1_tarski(k1_tarski(A_85), k6_enumset1(A_85, B_86, C_91, D_90, E_92, F_87, G_88, H_89)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 2.38/1.78  tff(c_126, plain, (![A_95, G_93, D_96, E_99, F_94, B_97, C_98]: (r1_tarski(k1_tarski(A_95), k5_enumset1(A_95, B_97, C_98, D_96, E_99, F_94, G_93)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_122])).
% 2.38/1.78  tff(c_130, plain, (![E_104, F_102, B_101, A_103, D_105, C_100]: (r1_tarski(k1_tarski(A_103), k4_enumset1(A_103, B_101, C_100, D_105, E_104, F_102)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_126])).
% 2.38/1.78  tff(c_172, plain, (![C_115, E_117, D_113, B_116, A_114]: (r1_tarski(k1_tarski(A_114), k3_enumset1(A_114, B_116, C_115, D_113, E_117)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_130])).
% 2.38/1.78  tff(c_176, plain, (![A_118, B_119, C_120, D_121]: (r1_tarski(k1_tarski(A_118), k2_enumset1(A_118, B_119, C_120, D_121)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_172])).
% 2.38/1.78  tff(c_180, plain, (![A_122, B_123, C_124]: (r1_tarski(k1_tarski(A_122), k1_enumset1(A_122, B_123, C_124)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_176])).
% 2.38/1.78  tff(c_183, plain, (![A_16, B_17]: (r1_tarski(k1_tarski(A_16), k2_tarski(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_180])).
% 2.38/1.78  tff(c_24, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.38/1.78  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_24])).
% 2.38/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.78  
% 2.38/1.78  Inference rules
% 2.38/1.78  ----------------------
% 2.38/1.78  #Ref     : 0
% 2.38/1.78  #Sup     : 37
% 2.38/1.78  #Fact    : 0
% 2.38/1.78  #Define  : 0
% 2.38/1.78  #Split   : 0
% 2.38/1.78  #Chain   : 0
% 2.38/1.78  #Close   : 0
% 2.38/1.78  
% 2.38/1.78  Ordering : KBO
% 2.38/1.78  
% 2.38/1.78  Simplification rules
% 2.38/1.78  ----------------------
% 2.38/1.78  #Subsume      : 0
% 2.38/1.78  #Demod        : 5
% 2.38/1.78  #Tautology    : 26
% 2.38/1.78  #SimpNegUnit  : 0
% 2.38/1.78  #BackRed      : 1
% 2.38/1.78  
% 2.38/1.79  #Partial instantiations: 0
% 2.38/1.79  #Strategies tried      : 1
% 2.38/1.79  
% 2.38/1.79  Timing (in seconds)
% 2.38/1.79  ----------------------
% 2.38/1.79  Preprocessing        : 0.56
% 2.38/1.79  Parsing              : 0.32
% 2.38/1.79  CNF conversion       : 0.03
% 2.38/1.79  Main loop            : 0.27
% 2.38/1.79  Inferencing          : 0.14
% 2.38/1.79  Reduction            : 0.07
% 2.38/1.79  Demodulation         : 0.06
% 2.38/1.79  BG Simplification    : 0.02
% 2.38/1.79  Subsumption          : 0.02
% 2.38/1.79  Abstraction          : 0.02
% 2.38/1.79  MUC search           : 0.00
% 2.38/1.79  Cooper               : 0.00
% 2.38/1.79  Total                : 0.90
% 2.38/1.79  Index Insertion      : 0.00
% 2.38/1.79  Index Deletion       : 0.00
% 2.38/1.79  Index Matching       : 0.00
% 2.38/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------

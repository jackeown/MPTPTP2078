%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:48 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 118 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   28 (  99 expanded)
%              Number of equality atoms :   27 (  98 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_6,plain,(
    ! [A_5,B_6,D_8,C_7] : k2_enumset1(A_5,B_6,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_30,B_31,C_32,D_33] : k3_enumset1(A_30,A_30,B_31,C_32,D_33) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_27,B_28,C_29] : k2_enumset1(A_27,A_27,B_28,C_29) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [D_37,A_34,B_35,C_36,E_38] : k4_enumset1(A_34,A_34,B_35,C_36,D_37,E_38) = k3_enumset1(A_34,B_35,C_36,D_37,E_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [E_43,F_44,D_42,A_39,C_41,B_40] : k5_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44) = k4_enumset1(A_39,B_40,C_41,D_42,E_43,F_44) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_268,plain,(
    ! [G_87,D_85,A_88,B_83,C_84,F_82,E_86] : k2_xboole_0(k4_enumset1(A_88,B_83,C_84,D_85,E_86,F_82),k1_tarski(G_87)) = k5_enumset1(A_88,B_83,C_84,D_85,E_86,F_82,G_87) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_277,plain,(
    ! [G_87,D_37,A_34,B_35,C_36,E_38] : k5_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,G_87) = k2_xboole_0(k3_enumset1(A_34,B_35,C_36,D_37,E_38),k1_tarski(G_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_268])).

tff(c_281,plain,(
    ! [C_94,A_89,G_91,B_93,E_92,D_90] : k2_xboole_0(k3_enumset1(A_89,B_93,C_94,D_90,E_92),k1_tarski(G_91)) = k4_enumset1(A_89,B_93,C_94,D_90,E_92,G_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_277])).

tff(c_290,plain,(
    ! [D_33,A_30,C_32,G_91,B_31] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,G_91) = k2_xboole_0(k2_enumset1(A_30,B_31,C_32,D_33),k1_tarski(G_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_281])).

tff(c_294,plain,(
    ! [C_95,G_99,B_96,D_98,A_97] : k2_xboole_0(k2_enumset1(A_97,B_96,C_95,D_98),k1_tarski(G_99)) = k3_enumset1(A_97,B_96,C_95,D_98,G_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_290])).

tff(c_312,plain,(
    ! [A_27,B_28,C_29,G_99] : k3_enumset1(A_27,A_27,B_28,C_29,G_99) = k2_xboole_0(k1_enumset1(A_27,B_28,C_29),k1_tarski(G_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_294])).

tff(c_542,plain,(
    ! [A_131,B_132,C_133,G_134] : k2_xboole_0(k1_enumset1(A_131,B_132,C_133),k1_tarski(G_134)) = k2_enumset1(A_131,B_132,C_133,G_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_312])).

tff(c_71,plain,(
    ! [A_55,B_56,D_57,C_58] : k2_enumset1(A_55,B_56,D_57,C_58) = k2_enumset1(A_55,B_56,C_58,D_57) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [B_56,D_57,C_58] : k2_enumset1(B_56,B_56,D_57,C_58) = k1_enumset1(B_56,C_58,D_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_16])).

tff(c_303,plain,(
    ! [B_56,D_57,C_58,G_99] : k3_enumset1(B_56,B_56,D_57,C_58,G_99) = k2_xboole_0(k1_enumset1(B_56,C_58,D_57),k1_tarski(G_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_294])).

tff(c_315,plain,(
    ! [B_56,C_58,D_57,G_99] : k2_xboole_0(k1_enumset1(B_56,C_58,D_57),k1_tarski(G_99)) = k2_enumset1(B_56,D_57,C_58,G_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_303])).

tff(c_548,plain,(
    ! [A_131,C_133,B_132,G_134] : k2_enumset1(A_131,C_133,B_132,G_134) = k2_enumset1(A_131,B_132,C_133,G_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_315])).

tff(c_24,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_24])).

tff(c_582,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_548,c_25])).

tff(c_585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.30  
% 2.21/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.30  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.21/1.30  
% 2.21/1.30  %Foreground sorts:
% 2.21/1.30  
% 2.21/1.30  
% 2.21/1.30  %Background operators:
% 2.21/1.30  
% 2.21/1.30  
% 2.21/1.30  %Foreground operators:
% 2.21/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.30  
% 2.51/1.31  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 2.51/1.31  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.51/1.31  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.51/1.31  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.51/1.31  tff(f_47, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.51/1.31  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 2.51/1.31  tff(f_50, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 2.51/1.31  tff(c_6, plain, (![A_5, B_6, D_8, C_7]: (k2_enumset1(A_5, B_6, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.31  tff(c_18, plain, (![A_30, B_31, C_32, D_33]: (k3_enumset1(A_30, A_30, B_31, C_32, D_33)=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.31  tff(c_16, plain, (![A_27, B_28, C_29]: (k2_enumset1(A_27, A_27, B_28, C_29)=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.31  tff(c_20, plain, (![D_37, A_34, B_35, C_36, E_38]: (k4_enumset1(A_34, A_34, B_35, C_36, D_37, E_38)=k3_enumset1(A_34, B_35, C_36, D_37, E_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.31  tff(c_22, plain, (![E_43, F_44, D_42, A_39, C_41, B_40]: (k5_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44)=k4_enumset1(A_39, B_40, C_41, D_42, E_43, F_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.31  tff(c_268, plain, (![G_87, D_85, A_88, B_83, C_84, F_82, E_86]: (k2_xboole_0(k4_enumset1(A_88, B_83, C_84, D_85, E_86, F_82), k1_tarski(G_87))=k5_enumset1(A_88, B_83, C_84, D_85, E_86, F_82, G_87))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.31  tff(c_277, plain, (![G_87, D_37, A_34, B_35, C_36, E_38]: (k5_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, G_87)=k2_xboole_0(k3_enumset1(A_34, B_35, C_36, D_37, E_38), k1_tarski(G_87)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_268])).
% 2.51/1.31  tff(c_281, plain, (![C_94, A_89, G_91, B_93, E_92, D_90]: (k2_xboole_0(k3_enumset1(A_89, B_93, C_94, D_90, E_92), k1_tarski(G_91))=k4_enumset1(A_89, B_93, C_94, D_90, E_92, G_91))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_277])).
% 2.51/1.31  tff(c_290, plain, (![D_33, A_30, C_32, G_91, B_31]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, G_91)=k2_xboole_0(k2_enumset1(A_30, B_31, C_32, D_33), k1_tarski(G_91)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_281])).
% 2.51/1.31  tff(c_294, plain, (![C_95, G_99, B_96, D_98, A_97]: (k2_xboole_0(k2_enumset1(A_97, B_96, C_95, D_98), k1_tarski(G_99))=k3_enumset1(A_97, B_96, C_95, D_98, G_99))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_290])).
% 2.51/1.31  tff(c_312, plain, (![A_27, B_28, C_29, G_99]: (k3_enumset1(A_27, A_27, B_28, C_29, G_99)=k2_xboole_0(k1_enumset1(A_27, B_28, C_29), k1_tarski(G_99)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_294])).
% 2.51/1.31  tff(c_542, plain, (![A_131, B_132, C_133, G_134]: (k2_xboole_0(k1_enumset1(A_131, B_132, C_133), k1_tarski(G_134))=k2_enumset1(A_131, B_132, C_133, G_134))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_312])).
% 2.51/1.31  tff(c_71, plain, (![A_55, B_56, D_57, C_58]: (k2_enumset1(A_55, B_56, D_57, C_58)=k2_enumset1(A_55, B_56, C_58, D_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.31  tff(c_87, plain, (![B_56, D_57, C_58]: (k2_enumset1(B_56, B_56, D_57, C_58)=k1_enumset1(B_56, C_58, D_57))), inference(superposition, [status(thm), theory('equality')], [c_71, c_16])).
% 2.51/1.31  tff(c_303, plain, (![B_56, D_57, C_58, G_99]: (k3_enumset1(B_56, B_56, D_57, C_58, G_99)=k2_xboole_0(k1_enumset1(B_56, C_58, D_57), k1_tarski(G_99)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_294])).
% 2.51/1.31  tff(c_315, plain, (![B_56, C_58, D_57, G_99]: (k2_xboole_0(k1_enumset1(B_56, C_58, D_57), k1_tarski(G_99))=k2_enumset1(B_56, D_57, C_58, G_99))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_303])).
% 2.51/1.31  tff(c_548, plain, (![A_131, C_133, B_132, G_134]: (k2_enumset1(A_131, C_133, B_132, G_134)=k2_enumset1(A_131, B_132, C_133, G_134))), inference(superposition, [status(thm), theory('equality')], [c_542, c_315])).
% 2.51/1.31  tff(c_24, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.31  tff(c_25, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_24])).
% 2.51/1.31  tff(c_582, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_548, c_548, c_25])).
% 2.51/1.31  tff(c_585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_582])).
% 2.51/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.31  
% 2.51/1.31  Inference rules
% 2.51/1.31  ----------------------
% 2.51/1.31  #Ref     : 0
% 2.51/1.31  #Sup     : 128
% 2.51/1.31  #Fact    : 0
% 2.51/1.31  #Define  : 0
% 2.51/1.31  #Split   : 0
% 2.51/1.31  #Chain   : 0
% 2.51/1.31  #Close   : 0
% 2.51/1.31  
% 2.51/1.31  Ordering : KBO
% 2.51/1.31  
% 2.51/1.31  Simplification rules
% 2.51/1.31  ----------------------
% 2.51/1.31  #Subsume      : 1
% 2.51/1.31  #Demod        : 80
% 2.51/1.31  #Tautology    : 105
% 2.51/1.31  #SimpNegUnit  : 0
% 2.51/1.31  #BackRed      : 1
% 2.51/1.31  
% 2.51/1.31  #Partial instantiations: 0
% 2.51/1.31  #Strategies tried      : 1
% 2.51/1.31  
% 2.51/1.31  Timing (in seconds)
% 2.51/1.31  ----------------------
% 2.51/1.31  Preprocessing        : 0.29
% 2.51/1.32  Parsing              : 0.15
% 2.51/1.32  CNF conversion       : 0.02
% 2.51/1.32  Main loop            : 0.26
% 2.51/1.32  Inferencing          : 0.11
% 2.51/1.32  Reduction            : 0.10
% 2.51/1.32  Demodulation         : 0.08
% 2.51/1.32  BG Simplification    : 0.02
% 2.51/1.32  Subsumption          : 0.03
% 2.51/1.32  Abstraction          : 0.02
% 2.51/1.32  MUC search           : 0.00
% 2.51/1.32  Cooper               : 0.00
% 2.51/1.32  Total                : 0.58
% 2.51/1.32  Index Insertion      : 0.00
% 2.51/1.32  Index Deletion       : 0.00
% 2.51/1.32  Index Matching       : 0.00
% 2.51/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

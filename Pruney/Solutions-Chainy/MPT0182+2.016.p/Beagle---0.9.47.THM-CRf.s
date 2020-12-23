%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:44 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   45 (  49 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 (  31 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_201,plain,(
    ! [A_85,B_86,C_87] : k2_xboole_0(k1_tarski(A_85),k2_tarski(B_86,C_87)) = k1_enumset1(A_85,B_86,C_87) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_216,plain,(
    ! [B_86,C_87,A_85] : k2_xboole_0(k2_tarski(B_86,C_87),k1_tarski(A_85)) = k1_enumset1(A_85,B_86,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_201])).

tff(c_22,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_43,B_44,C_45,D_46] : k3_enumset1(A_43,A_43,B_44,C_45,D_46) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_47,E_51,D_50,C_49,B_48] : k4_enumset1(A_47,A_47,B_48,C_49,D_50,E_51) = k3_enumset1(A_47,B_48,C_49,D_50,E_51) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_481,plain,(
    ! [B_111,A_113,F_115,D_114,C_116,E_112] : k2_xboole_0(k3_enumset1(A_113,B_111,C_116,D_114,E_112),k1_tarski(F_115)) = k4_enumset1(A_113,B_111,C_116,D_114,E_112,F_115) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_496,plain,(
    ! [F_115,D_46,C_45,A_43,B_44] : k4_enumset1(A_43,A_43,B_44,C_45,D_46,F_115) = k2_xboole_0(k2_enumset1(A_43,B_44,C_45,D_46),k1_tarski(F_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_481])).

tff(c_537,plain,(
    ! [A_122,F_123,D_121,B_124,C_120] : k2_xboole_0(k2_enumset1(A_122,B_124,C_120,D_121),k1_tarski(F_123)) = k3_enumset1(A_122,B_124,C_120,D_121,F_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_496])).

tff(c_552,plain,(
    ! [A_40,B_41,C_42,F_123] : k3_enumset1(A_40,A_40,B_41,C_42,F_123) = k2_xboole_0(k1_enumset1(A_40,B_41,C_42),k1_tarski(F_123)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_537])).

tff(c_571,plain,(
    ! [A_132,B_133,C_134,F_135] : k2_xboole_0(k1_enumset1(A_132,B_133,C_134),k1_tarski(F_135)) = k2_enumset1(A_132,B_133,C_134,F_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_552])).

tff(c_610,plain,(
    ! [A_38,B_39,F_135] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(F_135)) = k2_enumset1(A_38,A_38,B_39,F_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_571])).

tff(c_620,plain,(
    ! [F_135,A_38,B_39] : k1_enumset1(F_135,A_38,B_39) = k1_enumset1(A_38,B_39,F_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_22,c_610])).

tff(c_32,plain,(
    ! [A_65,C_67,B_66] : k1_enumset1(A_65,C_67,B_66) = k1_enumset1(A_65,B_66,C_67) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.37  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.51/1.37  
% 2.51/1.37  %Foreground sorts:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Background operators:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Foreground operators:
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.37  
% 2.51/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.51/1.38  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.51/1.38  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.51/1.38  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.51/1.38  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.51/1.38  tff(f_51, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.51/1.38  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 2.51/1.38  tff(f_57, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 2.51/1.38  tff(f_60, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 2.51/1.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.38  tff(c_201, plain, (![A_85, B_86, C_87]: (k2_xboole_0(k1_tarski(A_85), k2_tarski(B_86, C_87))=k1_enumset1(A_85, B_86, C_87))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.38  tff(c_216, plain, (![B_86, C_87, A_85]: (k2_xboole_0(k2_tarski(B_86, C_87), k1_tarski(A_85))=k1_enumset1(A_85, B_86, C_87))), inference(superposition, [status(thm), theory('equality')], [c_2, c_201])).
% 2.51/1.38  tff(c_22, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.38  tff(c_20, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.38  tff(c_24, plain, (![A_43, B_44, C_45, D_46]: (k3_enumset1(A_43, A_43, B_44, C_45, D_46)=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.51/1.38  tff(c_26, plain, (![A_47, E_51, D_50, C_49, B_48]: (k4_enumset1(A_47, A_47, B_48, C_49, D_50, E_51)=k3_enumset1(A_47, B_48, C_49, D_50, E_51))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.51/1.38  tff(c_481, plain, (![B_111, A_113, F_115, D_114, C_116, E_112]: (k2_xboole_0(k3_enumset1(A_113, B_111, C_116, D_114, E_112), k1_tarski(F_115))=k4_enumset1(A_113, B_111, C_116, D_114, E_112, F_115))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.38  tff(c_496, plain, (![F_115, D_46, C_45, A_43, B_44]: (k4_enumset1(A_43, A_43, B_44, C_45, D_46, F_115)=k2_xboole_0(k2_enumset1(A_43, B_44, C_45, D_46), k1_tarski(F_115)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_481])).
% 2.51/1.38  tff(c_537, plain, (![A_122, F_123, D_121, B_124, C_120]: (k2_xboole_0(k2_enumset1(A_122, B_124, C_120, D_121), k1_tarski(F_123))=k3_enumset1(A_122, B_124, C_120, D_121, F_123))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_496])).
% 2.51/1.38  tff(c_552, plain, (![A_40, B_41, C_42, F_123]: (k3_enumset1(A_40, A_40, B_41, C_42, F_123)=k2_xboole_0(k1_enumset1(A_40, B_41, C_42), k1_tarski(F_123)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_537])).
% 2.51/1.38  tff(c_571, plain, (![A_132, B_133, C_134, F_135]: (k2_xboole_0(k1_enumset1(A_132, B_133, C_134), k1_tarski(F_135))=k2_enumset1(A_132, B_133, C_134, F_135))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_552])).
% 2.51/1.38  tff(c_610, plain, (![A_38, B_39, F_135]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(F_135))=k2_enumset1(A_38, A_38, B_39, F_135))), inference(superposition, [status(thm), theory('equality')], [c_20, c_571])).
% 2.51/1.38  tff(c_620, plain, (![F_135, A_38, B_39]: (k1_enumset1(F_135, A_38, B_39)=k1_enumset1(A_38, B_39, F_135))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_22, c_610])).
% 2.51/1.38  tff(c_32, plain, (![A_65, C_67, B_66]: (k1_enumset1(A_65, C_67, B_66)=k1_enumset1(A_65, B_66, C_67))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.51/1.38  tff(c_34, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.38  tff(c_35, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 2.51/1.38  tff(c_623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_620, c_35])).
% 2.51/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  Inference rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Ref     : 0
% 2.51/1.38  #Sup     : 149
% 2.51/1.38  #Fact    : 0
% 2.51/1.38  #Define  : 0
% 2.51/1.38  #Split   : 0
% 2.51/1.38  #Chain   : 0
% 2.51/1.38  #Close   : 0
% 2.51/1.38  
% 2.51/1.38  Ordering : KBO
% 2.51/1.38  
% 2.51/1.38  Simplification rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Subsume      : 31
% 2.51/1.38  #Demod        : 51
% 2.51/1.38  #Tautology    : 88
% 2.51/1.38  #SimpNegUnit  : 0
% 2.51/1.38  #BackRed      : 1
% 2.51/1.38  
% 2.51/1.38  #Partial instantiations: 0
% 2.51/1.38  #Strategies tried      : 1
% 2.51/1.38  
% 2.51/1.38  Timing (in seconds)
% 2.51/1.38  ----------------------
% 2.51/1.38  Preprocessing        : 0.33
% 2.51/1.38  Parsing              : 0.18
% 2.51/1.38  CNF conversion       : 0.02
% 2.51/1.38  Main loop            : 0.28
% 2.51/1.38  Inferencing          : 0.11
% 2.51/1.38  Reduction            : 0.11
% 2.51/1.38  Demodulation         : 0.09
% 2.51/1.38  BG Simplification    : 0.02
% 2.51/1.38  Subsumption          : 0.04
% 2.51/1.38  Abstraction          : 0.02
% 2.51/1.38  MUC search           : 0.00
% 2.51/1.38  Cooper               : 0.00
% 2.51/1.38  Total                : 0.64
% 2.51/1.38  Index Insertion      : 0.00
% 2.51/1.38  Index Deletion       : 0.00
% 2.51/1.38  Index Matching       : 0.00
% 2.51/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

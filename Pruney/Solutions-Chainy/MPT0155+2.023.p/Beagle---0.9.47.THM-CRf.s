%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:11 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   35 (  53 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_6,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k1_tarski(A_9),k2_tarski(B_10,C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [A_45,B_46,C_47,D_48] : k2_xboole_0(k1_tarski(A_45),k1_enumset1(B_46,C_47,D_48)) = k2_enumset1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_45,A_35,B_36] : k2_xboole_0(k1_tarski(A_45),k2_tarski(A_35,B_36)) = k2_enumset1(A_45,A_35,A_35,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_72,plain,(
    ! [A_45,A_35,B_36] : k2_enumset1(A_45,A_35,A_35,B_36) = k1_enumset1(A_45,A_35,B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_tarski(A_12),k1_enumset1(B_13,C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,(
    ! [D_56,E_54,B_53,C_57,A_55] : k2_xboole_0(k2_tarski(A_55,B_53),k1_enumset1(C_57,D_56,E_54)) = k3_enumset1(A_55,B_53,C_57,D_56,E_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_636,plain,(
    ! [A_104,B_105,A_106,B_107] : k3_enumset1(A_104,B_105,A_106,A_106,B_107) = k2_xboole_0(k2_tarski(A_104,B_105),k2_tarski(A_106,B_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_149])).

tff(c_693,plain,(
    ! [A_34,A_106,B_107] : k3_enumset1(A_34,A_34,A_106,A_106,B_107) = k2_xboole_0(k1_tarski(A_34),k2_tarski(A_106,B_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_636])).

tff(c_713,plain,(
    ! [A_108,A_109,B_110] : k3_enumset1(A_108,A_108,A_109,A_109,B_110) = k1_enumset1(A_108,A_109,B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_693])).

tff(c_12,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] : k2_xboole_0(k1_tarski(A_21),k3_enumset1(B_22,C_23,D_24,E_25,F_26)) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,F_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_737,plain,(
    ! [A_21,A_108,A_109,B_110] : k4_enumset1(A_21,A_108,A_108,A_109,A_109,B_110) = k2_xboole_0(k1_tarski(A_21),k1_enumset1(A_108,A_109,B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_12])).

tff(c_841,plain,(
    ! [A_114,A_115,A_116,B_117] : k4_enumset1(A_114,A_115,A_115,A_116,A_116,B_117) = k2_enumset1(A_114,A_115,A_116,B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_737])).

tff(c_48,plain,(
    ! [A_42,B_43,C_44] : k2_xboole_0(k1_tarski(A_42),k2_tarski(B_43,C_44)) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_49,A_50] : k2_xboole_0(k1_tarski(A_49),k1_tarski(A_50)) = k1_enumset1(A_49,A_50,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_86,plain,(
    ! [A_50] : k2_xboole_0(k1_tarski(A_50),k1_tarski(A_50)) = k2_tarski(A_50,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_18])).

tff(c_103,plain,(
    ! [A_51] : k2_xboole_0(k1_tarski(A_51),k1_tarski(A_51)) = k1_tarski(A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_86])).

tff(c_57,plain,(
    ! [A_42,A_34] : k2_xboole_0(k1_tarski(A_42),k1_tarski(A_34)) = k1_enumset1(A_42,A_34,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_109,plain,(
    ! [A_51] : k1_enumset1(A_51,A_51,A_51) = k1_tarski(A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_57])).

tff(c_248,plain,(
    ! [C_68,A_67,F_66,B_69,D_65,E_64] : k2_xboole_0(k1_enumset1(A_67,B_69,C_68),k1_enumset1(D_65,E_64,F_66)) = k4_enumset1(A_67,B_69,C_68,D_65,E_64,F_66) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_257,plain,(
    ! [A_51,D_65,E_64,F_66] : k4_enumset1(A_51,A_51,A_51,D_65,E_64,F_66) = k2_xboole_0(k1_tarski(A_51),k1_enumset1(D_65,E_64,F_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_248])).

tff(c_275,plain,(
    ! [A_51,D_65,E_64,F_66] : k4_enumset1(A_51,A_51,A_51,D_65,E_64,F_66) = k2_enumset1(A_51,D_65,E_64,F_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_257])).

tff(c_860,plain,(
    ! [A_115,A_116,B_117] : k2_enumset1(A_115,A_116,A_116,B_117) = k2_enumset1(A_115,A_115,A_116,B_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_275])).

tff(c_880,plain,(
    ! [A_115,A_116,B_117] : k2_enumset1(A_115,A_115,A_116,B_117) = k1_enumset1(A_115,A_116,B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_860])).

tff(c_20,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.27  % Computer   : n025.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % DateTime   : Tue Dec  1 13:15:05 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.08/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.23  
% 2.51/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.23  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.51/1.23  
% 2.51/1.23  %Foreground sorts:
% 2.51/1.23  
% 2.51/1.23  
% 2.51/1.23  %Background operators:
% 2.51/1.23  
% 2.51/1.23  
% 2.51/1.23  %Foreground operators:
% 2.51/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.23  
% 2.51/1.24  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.51/1.24  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.51/1.24  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.51/1.24  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.51/1.24  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 2.51/1.24  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.51/1.24  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 2.51/1.24  tff(f_46, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.51/1.24  tff(c_6, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k1_tarski(A_9), k2_tarski(B_10, C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.24  tff(c_18, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.24  tff(c_60, plain, (![A_45, B_46, C_47, D_48]: (k2_xboole_0(k1_tarski(A_45), k1_enumset1(B_46, C_47, D_48))=k2_enumset1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.24  tff(c_69, plain, (![A_45, A_35, B_36]: (k2_xboole_0(k1_tarski(A_45), k2_tarski(A_35, B_36))=k2_enumset1(A_45, A_35, A_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_18, c_60])).
% 2.51/1.24  tff(c_72, plain, (![A_45, A_35, B_36]: (k2_enumset1(A_45, A_35, A_35, B_36)=k1_enumset1(A_45, A_35, B_36))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69])).
% 2.51/1.24  tff(c_8, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_tarski(A_12), k1_enumset1(B_13, C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.24  tff(c_16, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.24  tff(c_149, plain, (![D_56, E_54, B_53, C_57, A_55]: (k2_xboole_0(k2_tarski(A_55, B_53), k1_enumset1(C_57, D_56, E_54))=k3_enumset1(A_55, B_53, C_57, D_56, E_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.24  tff(c_636, plain, (![A_104, B_105, A_106, B_107]: (k3_enumset1(A_104, B_105, A_106, A_106, B_107)=k2_xboole_0(k2_tarski(A_104, B_105), k2_tarski(A_106, B_107)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_149])).
% 2.51/1.24  tff(c_693, plain, (![A_34, A_106, B_107]: (k3_enumset1(A_34, A_34, A_106, A_106, B_107)=k2_xboole_0(k1_tarski(A_34), k2_tarski(A_106, B_107)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_636])).
% 2.51/1.24  tff(c_713, plain, (![A_108, A_109, B_110]: (k3_enumset1(A_108, A_108, A_109, A_109, B_110)=k1_enumset1(A_108, A_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_693])).
% 2.51/1.24  tff(c_12, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k2_xboole_0(k1_tarski(A_21), k3_enumset1(B_22, C_23, D_24, E_25, F_26))=k4_enumset1(A_21, B_22, C_23, D_24, E_25, F_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.24  tff(c_737, plain, (![A_21, A_108, A_109, B_110]: (k4_enumset1(A_21, A_108, A_108, A_109, A_109, B_110)=k2_xboole_0(k1_tarski(A_21), k1_enumset1(A_108, A_109, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_713, c_12])).
% 2.51/1.24  tff(c_841, plain, (![A_114, A_115, A_116, B_117]: (k4_enumset1(A_114, A_115, A_115, A_116, A_116, B_117)=k2_enumset1(A_114, A_115, A_116, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_737])).
% 2.51/1.24  tff(c_48, plain, (![A_42, B_43, C_44]: (k2_xboole_0(k1_tarski(A_42), k2_tarski(B_43, C_44))=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.24  tff(c_73, plain, (![A_49, A_50]: (k2_xboole_0(k1_tarski(A_49), k1_tarski(A_50))=k1_enumset1(A_49, A_50, A_50))), inference(superposition, [status(thm), theory('equality')], [c_16, c_48])).
% 2.51/1.24  tff(c_86, plain, (![A_50]: (k2_xboole_0(k1_tarski(A_50), k1_tarski(A_50))=k2_tarski(A_50, A_50))), inference(superposition, [status(thm), theory('equality')], [c_73, c_18])).
% 2.51/1.24  tff(c_103, plain, (![A_51]: (k2_xboole_0(k1_tarski(A_51), k1_tarski(A_51))=k1_tarski(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_86])).
% 2.51/1.24  tff(c_57, plain, (![A_42, A_34]: (k2_xboole_0(k1_tarski(A_42), k1_tarski(A_34))=k1_enumset1(A_42, A_34, A_34))), inference(superposition, [status(thm), theory('equality')], [c_16, c_48])).
% 2.51/1.24  tff(c_109, plain, (![A_51]: (k1_enumset1(A_51, A_51, A_51)=k1_tarski(A_51))), inference(superposition, [status(thm), theory('equality')], [c_103, c_57])).
% 2.51/1.24  tff(c_248, plain, (![C_68, A_67, F_66, B_69, D_65, E_64]: (k2_xboole_0(k1_enumset1(A_67, B_69, C_68), k1_enumset1(D_65, E_64, F_66))=k4_enumset1(A_67, B_69, C_68, D_65, E_64, F_66))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.24  tff(c_257, plain, (![A_51, D_65, E_64, F_66]: (k4_enumset1(A_51, A_51, A_51, D_65, E_64, F_66)=k2_xboole_0(k1_tarski(A_51), k1_enumset1(D_65, E_64, F_66)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_248])).
% 2.51/1.24  tff(c_275, plain, (![A_51, D_65, E_64, F_66]: (k4_enumset1(A_51, A_51, A_51, D_65, E_64, F_66)=k2_enumset1(A_51, D_65, E_64, F_66))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_257])).
% 2.51/1.24  tff(c_860, plain, (![A_115, A_116, B_117]: (k2_enumset1(A_115, A_116, A_116, B_117)=k2_enumset1(A_115, A_115, A_116, B_117))), inference(superposition, [status(thm), theory('equality')], [c_841, c_275])).
% 2.51/1.24  tff(c_880, plain, (![A_115, A_116, B_117]: (k2_enumset1(A_115, A_115, A_116, B_117)=k1_enumset1(A_115, A_116, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_860])).
% 2.51/1.24  tff(c_20, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.51/1.24  tff(c_887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_880, c_20])).
% 2.51/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.24  
% 2.51/1.24  Inference rules
% 2.51/1.24  ----------------------
% 2.51/1.24  #Ref     : 0
% 2.51/1.24  #Sup     : 205
% 2.51/1.24  #Fact    : 0
% 2.51/1.24  #Define  : 0
% 2.51/1.24  #Split   : 0
% 2.51/1.24  #Chain   : 0
% 2.51/1.24  #Close   : 0
% 2.51/1.24  
% 2.51/1.24  Ordering : KBO
% 2.51/1.24  
% 2.51/1.24  Simplification rules
% 2.51/1.24  ----------------------
% 2.51/1.24  #Subsume      : 24
% 2.51/1.24  #Demod        : 145
% 2.51/1.24  #Tautology    : 142
% 2.51/1.24  #SimpNegUnit  : 0
% 2.51/1.24  #BackRed      : 1
% 2.51/1.24  
% 2.51/1.24  #Partial instantiations: 0
% 2.51/1.24  #Strategies tried      : 1
% 2.51/1.24  
% 2.51/1.24  Timing (in seconds)
% 2.51/1.24  ----------------------
% 2.51/1.25  Preprocessing        : 0.30
% 2.51/1.25  Parsing              : 0.17
% 2.51/1.25  CNF conversion       : 0.02
% 2.51/1.25  Main loop            : 0.31
% 2.51/1.25  Inferencing          : 0.13
% 2.51/1.25  Reduction            : 0.12
% 2.51/1.25  Demodulation         : 0.09
% 2.51/1.25  BG Simplification    : 0.02
% 2.51/1.25  Subsumption          : 0.03
% 2.51/1.25  Abstraction          : 0.02
% 2.51/1.25  MUC search           : 0.00
% 2.51/1.25  Cooper               : 0.00
% 2.51/1.25  Total                : 0.63
% 2.51/1.25  Index Insertion      : 0.00
% 2.51/1.25  Index Deletion       : 0.00
% 2.51/1.25  Index Matching       : 0.00
% 2.51/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

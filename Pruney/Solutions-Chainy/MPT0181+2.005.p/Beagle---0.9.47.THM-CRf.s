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
% DateTime   : Thu Dec  3 09:46:41 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   45 (  92 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   32 (  79 expanded)
%              Number of equality atoms :   31 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_41,B_42,C_43,D_44] : k3_enumset1(A_41,A_41,B_42,C_43,D_44) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_29,B_30,C_31] : k3_enumset1(A_29,A_29,A_29,B_30,C_31) = k1_enumset1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [B_42,C_43,D_44] : k2_enumset1(B_42,B_42,C_43,D_44) = k1_enumset1(B_42,C_43,D_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_16])).

tff(c_121,plain,(
    ! [A_50,B_52,E_48,C_51,D_49] : k2_xboole_0(k1_tarski(A_50),k2_enumset1(B_52,C_51,D_49,E_48)) = k3_enumset1(A_50,B_52,C_51,D_49,E_48) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_134,plain,(
    ! [A_53,B_54,C_55,D_56] : k3_enumset1(A_53,B_54,B_54,C_55,D_56) = k2_xboole_0(k1_tarski(A_53),k1_enumset1(B_54,C_55,D_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_121])).

tff(c_12,plain,(
    ! [A_24,B_25,C_26,D_27] : k3_enumset1(A_24,A_24,B_25,C_26,D_27) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_144,plain,(
    ! [B_54,C_55,D_56] : k2_xboole_0(k1_tarski(B_54),k1_enumset1(B_54,C_55,D_56)) = k2_enumset1(B_54,B_54,C_55,D_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_12])).

tff(c_170,plain,(
    ! [B_54,C_55,D_56] : k2_xboole_0(k1_tarski(B_54),k1_enumset1(B_54,C_55,D_56)) = k1_enumset1(B_54,C_55,D_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_144])).

tff(c_61,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_28] : k1_enumset1(A_28,A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [B_36] : k2_tarski(B_36,B_36) = k1_tarski(B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_14])).

tff(c_228,plain,(
    ! [G_68,B_66,F_63,C_67,E_65,A_64,D_69] : k2_xboole_0(k2_tarski(A_64,B_66),k3_enumset1(C_67,D_69,E_65,F_63,G_68)) = k5_enumset1(A_64,B_66,C_67,D_69,E_65,F_63,G_68) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243,plain,(
    ! [B_66,A_29,A_64,C_31,B_30] : k5_enumset1(A_64,B_66,A_29,A_29,A_29,B_30,C_31) = k2_xboole_0(k2_tarski(A_64,B_66),k1_enumset1(A_29,B_30,C_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_288,plain,(
    ! [B_75,D_73,E_77,F_76,A_78,C_72,G_74] : k2_xboole_0(k3_enumset1(A_78,B_75,C_72,D_73,E_77),k2_tarski(F_76,G_74)) = k5_enumset1(A_78,B_75,C_72,D_73,E_77,F_76,G_74) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_880,plain,(
    ! [C_103,A_102,B_101,F_100,G_104] : k5_enumset1(A_102,A_102,A_102,B_101,C_103,F_100,G_104) = k2_xboole_0(k1_enumset1(A_102,B_101,C_103),k2_tarski(F_100,G_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_288])).

tff(c_900,plain,(
    ! [A_29,B_30,C_31] : k2_xboole_0(k1_enumset1(A_29,A_29,A_29),k2_tarski(B_30,C_31)) = k2_xboole_0(k2_tarski(A_29,A_29),k1_enumset1(A_29,B_30,C_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_880])).

tff(c_929,plain,(
    ! [A_105,B_106,C_107] : k2_xboole_0(k1_tarski(A_105),k2_tarski(B_106,C_107)) = k1_enumset1(A_105,B_106,C_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_68,c_14,c_900])).

tff(c_1213,plain,(
    ! [A_121,A_122,B_123] : k2_xboole_0(k1_tarski(A_121),k2_tarski(A_122,B_123)) = k1_enumset1(A_121,B_123,A_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_929])).

tff(c_921,plain,(
    ! [A_29,B_30,C_31] : k2_xboole_0(k1_tarski(A_29),k2_tarski(B_30,C_31)) = k1_enumset1(A_29,B_30,C_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_68,c_14,c_900])).

tff(c_1219,plain,(
    ! [A_121,B_123,A_122] : k1_enumset1(A_121,B_123,A_122) = k1_enumset1(A_121,A_122,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_921])).

tff(c_18,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 09:26:42 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.51  
% 2.97/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.51  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.97/1.51  
% 2.97/1.51  %Foreground sorts:
% 2.97/1.51  
% 2.97/1.51  
% 2.97/1.51  %Background operators:
% 2.97/1.51  
% 2.97/1.51  
% 2.97/1.51  %Foreground operators:
% 2.97/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.97/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.51  
% 2.97/1.52  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.97/1.52  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.97/1.52  tff(f_41, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_enumset1)).
% 2.97/1.52  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.97/1.52  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.97/1.52  tff(f_39, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.97/1.52  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.97/1.52  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 2.97/1.52  tff(f_44, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 2.97/1.52  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.52  tff(c_96, plain, (![A_41, B_42, C_43, D_44]: (k3_enumset1(A_41, A_41, B_42, C_43, D_44)=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.52  tff(c_16, plain, (![A_29, B_30, C_31]: (k3_enumset1(A_29, A_29, A_29, B_30, C_31)=k1_enumset1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.97/1.52  tff(c_103, plain, (![B_42, C_43, D_44]: (k2_enumset1(B_42, B_42, C_43, D_44)=k1_enumset1(B_42, C_43, D_44))), inference(superposition, [status(thm), theory('equality')], [c_96, c_16])).
% 2.97/1.52  tff(c_121, plain, (![A_50, B_52, E_48, C_51, D_49]: (k2_xboole_0(k1_tarski(A_50), k2_enumset1(B_52, C_51, D_49, E_48))=k3_enumset1(A_50, B_52, C_51, D_49, E_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.97/1.52  tff(c_134, plain, (![A_53, B_54, C_55, D_56]: (k3_enumset1(A_53, B_54, B_54, C_55, D_56)=k2_xboole_0(k1_tarski(A_53), k1_enumset1(B_54, C_55, D_56)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_121])).
% 2.97/1.52  tff(c_12, plain, (![A_24, B_25, C_26, D_27]: (k3_enumset1(A_24, A_24, B_25, C_26, D_27)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.52  tff(c_144, plain, (![B_54, C_55, D_56]: (k2_xboole_0(k1_tarski(B_54), k1_enumset1(B_54, C_55, D_56))=k2_enumset1(B_54, B_54, C_55, D_56))), inference(superposition, [status(thm), theory('equality')], [c_134, c_12])).
% 2.97/1.52  tff(c_170, plain, (![B_54, C_55, D_56]: (k2_xboole_0(k1_tarski(B_54), k1_enumset1(B_54, C_55, D_56))=k1_enumset1(B_54, C_55, D_56))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_144])).
% 2.97/1.52  tff(c_61, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.52  tff(c_14, plain, (![A_28]: (k1_enumset1(A_28, A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.97/1.52  tff(c_68, plain, (![B_36]: (k2_tarski(B_36, B_36)=k1_tarski(B_36))), inference(superposition, [status(thm), theory('equality')], [c_61, c_14])).
% 2.97/1.52  tff(c_228, plain, (![G_68, B_66, F_63, C_67, E_65, A_64, D_69]: (k2_xboole_0(k2_tarski(A_64, B_66), k3_enumset1(C_67, D_69, E_65, F_63, G_68))=k5_enumset1(A_64, B_66, C_67, D_69, E_65, F_63, G_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.52  tff(c_243, plain, (![B_66, A_29, A_64, C_31, B_30]: (k5_enumset1(A_64, B_66, A_29, A_29, A_29, B_30, C_31)=k2_xboole_0(k2_tarski(A_64, B_66), k1_enumset1(A_29, B_30, C_31)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_228])).
% 2.97/1.52  tff(c_288, plain, (![B_75, D_73, E_77, F_76, A_78, C_72, G_74]: (k2_xboole_0(k3_enumset1(A_78, B_75, C_72, D_73, E_77), k2_tarski(F_76, G_74))=k5_enumset1(A_78, B_75, C_72, D_73, E_77, F_76, G_74))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.52  tff(c_880, plain, (![C_103, A_102, B_101, F_100, G_104]: (k5_enumset1(A_102, A_102, A_102, B_101, C_103, F_100, G_104)=k2_xboole_0(k1_enumset1(A_102, B_101, C_103), k2_tarski(F_100, G_104)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_288])).
% 2.97/1.52  tff(c_900, plain, (![A_29, B_30, C_31]: (k2_xboole_0(k1_enumset1(A_29, A_29, A_29), k2_tarski(B_30, C_31))=k2_xboole_0(k2_tarski(A_29, A_29), k1_enumset1(A_29, B_30, C_31)))), inference(superposition, [status(thm), theory('equality')], [c_243, c_880])).
% 2.97/1.52  tff(c_929, plain, (![A_105, B_106, C_107]: (k2_xboole_0(k1_tarski(A_105), k2_tarski(B_106, C_107))=k1_enumset1(A_105, B_106, C_107))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_68, c_14, c_900])).
% 2.97/1.52  tff(c_1213, plain, (![A_121, A_122, B_123]: (k2_xboole_0(k1_tarski(A_121), k2_tarski(A_122, B_123))=k1_enumset1(A_121, B_123, A_122))), inference(superposition, [status(thm), theory('equality')], [c_2, c_929])).
% 2.97/1.52  tff(c_921, plain, (![A_29, B_30, C_31]: (k2_xboole_0(k1_tarski(A_29), k2_tarski(B_30, C_31))=k1_enumset1(A_29, B_30, C_31))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_68, c_14, c_900])).
% 2.97/1.52  tff(c_1219, plain, (![A_121, B_123, A_122]: (k1_enumset1(A_121, B_123, A_122)=k1_enumset1(A_121, A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_1213, c_921])).
% 2.97/1.52  tff(c_18, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.97/1.52  tff(c_1259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1219, c_18])).
% 2.97/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.52  
% 2.97/1.52  Inference rules
% 2.97/1.52  ----------------------
% 2.97/1.52  #Ref     : 0
% 2.97/1.52  #Sup     : 299
% 2.97/1.52  #Fact    : 0
% 2.97/1.52  #Define  : 0
% 2.97/1.52  #Split   : 0
% 2.97/1.52  #Chain   : 0
% 2.97/1.52  #Close   : 0
% 2.97/1.52  
% 2.97/1.52  Ordering : KBO
% 2.97/1.52  
% 2.97/1.52  Simplification rules
% 2.97/1.52  ----------------------
% 2.97/1.52  #Subsume      : 11
% 2.97/1.52  #Demod        : 196
% 2.97/1.52  #Tautology    : 208
% 2.97/1.52  #SimpNegUnit  : 0
% 2.97/1.52  #BackRed      : 3
% 2.97/1.52  
% 2.97/1.52  #Partial instantiations: 0
% 2.97/1.52  #Strategies tried      : 1
% 2.97/1.52  
% 2.97/1.52  Timing (in seconds)
% 2.97/1.52  ----------------------
% 2.97/1.52  Preprocessing        : 0.26
% 2.97/1.52  Parsing              : 0.14
% 2.97/1.52  CNF conversion       : 0.02
% 2.97/1.52  Main loop            : 0.46
% 2.97/1.52  Inferencing          : 0.19
% 2.97/1.52  Reduction            : 0.17
% 2.97/1.52  Demodulation         : 0.14
% 2.97/1.52  BG Simplification    : 0.02
% 2.97/1.52  Subsumption          : 0.05
% 2.97/1.52  Abstraction          : 0.03
% 2.97/1.52  MUC search           : 0.00
% 2.97/1.52  Cooper               : 0.00
% 2.97/1.52  Total                : 0.75
% 2.97/1.52  Index Insertion      : 0.00
% 2.97/1.52  Index Deletion       : 0.00
% 2.97/1.52  Index Matching       : 0.00
% 2.97/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

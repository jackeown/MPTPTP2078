%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:13 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   33 (  53 expanded)
%              Number of equality atoms :   32 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_tarski(A_3,B_4),k1_tarski(C_5)) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_54] : k2_tarski(A_54,A_54) = k1_tarski(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [A_62,B_63,C_64] : k2_xboole_0(k2_tarski(A_62,B_63),k1_tarski(C_64)) = k1_enumset1(A_62,B_63,C_64) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_54,C_64] : k2_xboole_0(k1_tarski(A_54),k1_tarski(C_64)) = k1_enumset1(A_54,A_54,C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_54])).

tff(c_66,plain,(
    ! [A_54,C_64] : k2_xboole_0(k1_tarski(A_54),k1_tarski(C_64)) = k2_tarski(A_54,C_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_63])).

tff(c_67,plain,(
    ! [A_65,B_66,C_67,D_68] : k2_xboole_0(k1_tarski(A_65),k1_enumset1(B_66,C_67,D_68)) = k2_enumset1(A_65,B_66,C_67,D_68) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_71,A_72,B_73] : k2_xboole_0(k1_tarski(A_71),k2_tarski(A_72,B_73)) = k2_enumset1(A_71,A_72,A_72,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_67])).

tff(c_103,plain,(
    ! [A_71,A_54] : k2_xboole_0(k1_tarski(A_71),k1_tarski(A_54)) = k2_enumset1(A_71,A_54,A_54,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_88])).

tff(c_108,plain,(
    ! [A_71,A_54] : k2_enumset1(A_71,A_54,A_54,A_54) = k2_tarski(A_71,A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_103])).

tff(c_244,plain,(
    ! [A_98,D_96,B_95,C_94,E_97] : k2_xboole_0(k2_enumset1(A_98,B_95,C_94,D_96),k1_tarski(E_97)) = k3_enumset1(A_98,B_95,C_94,D_96,E_97) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_256,plain,(
    ! [A_71,A_54,E_97] : k3_enumset1(A_71,A_54,A_54,A_54,E_97) = k2_xboole_0(k2_tarski(A_71,A_54),k1_tarski(E_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_244])).

tff(c_262,plain,(
    ! [A_71,A_54,E_97] : k3_enumset1(A_71,A_54,A_54,A_54,E_97) = k1_enumset1(A_71,A_54,E_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_256])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [C_89,B_91,E_92,A_93,D_90] : k2_xboole_0(k2_tarski(A_93,B_91),k1_enumset1(C_89,D_90,E_92)) = k3_enumset1(A_93,B_91,C_89,D_90,E_92) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_240,plain,(
    ! [A_54,C_89,D_90,E_92] : k3_enumset1(A_54,A_54,C_89,D_90,E_92) = k2_xboole_0(k1_tarski(A_54),k1_enumset1(C_89,D_90,E_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_228])).

tff(c_351,plain,(
    ! [A_110,C_111,D_112,E_113] : k3_enumset1(A_110,A_110,C_111,D_112,E_113) = k2_enumset1(A_110,C_111,D_112,E_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_240])).

tff(c_377,plain,(
    ! [A_54,E_97] : k2_enumset1(A_54,A_54,A_54,E_97) = k1_enumset1(A_54,A_54,E_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_351])).

tff(c_466,plain,(
    ! [A_122,E_123] : k2_enumset1(A_122,A_122,A_122,E_123) = k2_tarski(A_122,E_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_377])).

tff(c_12,plain,(
    ! [C_22,D_23,A_20,B_21,E_24] : k2_xboole_0(k2_enumset1(A_20,B_21,C_22,D_23),k1_tarski(E_24)) = k3_enumset1(A_20,B_21,C_22,D_23,E_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_482,plain,(
    ! [A_122,E_123,E_24] : k3_enumset1(A_122,A_122,A_122,E_123,E_24) = k2_xboole_0(k2_tarski(A_122,E_123),k1_tarski(E_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_12])).

tff(c_1591,plain,(
    ! [A_183,E_184,E_185] : k3_enumset1(A_183,A_183,A_183,E_184,E_185) = k1_enumset1(A_183,E_184,E_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_482])).

tff(c_243,plain,(
    ! [A_54,C_89,D_90,E_92] : k3_enumset1(A_54,A_54,C_89,D_90,E_92) = k2_enumset1(A_54,C_89,D_90,E_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_240])).

tff(c_1624,plain,(
    ! [A_183,E_184,E_185] : k2_enumset1(A_183,A_183,E_184,E_185) = k1_enumset1(A_183,E_184,E_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_1591,c_243])).

tff(c_26,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.53  
% 3.26/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.53  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.26/1.53  
% 3.26/1.53  %Foreground sorts:
% 3.26/1.53  
% 3.26/1.53  
% 3.26/1.53  %Background operators:
% 3.26/1.53  
% 3.26/1.53  
% 3.26/1.53  %Foreground operators:
% 3.26/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.26/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.53  
% 3.26/1.54  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.26/1.54  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.26/1.54  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.26/1.54  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.26/1.54  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.26/1.54  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 3.26/1.54  tff(f_52, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.26/1.54  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_tarski(A_3, B_4), k1_tarski(C_5))=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.54  tff(c_24, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.26/1.54  tff(c_22, plain, (![A_54]: (k2_tarski(A_54, A_54)=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.26/1.54  tff(c_54, plain, (![A_62, B_63, C_64]: (k2_xboole_0(k2_tarski(A_62, B_63), k1_tarski(C_64))=k1_enumset1(A_62, B_63, C_64))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.54  tff(c_63, plain, (![A_54, C_64]: (k2_xboole_0(k1_tarski(A_54), k1_tarski(C_64))=k1_enumset1(A_54, A_54, C_64))), inference(superposition, [status(thm), theory('equality')], [c_22, c_54])).
% 3.26/1.54  tff(c_66, plain, (![A_54, C_64]: (k2_xboole_0(k1_tarski(A_54), k1_tarski(C_64))=k2_tarski(A_54, C_64))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_63])).
% 3.26/1.54  tff(c_67, plain, (![A_65, B_66, C_67, D_68]: (k2_xboole_0(k1_tarski(A_65), k1_enumset1(B_66, C_67, D_68))=k2_enumset1(A_65, B_66, C_67, D_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.54  tff(c_88, plain, (![A_71, A_72, B_73]: (k2_xboole_0(k1_tarski(A_71), k2_tarski(A_72, B_73))=k2_enumset1(A_71, A_72, A_72, B_73))), inference(superposition, [status(thm), theory('equality')], [c_24, c_67])).
% 3.26/1.54  tff(c_103, plain, (![A_71, A_54]: (k2_xboole_0(k1_tarski(A_71), k1_tarski(A_54))=k2_enumset1(A_71, A_54, A_54, A_54))), inference(superposition, [status(thm), theory('equality')], [c_22, c_88])).
% 3.26/1.54  tff(c_108, plain, (![A_71, A_54]: (k2_enumset1(A_71, A_54, A_54, A_54)=k2_tarski(A_71, A_54))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_103])).
% 3.26/1.54  tff(c_244, plain, (![A_98, D_96, B_95, C_94, E_97]: (k2_xboole_0(k2_enumset1(A_98, B_95, C_94, D_96), k1_tarski(E_97))=k3_enumset1(A_98, B_95, C_94, D_96, E_97))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.54  tff(c_256, plain, (![A_71, A_54, E_97]: (k3_enumset1(A_71, A_54, A_54, A_54, E_97)=k2_xboole_0(k2_tarski(A_71, A_54), k1_tarski(E_97)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_244])).
% 3.26/1.54  tff(c_262, plain, (![A_71, A_54, E_97]: (k3_enumset1(A_71, A_54, A_54, A_54, E_97)=k1_enumset1(A_71, A_54, E_97))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_256])).
% 3.26/1.54  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.54  tff(c_228, plain, (![C_89, B_91, E_92, A_93, D_90]: (k2_xboole_0(k2_tarski(A_93, B_91), k1_enumset1(C_89, D_90, E_92))=k3_enumset1(A_93, B_91, C_89, D_90, E_92))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.54  tff(c_240, plain, (![A_54, C_89, D_90, E_92]: (k3_enumset1(A_54, A_54, C_89, D_90, E_92)=k2_xboole_0(k1_tarski(A_54), k1_enumset1(C_89, D_90, E_92)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_228])).
% 3.26/1.54  tff(c_351, plain, (![A_110, C_111, D_112, E_113]: (k3_enumset1(A_110, A_110, C_111, D_112, E_113)=k2_enumset1(A_110, C_111, D_112, E_113))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_240])).
% 3.26/1.54  tff(c_377, plain, (![A_54, E_97]: (k2_enumset1(A_54, A_54, A_54, E_97)=k1_enumset1(A_54, A_54, E_97))), inference(superposition, [status(thm), theory('equality')], [c_262, c_351])).
% 3.26/1.54  tff(c_466, plain, (![A_122, E_123]: (k2_enumset1(A_122, A_122, A_122, E_123)=k2_tarski(A_122, E_123))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_377])).
% 3.26/1.54  tff(c_12, plain, (![C_22, D_23, A_20, B_21, E_24]: (k2_xboole_0(k2_enumset1(A_20, B_21, C_22, D_23), k1_tarski(E_24))=k3_enumset1(A_20, B_21, C_22, D_23, E_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.54  tff(c_482, plain, (![A_122, E_123, E_24]: (k3_enumset1(A_122, A_122, A_122, E_123, E_24)=k2_xboole_0(k2_tarski(A_122, E_123), k1_tarski(E_24)))), inference(superposition, [status(thm), theory('equality')], [c_466, c_12])).
% 3.26/1.54  tff(c_1591, plain, (![A_183, E_184, E_185]: (k3_enumset1(A_183, A_183, A_183, E_184, E_185)=k1_enumset1(A_183, E_184, E_185))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_482])).
% 3.26/1.54  tff(c_243, plain, (![A_54, C_89, D_90, E_92]: (k3_enumset1(A_54, A_54, C_89, D_90, E_92)=k2_enumset1(A_54, C_89, D_90, E_92))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_240])).
% 3.26/1.54  tff(c_1624, plain, (![A_183, E_184, E_185]: (k2_enumset1(A_183, A_183, E_184, E_185)=k1_enumset1(A_183, E_184, E_185))), inference(superposition, [status(thm), theory('equality')], [c_1591, c_243])).
% 3.26/1.54  tff(c_26, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.26/1.54  tff(c_1691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1624, c_26])).
% 3.26/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.54  
% 3.26/1.54  Inference rules
% 3.26/1.54  ----------------------
% 3.26/1.54  #Ref     : 0
% 3.26/1.54  #Sup     : 382
% 3.26/1.54  #Fact    : 0
% 3.26/1.54  #Define  : 0
% 3.26/1.54  #Split   : 0
% 3.26/1.54  #Chain   : 0
% 3.26/1.54  #Close   : 0
% 3.26/1.54  
% 3.26/1.54  Ordering : KBO
% 3.26/1.54  
% 3.26/1.54  Simplification rules
% 3.26/1.54  ----------------------
% 3.26/1.54  #Subsume      : 9
% 3.26/1.54  #Demod        : 396
% 3.26/1.54  #Tautology    : 283
% 3.26/1.54  #SimpNegUnit  : 0
% 3.26/1.54  #BackRed      : 6
% 3.26/1.54  
% 3.26/1.54  #Partial instantiations: 0
% 3.26/1.54  #Strategies tried      : 1
% 3.26/1.54  
% 3.26/1.54  Timing (in seconds)
% 3.26/1.54  ----------------------
% 3.26/1.54  Preprocessing        : 0.33
% 3.26/1.54  Parsing              : 0.17
% 3.26/1.54  CNF conversion       : 0.02
% 3.26/1.55  Main loop            : 0.43
% 3.26/1.55  Inferencing          : 0.18
% 3.26/1.55  Reduction            : 0.16
% 3.26/1.55  Demodulation         : 0.13
% 3.26/1.55  BG Simplification    : 0.03
% 3.26/1.55  Subsumption          : 0.04
% 3.26/1.55  Abstraction          : 0.03
% 3.26/1.55  MUC search           : 0.00
% 3.26/1.55  Cooper               : 0.00
% 3.26/1.55  Total                : 0.78
% 3.26/1.55  Index Insertion      : 0.00
% 3.26/1.55  Index Deletion       : 0.00
% 3.26/1.55  Index Matching       : 0.00
% 3.26/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

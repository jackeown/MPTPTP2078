%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:42 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 154 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :   37 ( 136 expanded)
%              Number of equality atoms :   36 ( 135 expanded)
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

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_43,B_44,C_45] : k2_enumset1(A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_40] : k2_tarski(A_40,A_40) = k1_tarski(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_46,B_47,C_48,D_49] : k3_enumset1(A_46,A_46,B_47,C_48,D_49) = k2_enumset1(A_46,B_47,C_48,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_129,plain,(
    ! [A_92,D_89,C_91,B_90,E_93] : k2_xboole_0(k1_enumset1(A_92,B_90,C_91),k2_tarski(D_89,E_93)) = k3_enumset1(A_92,B_90,C_91,D_89,E_93) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,(
    ! [A_41,B_42,D_89,E_93] : k3_enumset1(A_41,A_41,B_42,D_89,E_93) = k2_xboole_0(k2_tarski(A_41,B_42),k2_tarski(D_89,E_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_129])).

tff(c_151,plain,(
    ! [A_94,B_95,D_96,E_97] : k2_xboole_0(k2_tarski(A_94,B_95),k2_tarski(D_96,E_97)) = k2_enumset1(A_94,B_95,D_96,E_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_138])).

tff(c_172,plain,(
    ! [A_40,D_96,E_97] : k2_xboole_0(k1_tarski(A_40),k2_tarski(D_96,E_97)) = k2_enumset1(A_40,A_40,D_96,E_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_151])).

tff(c_179,plain,(
    ! [A_98,D_99,E_100] : k2_xboole_0(k1_tarski(A_98),k2_tarski(D_99,E_100)) = k1_enumset1(A_98,D_99,E_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_172])).

tff(c_289,plain,(
    ! [A_110,B_111,A_112] : k2_xboole_0(k1_tarski(A_110),k2_tarski(B_111,A_112)) = k1_enumset1(A_110,A_112,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_179])).

tff(c_178,plain,(
    ! [A_40,D_96,E_97] : k2_xboole_0(k1_tarski(A_40),k2_tarski(D_96,E_97)) = k1_enumset1(A_40,D_96,E_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_172])).

tff(c_295,plain,(
    ! [A_110,B_111,A_112] : k1_enumset1(A_110,B_111,A_112) = k1_enumset1(A_110,A_112,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_178])).

tff(c_274,plain,(
    ! [A_109,C_105,B_108,E_107,D_106] : k2_xboole_0(k2_enumset1(A_109,B_108,C_105,D_106),k1_tarski(E_107)) = k3_enumset1(A_109,B_108,C_105,D_106,E_107) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_283,plain,(
    ! [A_43,B_44,C_45,E_107] : k3_enumset1(A_43,A_43,B_44,C_45,E_107) = k2_xboole_0(k1_enumset1(A_43,B_44,C_45),k1_tarski(E_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_274])).

tff(c_286,plain,(
    ! [A_43,B_44,C_45,E_107] : k2_xboole_0(k1_enumset1(A_43,B_44,C_45),k1_tarski(E_107)) = k2_enumset1(A_43,B_44,C_45,E_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_283])).

tff(c_147,plain,(
    ! [A_92,B_90,C_91,A_40] : k3_enumset1(A_92,B_90,C_91,A_40,A_40) = k2_xboole_0(k1_enumset1(A_92,B_90,C_91),k1_tarski(A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_129])).

tff(c_1166,plain,(
    ! [A_184,B_185,C_186,A_187] : k3_enumset1(A_184,B_185,C_186,A_187,A_187) = k2_enumset1(A_184,B_185,C_186,A_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_147])).

tff(c_1181,plain,(
    ! [B_185,C_186,A_187] : k2_enumset1(B_185,C_186,A_187,A_187) = k2_enumset1(B_185,B_185,C_186,A_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_24])).

tff(c_1199,plain,(
    ! [B_185,C_186,A_187] : k2_enumset1(B_185,C_186,A_187,A_187) = k1_enumset1(B_185,C_186,A_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1181])).

tff(c_501,plain,(
    ! [A_141,B_142,A_143] : k2_xboole_0(k2_tarski(A_141,B_142),k1_tarski(A_143)) = k2_enumset1(A_141,B_142,A_143,A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_151])).

tff(c_662,plain,(
    ! [B_155,A_156,A_157] : k2_xboole_0(k2_tarski(B_155,A_156),k1_tarski(A_157)) = k2_enumset1(A_156,B_155,A_157,A_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_501])).

tff(c_175,plain,(
    ! [A_94,B_95,A_40] : k2_xboole_0(k2_tarski(A_94,B_95),k1_tarski(A_40)) = k2_enumset1(A_94,B_95,A_40,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_151])).

tff(c_682,plain,(
    ! [B_155,A_156,A_157] : k2_enumset1(B_155,A_156,A_157,A_157) = k2_enumset1(A_156,B_155,A_157,A_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_175])).

tff(c_1208,plain,(
    ! [B_155,A_156,A_157] : k1_enumset1(B_155,A_156,A_157) = k1_enumset1(A_156,B_155,A_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_1199,c_682])).

tff(c_32,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_324,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_32])).

tff(c_1272,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_324])).

tff(c_1275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_1272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:10:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.50  
% 3.12/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.50  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.12/1.50  
% 3.12/1.50  %Foreground sorts:
% 3.12/1.50  
% 3.12/1.50  
% 3.12/1.50  %Background operators:
% 3.12/1.50  
% 3.12/1.50  
% 3.12/1.50  %Foreground operators:
% 3.12/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.12/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.12/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.50  
% 3.39/1.52  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.39/1.52  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.39/1.52  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.39/1.52  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.39/1.52  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.39/1.52  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 3.39/1.52  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.39/1.52  tff(f_58, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 3.39/1.52  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.52  tff(c_22, plain, (![A_43, B_44, C_45]: (k2_enumset1(A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.52  tff(c_18, plain, (![A_40]: (k2_tarski(A_40, A_40)=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.39/1.52  tff(c_24, plain, (![A_46, B_47, C_48, D_49]: (k3_enumset1(A_46, A_46, B_47, C_48, D_49)=k2_enumset1(A_46, B_47, C_48, D_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.39/1.52  tff(c_20, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.39/1.52  tff(c_129, plain, (![A_92, D_89, C_91, B_90, E_93]: (k2_xboole_0(k1_enumset1(A_92, B_90, C_91), k2_tarski(D_89, E_93))=k3_enumset1(A_92, B_90, C_91, D_89, E_93))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.52  tff(c_138, plain, (![A_41, B_42, D_89, E_93]: (k3_enumset1(A_41, A_41, B_42, D_89, E_93)=k2_xboole_0(k2_tarski(A_41, B_42), k2_tarski(D_89, E_93)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_129])).
% 3.39/1.52  tff(c_151, plain, (![A_94, B_95, D_96, E_97]: (k2_xboole_0(k2_tarski(A_94, B_95), k2_tarski(D_96, E_97))=k2_enumset1(A_94, B_95, D_96, E_97))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_138])).
% 3.39/1.52  tff(c_172, plain, (![A_40, D_96, E_97]: (k2_xboole_0(k1_tarski(A_40), k2_tarski(D_96, E_97))=k2_enumset1(A_40, A_40, D_96, E_97))), inference(superposition, [status(thm), theory('equality')], [c_18, c_151])).
% 3.39/1.52  tff(c_179, plain, (![A_98, D_99, E_100]: (k2_xboole_0(k1_tarski(A_98), k2_tarski(D_99, E_100))=k1_enumset1(A_98, D_99, E_100))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_172])).
% 3.39/1.52  tff(c_289, plain, (![A_110, B_111, A_112]: (k2_xboole_0(k1_tarski(A_110), k2_tarski(B_111, A_112))=k1_enumset1(A_110, A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_6, c_179])).
% 3.39/1.52  tff(c_178, plain, (![A_40, D_96, E_97]: (k2_xboole_0(k1_tarski(A_40), k2_tarski(D_96, E_97))=k1_enumset1(A_40, D_96, E_97))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_172])).
% 3.39/1.52  tff(c_295, plain, (![A_110, B_111, A_112]: (k1_enumset1(A_110, B_111, A_112)=k1_enumset1(A_110, A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_289, c_178])).
% 3.39/1.52  tff(c_274, plain, (![A_109, C_105, B_108, E_107, D_106]: (k2_xboole_0(k2_enumset1(A_109, B_108, C_105, D_106), k1_tarski(E_107))=k3_enumset1(A_109, B_108, C_105, D_106, E_107))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.39/1.52  tff(c_283, plain, (![A_43, B_44, C_45, E_107]: (k3_enumset1(A_43, A_43, B_44, C_45, E_107)=k2_xboole_0(k1_enumset1(A_43, B_44, C_45), k1_tarski(E_107)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_274])).
% 3.39/1.52  tff(c_286, plain, (![A_43, B_44, C_45, E_107]: (k2_xboole_0(k1_enumset1(A_43, B_44, C_45), k1_tarski(E_107))=k2_enumset1(A_43, B_44, C_45, E_107))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_283])).
% 3.39/1.52  tff(c_147, plain, (![A_92, B_90, C_91, A_40]: (k3_enumset1(A_92, B_90, C_91, A_40, A_40)=k2_xboole_0(k1_enumset1(A_92, B_90, C_91), k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_129])).
% 3.39/1.52  tff(c_1166, plain, (![A_184, B_185, C_186, A_187]: (k3_enumset1(A_184, B_185, C_186, A_187, A_187)=k2_enumset1(A_184, B_185, C_186, A_187))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_147])).
% 3.39/1.52  tff(c_1181, plain, (![B_185, C_186, A_187]: (k2_enumset1(B_185, C_186, A_187, A_187)=k2_enumset1(B_185, B_185, C_186, A_187))), inference(superposition, [status(thm), theory('equality')], [c_1166, c_24])).
% 3.39/1.52  tff(c_1199, plain, (![B_185, C_186, A_187]: (k2_enumset1(B_185, C_186, A_187, A_187)=k1_enumset1(B_185, C_186, A_187))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1181])).
% 3.39/1.52  tff(c_501, plain, (![A_141, B_142, A_143]: (k2_xboole_0(k2_tarski(A_141, B_142), k1_tarski(A_143))=k2_enumset1(A_141, B_142, A_143, A_143))), inference(superposition, [status(thm), theory('equality')], [c_18, c_151])).
% 3.39/1.52  tff(c_662, plain, (![B_155, A_156, A_157]: (k2_xboole_0(k2_tarski(B_155, A_156), k1_tarski(A_157))=k2_enumset1(A_156, B_155, A_157, A_157))), inference(superposition, [status(thm), theory('equality')], [c_6, c_501])).
% 3.39/1.52  tff(c_175, plain, (![A_94, B_95, A_40]: (k2_xboole_0(k2_tarski(A_94, B_95), k1_tarski(A_40))=k2_enumset1(A_94, B_95, A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_18, c_151])).
% 3.39/1.52  tff(c_682, plain, (![B_155, A_156, A_157]: (k2_enumset1(B_155, A_156, A_157, A_157)=k2_enumset1(A_156, B_155, A_157, A_157))), inference(superposition, [status(thm), theory('equality')], [c_662, c_175])).
% 3.39/1.52  tff(c_1208, plain, (![B_155, A_156, A_157]: (k1_enumset1(B_155, A_156, A_157)=k1_enumset1(A_156, B_155, A_157))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_1199, c_682])).
% 3.39/1.52  tff(c_32, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.52  tff(c_324, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_32])).
% 3.39/1.52  tff(c_1272, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_324])).
% 3.39/1.52  tff(c_1275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_1272])).
% 3.39/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.52  
% 3.39/1.52  Inference rules
% 3.39/1.52  ----------------------
% 3.39/1.52  #Ref     : 0
% 3.39/1.52  #Sup     : 303
% 3.39/1.52  #Fact    : 0
% 3.39/1.52  #Define  : 0
% 3.39/1.52  #Split   : 0
% 3.39/1.52  #Chain   : 0
% 3.39/1.52  #Close   : 0
% 3.39/1.52  
% 3.39/1.52  Ordering : KBO
% 3.39/1.52  
% 3.39/1.52  Simplification rules
% 3.39/1.52  ----------------------
% 3.39/1.52  #Subsume      : 21
% 3.39/1.52  #Demod        : 177
% 3.39/1.52  #Tautology    : 190
% 3.39/1.52  #SimpNegUnit  : 0
% 3.39/1.52  #BackRed      : 8
% 3.39/1.52  
% 3.39/1.52  #Partial instantiations: 0
% 3.39/1.52  #Strategies tried      : 1
% 3.39/1.52  
% 3.39/1.52  Timing (in seconds)
% 3.39/1.52  ----------------------
% 3.39/1.52  Preprocessing        : 0.32
% 3.39/1.52  Parsing              : 0.17
% 3.39/1.52  CNF conversion       : 0.02
% 3.39/1.52  Main loop            : 0.43
% 3.39/1.52  Inferencing          : 0.17
% 3.39/1.52  Reduction            : 0.17
% 3.39/1.52  Demodulation         : 0.14
% 3.39/1.52  BG Simplification    : 0.03
% 3.39/1.52  Subsumption          : 0.05
% 3.39/1.52  Abstraction          : 0.03
% 3.39/1.52  MUC search           : 0.00
% 3.39/1.52  Cooper               : 0.00
% 3.39/1.52  Total                : 0.78
% 3.39/1.52  Index Insertion      : 0.00
% 3.39/1.52  Index Deletion       : 0.00
% 3.39/1.52  Index Matching       : 0.00
% 3.39/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

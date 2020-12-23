%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:52 EST 2020

% Result     : Theorem 15.65s
% Output     : CNFRefutation 15.80s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 193 expanded)
%              Number of leaves         :   31 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 ( 174 expanded)
%              Number of equality atoms :   44 ( 173 expanded)
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

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_8,plain,(
    ! [A_7,B_8,D_10,C_9] : k2_enumset1(A_7,B_8,D_10,C_9) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_207,plain,(
    ! [A_121,B_122,D_123,C_124] : k2_enumset1(A_121,B_122,D_123,C_124) = k2_enumset1(A_121,B_122,C_124,D_123) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11,D_14,C_13,B_12] : k2_enumset1(A_11,D_14,C_13,B_12) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_239,plain,(
    ! [A_121,C_124,D_123,B_122] : k2_enumset1(A_121,C_124,D_123,B_122) = k2_enumset1(A_121,B_122,C_124,D_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_10])).

tff(c_610,plain,(
    ! [A_152,B_150,C_148,D_149,E_151] : k2_xboole_0(k2_tarski(A_152,B_150),k1_enumset1(C_148,D_149,E_151)) = k3_enumset1(A_152,B_150,C_148,D_149,E_151) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_619,plain,(
    ! [A_152,B_150,C_148,D_149,E_151] : k2_xboole_0(k1_enumset1(C_148,D_149,E_151),k2_tarski(A_152,B_150)) = k3_enumset1(A_152,B_150,C_148,D_149,E_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_2])).

tff(c_36,plain,(
    ! [E_88,C_86,B_85,D_87,A_84] : k4_enumset1(A_84,A_84,B_85,C_86,D_87,E_88) = k3_enumset1(A_84,B_85,C_86,D_87,E_88) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_77,B_78,C_79] : k2_enumset1(A_77,A_77,B_78,C_79) = k1_enumset1(A_77,B_78,C_79) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_283,plain,(
    ! [A_77,C_79,B_78] : k2_enumset1(A_77,A_77,C_79,B_78) = k1_enumset1(A_77,B_78,C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_207])).

tff(c_38,plain,(
    ! [D_92,C_91,F_94,A_89,B_90,E_93] : k5_enumset1(A_89,A_89,B_90,C_91,D_92,E_93,F_94) = k4_enumset1(A_89,B_90,C_91,D_92,E_93,F_94) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [A_80,B_81,C_82,D_83] : k3_enumset1(A_80,A_80,B_81,C_82,D_83) = k2_enumset1(A_80,B_81,C_82,D_83) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_979,plain,(
    ! [A_185,E_184,D_183,C_180,B_182,G_181,F_186] : k2_xboole_0(k3_enumset1(A_185,B_182,C_180,D_183,E_184),k2_tarski(F_186,G_181)) = k5_enumset1(A_185,B_182,C_180,D_183,E_184,F_186,G_181) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_994,plain,(
    ! [B_81,D_83,A_80,G_181,F_186,C_82] : k5_enumset1(A_80,A_80,B_81,C_82,D_83,F_186,G_181) = k2_xboole_0(k2_enumset1(A_80,B_81,C_82,D_83),k2_tarski(F_186,G_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_979])).

tff(c_3230,plain,(
    ! [G_285,F_282,A_283,D_287,C_286,B_284] : k2_xboole_0(k2_enumset1(A_283,B_284,C_286,D_287),k2_tarski(F_282,G_285)) = k4_enumset1(A_283,B_284,C_286,D_287,F_282,G_285) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_994])).

tff(c_3299,plain,(
    ! [G_285,F_282,B_78,A_77,C_79] : k4_enumset1(A_77,A_77,C_79,B_78,F_282,G_285) = k2_xboole_0(k1_enumset1(A_77,B_78,C_79),k2_tarski(F_282,G_285)) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_3230])).

tff(c_6581,plain,(
    ! [B_385,C_387,A_384,G_383,F_386] : k3_enumset1(F_386,G_383,A_384,B_385,C_387) = k3_enumset1(A_384,C_387,B_385,F_386,G_383) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_36,c_3299])).

tff(c_6737,plain,(
    ! [A_384,C_387,B_385,G_383] : k3_enumset1(A_384,C_387,B_385,G_383,G_383) = k2_enumset1(G_383,A_384,B_385,C_387) ),
    inference(superposition,[status(thm),theory(equality)],[c_6581,c_34])).

tff(c_766,plain,(
    ! [C_170,D_171,A_175,B_173,G_174,F_169,E_172] : k2_xboole_0(k4_enumset1(A_175,B_173,C_170,D_171,E_172,F_169),k1_tarski(G_174)) = k5_enumset1(A_175,B_173,C_170,D_171,E_172,F_169,G_174) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_781,plain,(
    ! [E_88,C_86,B_85,D_87,A_84,G_174] : k5_enumset1(A_84,A_84,B_85,C_86,D_87,E_88,G_174) = k2_xboole_0(k3_enumset1(A_84,B_85,C_86,D_87,E_88),k1_tarski(G_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_766])).

tff(c_790,plain,(
    ! [E_88,C_86,B_85,D_87,A_84,G_174] : k2_xboole_0(k3_enumset1(A_84,B_85,C_86,D_87,E_88),k1_tarski(G_174)) = k4_enumset1(A_84,B_85,C_86,D_87,E_88,G_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_781])).

tff(c_28,plain,(
    ! [A_74] : k2_tarski(A_74,A_74) = k1_tarski(A_74) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1003,plain,(
    ! [A_74,A_185,E_184,D_183,C_180,B_182] : k5_enumset1(A_185,B_182,C_180,D_183,E_184,A_74,A_74) = k2_xboole_0(k3_enumset1(A_185,B_182,C_180,D_183,E_184),k1_tarski(A_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_979])).

tff(c_3601,plain,(
    ! [C_296,B_293,A_291,A_294,D_292,E_295] : k5_enumset1(A_291,B_293,C_296,D_292,E_295,A_294,A_294) = k4_enumset1(A_291,B_293,C_296,D_292,E_295,A_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_1003])).

tff(c_3614,plain,(
    ! [C_296,B_293,A_294,D_292,E_295] : k4_enumset1(B_293,C_296,D_292,E_295,A_294,A_294) = k4_enumset1(B_293,B_293,C_296,D_292,E_295,A_294) ),
    inference(superposition,[status(thm),theory(equality)],[c_3601,c_38])).

tff(c_19872,plain,(
    ! [B_587,A_586,E_589,C_585,D_588] : k4_enumset1(B_587,C_585,D_588,E_589,A_586,A_586) = k3_enumset1(B_587,C_585,D_588,E_589,A_586) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3614])).

tff(c_19900,plain,(
    ! [C_585,D_588,E_589,A_586] : k3_enumset1(C_585,D_588,E_589,A_586,A_586) = k3_enumset1(C_585,C_585,D_588,E_589,A_586) ),
    inference(superposition,[status(thm),theory(equality)],[c_19872,c_36])).

tff(c_19915,plain,(
    ! [C_585,D_588,E_589,A_586] : k2_enumset1(C_585,D_588,E_589,A_586) = k2_enumset1(A_586,C_585,E_589,D_588) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6737,c_34,c_19900])).

tff(c_42,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_42])).

tff(c_44,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_43])).

tff(c_19918,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19915,c_19915,c_19915,c_44])).

tff(c_19921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_239,c_10,c_19918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.65/5.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.65/5.68  
% 15.65/5.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.65/5.69  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.65/5.69  
% 15.65/5.69  %Foreground sorts:
% 15.65/5.69  
% 15.65/5.69  
% 15.65/5.69  %Background operators:
% 15.65/5.69  
% 15.65/5.69  
% 15.65/5.69  %Foreground operators:
% 15.65/5.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.65/5.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.65/5.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.65/5.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.65/5.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.65/5.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.65/5.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.65/5.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.65/5.69  tff('#skF_2', type, '#skF_2': $i).
% 15.65/5.69  tff('#skF_3', type, '#skF_3': $i).
% 15.65/5.69  tff('#skF_1', type, '#skF_1': $i).
% 15.65/5.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.65/5.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.65/5.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.65/5.69  tff('#skF_4', type, '#skF_4': $i).
% 15.65/5.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.65/5.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.65/5.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.65/5.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.65/5.69  
% 15.80/5.71  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 15.80/5.71  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 15.80/5.71  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 15.80/5.71  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 15.80/5.71  tff(f_61, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 15.80/5.71  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 15.80/5.71  tff(f_63, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 15.80/5.71  tff(f_59, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 15.80/5.71  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 15.80/5.71  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 15.80/5.71  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 15.80/5.71  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 15.80/5.71  tff(c_8, plain, (![A_7, B_8, D_10, C_9]: (k2_enumset1(A_7, B_8, D_10, C_9)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.80/5.71  tff(c_207, plain, (![A_121, B_122, D_123, C_124]: (k2_enumset1(A_121, B_122, D_123, C_124)=k2_enumset1(A_121, B_122, C_124, D_123))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.80/5.71  tff(c_10, plain, (![A_11, D_14, C_13, B_12]: (k2_enumset1(A_11, D_14, C_13, B_12)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.80/5.71  tff(c_239, plain, (![A_121, C_124, D_123, B_122]: (k2_enumset1(A_121, C_124, D_123, B_122)=k2_enumset1(A_121, B_122, C_124, D_123))), inference(superposition, [status(thm), theory('equality')], [c_207, c_10])).
% 15.80/5.71  tff(c_610, plain, (![A_152, B_150, C_148, D_149, E_151]: (k2_xboole_0(k2_tarski(A_152, B_150), k1_enumset1(C_148, D_149, E_151))=k3_enumset1(A_152, B_150, C_148, D_149, E_151))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.80/5.71  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.80/5.71  tff(c_619, plain, (![A_152, B_150, C_148, D_149, E_151]: (k2_xboole_0(k1_enumset1(C_148, D_149, E_151), k2_tarski(A_152, B_150))=k3_enumset1(A_152, B_150, C_148, D_149, E_151))), inference(superposition, [status(thm), theory('equality')], [c_610, c_2])).
% 15.80/5.71  tff(c_36, plain, (![E_88, C_86, B_85, D_87, A_84]: (k4_enumset1(A_84, A_84, B_85, C_86, D_87, E_88)=k3_enumset1(A_84, B_85, C_86, D_87, E_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.80/5.71  tff(c_32, plain, (![A_77, B_78, C_79]: (k2_enumset1(A_77, A_77, B_78, C_79)=k1_enumset1(A_77, B_78, C_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.80/5.71  tff(c_283, plain, (![A_77, C_79, B_78]: (k2_enumset1(A_77, A_77, C_79, B_78)=k1_enumset1(A_77, B_78, C_79))), inference(superposition, [status(thm), theory('equality')], [c_32, c_207])).
% 15.80/5.71  tff(c_38, plain, (![D_92, C_91, F_94, A_89, B_90, E_93]: (k5_enumset1(A_89, A_89, B_90, C_91, D_92, E_93, F_94)=k4_enumset1(A_89, B_90, C_91, D_92, E_93, F_94))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.80/5.71  tff(c_34, plain, (![A_80, B_81, C_82, D_83]: (k3_enumset1(A_80, A_80, B_81, C_82, D_83)=k2_enumset1(A_80, B_81, C_82, D_83))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.80/5.71  tff(c_979, plain, (![A_185, E_184, D_183, C_180, B_182, G_181, F_186]: (k2_xboole_0(k3_enumset1(A_185, B_182, C_180, D_183, E_184), k2_tarski(F_186, G_181))=k5_enumset1(A_185, B_182, C_180, D_183, E_184, F_186, G_181))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.80/5.71  tff(c_994, plain, (![B_81, D_83, A_80, G_181, F_186, C_82]: (k5_enumset1(A_80, A_80, B_81, C_82, D_83, F_186, G_181)=k2_xboole_0(k2_enumset1(A_80, B_81, C_82, D_83), k2_tarski(F_186, G_181)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_979])).
% 15.80/5.71  tff(c_3230, plain, (![G_285, F_282, A_283, D_287, C_286, B_284]: (k2_xboole_0(k2_enumset1(A_283, B_284, C_286, D_287), k2_tarski(F_282, G_285))=k4_enumset1(A_283, B_284, C_286, D_287, F_282, G_285))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_994])).
% 15.80/5.71  tff(c_3299, plain, (![G_285, F_282, B_78, A_77, C_79]: (k4_enumset1(A_77, A_77, C_79, B_78, F_282, G_285)=k2_xboole_0(k1_enumset1(A_77, B_78, C_79), k2_tarski(F_282, G_285)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_3230])).
% 15.80/5.71  tff(c_6581, plain, (![B_385, C_387, A_384, G_383, F_386]: (k3_enumset1(F_386, G_383, A_384, B_385, C_387)=k3_enumset1(A_384, C_387, B_385, F_386, G_383))), inference(demodulation, [status(thm), theory('equality')], [c_619, c_36, c_3299])).
% 15.80/5.71  tff(c_6737, plain, (![A_384, C_387, B_385, G_383]: (k3_enumset1(A_384, C_387, B_385, G_383, G_383)=k2_enumset1(G_383, A_384, B_385, C_387))), inference(superposition, [status(thm), theory('equality')], [c_6581, c_34])).
% 15.80/5.71  tff(c_766, plain, (![C_170, D_171, A_175, B_173, G_174, F_169, E_172]: (k2_xboole_0(k4_enumset1(A_175, B_173, C_170, D_171, E_172, F_169), k1_tarski(G_174))=k5_enumset1(A_175, B_173, C_170, D_171, E_172, F_169, G_174))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.80/5.71  tff(c_781, plain, (![E_88, C_86, B_85, D_87, A_84, G_174]: (k5_enumset1(A_84, A_84, B_85, C_86, D_87, E_88, G_174)=k2_xboole_0(k3_enumset1(A_84, B_85, C_86, D_87, E_88), k1_tarski(G_174)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_766])).
% 15.80/5.71  tff(c_790, plain, (![E_88, C_86, B_85, D_87, A_84, G_174]: (k2_xboole_0(k3_enumset1(A_84, B_85, C_86, D_87, E_88), k1_tarski(G_174))=k4_enumset1(A_84, B_85, C_86, D_87, E_88, G_174))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_781])).
% 15.80/5.71  tff(c_28, plain, (![A_74]: (k2_tarski(A_74, A_74)=k1_tarski(A_74))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.80/5.71  tff(c_1003, plain, (![A_74, A_185, E_184, D_183, C_180, B_182]: (k5_enumset1(A_185, B_182, C_180, D_183, E_184, A_74, A_74)=k2_xboole_0(k3_enumset1(A_185, B_182, C_180, D_183, E_184), k1_tarski(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_979])).
% 15.80/5.71  tff(c_3601, plain, (![C_296, B_293, A_291, A_294, D_292, E_295]: (k5_enumset1(A_291, B_293, C_296, D_292, E_295, A_294, A_294)=k4_enumset1(A_291, B_293, C_296, D_292, E_295, A_294))), inference(demodulation, [status(thm), theory('equality')], [c_790, c_1003])).
% 15.80/5.71  tff(c_3614, plain, (![C_296, B_293, A_294, D_292, E_295]: (k4_enumset1(B_293, C_296, D_292, E_295, A_294, A_294)=k4_enumset1(B_293, B_293, C_296, D_292, E_295, A_294))), inference(superposition, [status(thm), theory('equality')], [c_3601, c_38])).
% 15.80/5.71  tff(c_19872, plain, (![B_587, A_586, E_589, C_585, D_588]: (k4_enumset1(B_587, C_585, D_588, E_589, A_586, A_586)=k3_enumset1(B_587, C_585, D_588, E_589, A_586))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3614])).
% 15.80/5.71  tff(c_19900, plain, (![C_585, D_588, E_589, A_586]: (k3_enumset1(C_585, D_588, E_589, A_586, A_586)=k3_enumset1(C_585, C_585, D_588, E_589, A_586))), inference(superposition, [status(thm), theory('equality')], [c_19872, c_36])).
% 15.80/5.71  tff(c_19915, plain, (![C_585, D_588, E_589, A_586]: (k2_enumset1(C_585, D_588, E_589, A_586)=k2_enumset1(A_586, C_585, E_589, D_588))), inference(demodulation, [status(thm), theory('equality')], [c_6737, c_34, c_19900])).
% 15.80/5.71  tff(c_42, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.80/5.71  tff(c_43, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_42])).
% 15.80/5.71  tff(c_44, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_43])).
% 15.80/5.71  tff(c_19918, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19915, c_19915, c_19915, c_44])).
% 15.80/5.71  tff(c_19921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_239, c_10, c_19918])).
% 15.80/5.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.80/5.71  
% 15.80/5.71  Inference rules
% 15.80/5.71  ----------------------
% 15.80/5.71  #Ref     : 0
% 15.80/5.71  #Sup     : 4591
% 15.80/5.71  #Fact    : 0
% 15.80/5.71  #Define  : 0
% 15.80/5.71  #Split   : 0
% 15.80/5.71  #Chain   : 0
% 15.80/5.71  #Close   : 0
% 15.80/5.71  
% 15.80/5.71  Ordering : KBO
% 15.80/5.71  
% 15.80/5.71  Simplification rules
% 15.80/5.71  ----------------------
% 15.80/5.71  #Subsume      : 701
% 15.80/5.71  #Demod        : 5427
% 15.80/5.71  #Tautology    : 3073
% 15.80/5.71  #SimpNegUnit  : 0
% 15.80/5.71  #BackRed      : 27
% 15.80/5.71  
% 15.80/5.71  #Partial instantiations: 0
% 15.80/5.71  #Strategies tried      : 1
% 15.80/5.71  
% 15.80/5.71  Timing (in seconds)
% 15.80/5.71  ----------------------
% 15.80/5.72  Preprocessing        : 0.53
% 15.80/5.72  Parsing              : 0.27
% 15.80/5.72  CNF conversion       : 0.04
% 15.80/5.72  Main loop            : 4.26
% 15.80/5.72  Inferencing          : 1.23
% 15.80/5.72  Reduction            : 2.22
% 15.80/5.72  Demodulation         : 1.94
% 15.80/5.72  BG Simplification    : 0.15
% 15.80/5.72  Subsumption          : 0.48
% 15.80/5.72  Abstraction          : 0.22
% 15.80/5.72  MUC search           : 0.00
% 15.80/5.72  Cooper               : 0.00
% 15.80/5.72  Total                : 4.84
% 15.80/5.72  Index Insertion      : 0.00
% 15.80/5.72  Index Deletion       : 0.00
% 15.80/5.72  Index Matching       : 0.00
% 15.80/5.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

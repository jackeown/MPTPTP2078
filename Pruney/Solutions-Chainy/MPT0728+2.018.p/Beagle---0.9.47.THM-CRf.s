%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:57 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  52 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 (  46 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_82,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_85,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k4_enumset1(A_17,A_17,B_18,C_19,D_20,E_21) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k5_enumset1(A_22,A_22,B_23,C_24,D_25,E_26,F_27) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_313,plain,(
    ! [C_171,A_170,D_173,B_172,G_167,E_169,F_168] : k6_enumset1(A_170,A_170,B_172,C_171,D_173,E_169,F_168,G_167) = k5_enumset1(A_170,B_172,C_171,D_173,E_169,F_168,G_167) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    ! [J_48,C_39,B_38,D_40,F_42,G_43,E_41,H_44] : r2_hidden(J_48,k6_enumset1(J_48,B_38,C_39,D_40,E_41,F_42,G_43,H_44)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_346,plain,(
    ! [B_180,A_174,E_178,G_177,D_175,F_176,C_179] : r2_hidden(A_174,k5_enumset1(A_174,B_180,C_179,D_175,E_178,F_176,G_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_52])).

tff(c_350,plain,(
    ! [C_182,A_181,F_184,B_186,D_185,E_183] : r2_hidden(A_181,k4_enumset1(A_181,B_186,C_182,D_185,E_183,F_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_346])).

tff(c_354,plain,(
    ! [C_187,E_191,B_189,A_188,D_190] : r2_hidden(A_188,k3_enumset1(A_188,B_189,C_187,D_190,E_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_350])).

tff(c_429,plain,(
    ! [A_195,B_196,C_197,D_198] : r2_hidden(A_195,k2_enumset1(A_195,B_196,C_197,D_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_354])).

tff(c_433,plain,(
    ! [A_199,B_200,C_201] : r2_hidden(A_199,k1_enumset1(A_199,B_200,C_201)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_429])).

tff(c_437,plain,(
    ! [A_202,B_203] : r2_hidden(A_202,k2_tarski(A_202,B_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_433])).

tff(c_512,plain,(
    ! [A_207] : r2_hidden(A_207,k1_tarski(A_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_437])).

tff(c_90,plain,(
    ! [A_49] : k2_xboole_0(A_49,k1_tarski(A_49)) = k1_ordinal1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_161,plain,(
    ! [D_62,B_63,A_64] :
      ( ~ r2_hidden(D_62,B_63)
      | r2_hidden(D_62,k2_xboole_0(A_64,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_167,plain,(
    ! [D_62,A_49] :
      ( ~ r2_hidden(D_62,k1_tarski(A_49))
      | r2_hidden(D_62,k1_ordinal1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_161])).

tff(c_516,plain,(
    ! [A_207] : r2_hidden(A_207,k1_ordinal1(A_207)) ),
    inference(resolution,[status(thm)],[c_512,c_167])).

tff(c_92,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:40:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.46  
% 2.89/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.46  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.89/1.46  
% 2.89/1.46  %Foreground sorts:
% 2.89/1.46  
% 2.89/1.46  
% 2.89/1.46  %Background operators:
% 2.89/1.46  
% 2.89/1.46  
% 2.89/1.46  %Foreground operators:
% 2.89/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.89/1.46  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.89/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.89/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.89/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.46  
% 3.23/1.47  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.23/1.47  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.23/1.47  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.23/1.47  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.23/1.47  tff(f_44, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.23/1.47  tff(f_46, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.23/1.47  tff(f_48, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.23/1.47  tff(f_80, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.23/1.47  tff(f_82, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.23/1.47  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.23/1.47  tff(f_85, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 3.23/1.47  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.47  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.47  tff(c_24, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.47  tff(c_26, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.23/1.47  tff(c_28, plain, (![E_21, D_20, C_19, B_18, A_17]: (k4_enumset1(A_17, A_17, B_18, C_19, D_20, E_21)=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.47  tff(c_30, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k5_enumset1(A_22, A_22, B_23, C_24, D_25, E_26, F_27)=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.23/1.47  tff(c_313, plain, (![C_171, A_170, D_173, B_172, G_167, E_169, F_168]: (k6_enumset1(A_170, A_170, B_172, C_171, D_173, E_169, F_168, G_167)=k5_enumset1(A_170, B_172, C_171, D_173, E_169, F_168, G_167))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.47  tff(c_52, plain, (![J_48, C_39, B_38, D_40, F_42, G_43, E_41, H_44]: (r2_hidden(J_48, k6_enumset1(J_48, B_38, C_39, D_40, E_41, F_42, G_43, H_44)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.23/1.47  tff(c_346, plain, (![B_180, A_174, E_178, G_177, D_175, F_176, C_179]: (r2_hidden(A_174, k5_enumset1(A_174, B_180, C_179, D_175, E_178, F_176, G_177)))), inference(superposition, [status(thm), theory('equality')], [c_313, c_52])).
% 3.23/1.47  tff(c_350, plain, (![C_182, A_181, F_184, B_186, D_185, E_183]: (r2_hidden(A_181, k4_enumset1(A_181, B_186, C_182, D_185, E_183, F_184)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_346])).
% 3.23/1.47  tff(c_354, plain, (![C_187, E_191, B_189, A_188, D_190]: (r2_hidden(A_188, k3_enumset1(A_188, B_189, C_187, D_190, E_191)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_350])).
% 3.23/1.47  tff(c_429, plain, (![A_195, B_196, C_197, D_198]: (r2_hidden(A_195, k2_enumset1(A_195, B_196, C_197, D_198)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_354])).
% 3.23/1.47  tff(c_433, plain, (![A_199, B_200, C_201]: (r2_hidden(A_199, k1_enumset1(A_199, B_200, C_201)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_429])).
% 3.23/1.47  tff(c_437, plain, (![A_202, B_203]: (r2_hidden(A_202, k2_tarski(A_202, B_203)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_433])).
% 3.23/1.47  tff(c_512, plain, (![A_207]: (r2_hidden(A_207, k1_tarski(A_207)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_437])).
% 3.23/1.47  tff(c_90, plain, (![A_49]: (k2_xboole_0(A_49, k1_tarski(A_49))=k1_ordinal1(A_49))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.23/1.47  tff(c_161, plain, (![D_62, B_63, A_64]: (~r2_hidden(D_62, B_63) | r2_hidden(D_62, k2_xboole_0(A_64, B_63)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.23/1.47  tff(c_167, plain, (![D_62, A_49]: (~r2_hidden(D_62, k1_tarski(A_49)) | r2_hidden(D_62, k1_ordinal1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_161])).
% 3.23/1.47  tff(c_516, plain, (![A_207]: (r2_hidden(A_207, k1_ordinal1(A_207)))), inference(resolution, [status(thm)], [c_512, c_167])).
% 3.23/1.47  tff(c_92, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.23/1.47  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_516, c_92])).
% 3.23/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.47  
% 3.23/1.47  Inference rules
% 3.23/1.47  ----------------------
% 3.23/1.47  #Ref     : 0
% 3.23/1.47  #Sup     : 90
% 3.23/1.47  #Fact    : 4
% 3.23/1.47  #Define  : 0
% 3.23/1.47  #Split   : 0
% 3.23/1.47  #Chain   : 0
% 3.23/1.47  #Close   : 0
% 3.23/1.47  
% 3.23/1.47  Ordering : KBO
% 3.23/1.47  
% 3.23/1.47  Simplification rules
% 3.23/1.47  ----------------------
% 3.23/1.47  #Subsume      : 3
% 3.23/1.47  #Demod        : 1
% 3.23/1.47  #Tautology    : 28
% 3.23/1.47  #SimpNegUnit  : 0
% 3.23/1.47  #BackRed      : 1
% 3.23/1.47  
% 3.23/1.47  #Partial instantiations: 0
% 3.23/1.47  #Strategies tried      : 1
% 3.23/1.47  
% 3.23/1.47  Timing (in seconds)
% 3.23/1.47  ----------------------
% 3.25/1.47  Preprocessing        : 0.36
% 3.25/1.47  Parsing              : 0.17
% 3.25/1.47  CNF conversion       : 0.03
% 3.25/1.48  Main loop            : 0.32
% 3.25/1.48  Inferencing          : 0.10
% 3.25/1.48  Reduction            : 0.09
% 3.25/1.48  Demodulation         : 0.07
% 3.25/1.48  BG Simplification    : 0.02
% 3.25/1.48  Subsumption          : 0.10
% 3.25/1.48  Abstraction          : 0.03
% 3.25/1.48  MUC search           : 0.00
% 3.25/1.48  Cooper               : 0.00
% 3.25/1.48  Total                : 0.71
% 3.25/1.48  Index Insertion      : 0.00
% 3.25/1.48  Index Deletion       : 0.00
% 3.25/1.48  Index Matching       : 0.00
% 3.25/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

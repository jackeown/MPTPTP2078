%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:01 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   65 (  78 expanded)
%              Number of leaves         :   32 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :   59 (  81 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_75,axiom,(
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

tff(f_86,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_77,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_311,plain,(
    ! [B_256,F_253,E_252,A_250,D_255,G_254,C_251] : k6_enumset1(A_250,A_250,B_256,C_251,D_255,E_252,F_253,G_254) = k5_enumset1(A_250,B_256,C_251,D_255,E_252,F_253,G_254) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [D_36,G_39,J_44,F_38,E_37,A_33,B_34,C_35] : r2_hidden(J_44,k6_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39,J_44)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_960,plain,(
    ! [E_616,C_615,D_618,G_617,F_613,B_614,A_619] : r2_hidden(G_617,k5_enumset1(A_619,B_614,C_615,D_618,E_616,F_613,G_617)) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_22])).

tff(c_968,plain,(
    ! [E_622,C_625,A_623,D_624,B_621,F_620] : r2_hidden(F_620,k4_enumset1(A_623,B_621,C_625,D_624,E_622,F_620)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_960])).

tff(c_976,plain,(
    ! [B_628,C_626,A_627,E_630,D_629] : r2_hidden(E_630,k3_enumset1(A_627,B_628,C_626,D_629,E_630)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_968])).

tff(c_984,plain,(
    ! [D_631,A_632,B_633,C_634] : r2_hidden(D_631,k2_enumset1(A_632,B_633,C_634,D_631)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_976])).

tff(c_993,plain,(
    ! [C_644,A_645,B_646] : r2_hidden(C_644,k1_enumset1(A_645,B_646,C_644)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_984])).

tff(c_999,plain,(
    ! [B_3,A_2] : r2_hidden(B_3,k2_tarski(A_2,B_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_993])).

tff(c_78,plain,(
    k1_ordinal1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_74,plain,(
    ! [A_45] : k2_xboole_0(A_45,k1_tarski(A_45)) = k1_ordinal1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,k3_tarski(B_30))
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [D_36,G_39,J_44,F_38,A_33,B_34,H_40,C_35] : r2_hidden(J_44,k6_enumset1(A_33,B_34,C_35,D_36,J_44,F_38,G_39,H_40)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_388,plain,(
    ! [A_263,C_259,F_257,G_261,E_260,B_258,D_262] : r2_hidden(D_262,k5_enumset1(A_263,B_258,C_259,D_262,E_260,F_257,G_261)) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_28])).

tff(c_396,plain,(
    ! [D_268,E_266,F_264,A_267,C_269,B_265] : r2_hidden(C_269,k4_enumset1(A_267,B_265,C_269,D_268,E_266,F_264)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_388])).

tff(c_404,plain,(
    ! [E_274,A_271,D_273,C_270,B_272] : r2_hidden(B_272,k3_enumset1(A_271,B_272,C_270,D_273,E_274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_396])).

tff(c_456,plain,(
    ! [A_284,B_285,C_286,D_287] : r2_hidden(A_284,k2_enumset1(A_284,B_285,C_286,D_287)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_404])).

tff(c_464,plain,(
    ! [A_288,B_289,C_290] : r2_hidden(A_288,k1_enumset1(A_288,B_289,C_290)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_456])).

tff(c_472,plain,(
    ! [A_291,B_292] : r2_hidden(A_291,k2_tarski(A_291,B_292)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_464])).

tff(c_484,plain,(
    ! [A_293] : r2_hidden(A_293,k1_tarski(A_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_472])).

tff(c_76,plain,(
    ! [B_47,A_46] :
      ( ~ r1_tarski(B_47,A_46)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_492,plain,(
    ! [A_294] : ~ r1_tarski(k1_tarski(A_294),A_294) ),
    inference(resolution,[status(thm)],[c_484,c_76])).

tff(c_526,plain,(
    ! [B_319] : ~ r2_hidden(k1_tarski(k3_tarski(B_319)),B_319) ),
    inference(resolution,[status(thm)],[c_16,c_492])).

tff(c_607,plain,(
    ! [A_362,B_363] : ~ r2_hidden(k1_tarski(k2_xboole_0(A_362,B_363)),k2_tarski(A_362,B_363)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_526])).

tff(c_619,plain,(
    ! [A_373] : ~ r2_hidden(k1_tarski(k1_ordinal1(A_373)),k2_tarski(A_373,k1_tarski(A_373))) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_607])).

tff(c_622,plain,(
    ~ r2_hidden(k1_tarski('#skF_3'),k2_tarski('#skF_3',k1_tarski('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_619])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.67  
% 3.79/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.67  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 3.79/1.67  
% 3.79/1.67  %Foreground sorts:
% 3.79/1.67  
% 3.79/1.67  
% 3.79/1.67  %Background operators:
% 3.79/1.67  
% 3.79/1.67  
% 3.79/1.67  %Foreground operators:
% 3.79/1.67  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.79/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.79/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.79/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.79/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.79/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.79/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.79/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.79/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.79/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.79/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.67  
% 3.79/1.69  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.79/1.69  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.79/1.69  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.79/1.69  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.79/1.69  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.79/1.69  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.79/1.69  tff(f_75, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.79/1.69  tff(f_86, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 3.79/1.69  tff(f_77, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.79/1.69  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 3.79/1.69  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.79/1.69  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.79/1.69  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.79/1.69  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.79/1.69  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.69  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.79/1.69  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.79/1.69  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.79/1.69  tff(c_311, plain, (![B_256, F_253, E_252, A_250, D_255, G_254, C_251]: (k6_enumset1(A_250, A_250, B_256, C_251, D_255, E_252, F_253, G_254)=k5_enumset1(A_250, B_256, C_251, D_255, E_252, F_253, G_254))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.79/1.69  tff(c_22, plain, (![D_36, G_39, J_44, F_38, E_37, A_33, B_34, C_35]: (r2_hidden(J_44, k6_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39, J_44)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.79/1.69  tff(c_960, plain, (![E_616, C_615, D_618, G_617, F_613, B_614, A_619]: (r2_hidden(G_617, k5_enumset1(A_619, B_614, C_615, D_618, E_616, F_613, G_617)))), inference(superposition, [status(thm), theory('equality')], [c_311, c_22])).
% 3.79/1.69  tff(c_968, plain, (![E_622, C_625, A_623, D_624, B_621, F_620]: (r2_hidden(F_620, k4_enumset1(A_623, B_621, C_625, D_624, E_622, F_620)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_960])).
% 3.79/1.69  tff(c_976, plain, (![B_628, C_626, A_627, E_630, D_629]: (r2_hidden(E_630, k3_enumset1(A_627, B_628, C_626, D_629, E_630)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_968])).
% 3.79/1.69  tff(c_984, plain, (![D_631, A_632, B_633, C_634]: (r2_hidden(D_631, k2_enumset1(A_632, B_633, C_634, D_631)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_976])).
% 3.79/1.69  tff(c_993, plain, (![C_644, A_645, B_646]: (r2_hidden(C_644, k1_enumset1(A_645, B_646, C_644)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_984])).
% 3.79/1.69  tff(c_999, plain, (![B_3, A_2]: (r2_hidden(B_3, k2_tarski(A_2, B_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_993])).
% 3.79/1.69  tff(c_78, plain, (k1_ordinal1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.79/1.69  tff(c_74, plain, (![A_45]: (k2_xboole_0(A_45, k1_tarski(A_45))=k1_ordinal1(A_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.79/1.69  tff(c_18, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.79/1.69  tff(c_16, plain, (![A_29, B_30]: (r1_tarski(A_29, k3_tarski(B_30)) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.69  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.79/1.69  tff(c_28, plain, (![D_36, G_39, J_44, F_38, A_33, B_34, H_40, C_35]: (r2_hidden(J_44, k6_enumset1(A_33, B_34, C_35, D_36, J_44, F_38, G_39, H_40)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.79/1.69  tff(c_388, plain, (![A_263, C_259, F_257, G_261, E_260, B_258, D_262]: (r2_hidden(D_262, k5_enumset1(A_263, B_258, C_259, D_262, E_260, F_257, G_261)))), inference(superposition, [status(thm), theory('equality')], [c_311, c_28])).
% 3.79/1.69  tff(c_396, plain, (![D_268, E_266, F_264, A_267, C_269, B_265]: (r2_hidden(C_269, k4_enumset1(A_267, B_265, C_269, D_268, E_266, F_264)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_388])).
% 3.79/1.69  tff(c_404, plain, (![E_274, A_271, D_273, C_270, B_272]: (r2_hidden(B_272, k3_enumset1(A_271, B_272, C_270, D_273, E_274)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_396])).
% 3.79/1.69  tff(c_456, plain, (![A_284, B_285, C_286, D_287]: (r2_hidden(A_284, k2_enumset1(A_284, B_285, C_286, D_287)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_404])).
% 3.79/1.69  tff(c_464, plain, (![A_288, B_289, C_290]: (r2_hidden(A_288, k1_enumset1(A_288, B_289, C_290)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_456])).
% 3.79/1.69  tff(c_472, plain, (![A_291, B_292]: (r2_hidden(A_291, k2_tarski(A_291, B_292)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_464])).
% 3.79/1.69  tff(c_484, plain, (![A_293]: (r2_hidden(A_293, k1_tarski(A_293)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_472])).
% 3.79/1.69  tff(c_76, plain, (![B_47, A_46]: (~r1_tarski(B_47, A_46) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.79/1.69  tff(c_492, plain, (![A_294]: (~r1_tarski(k1_tarski(A_294), A_294))), inference(resolution, [status(thm)], [c_484, c_76])).
% 3.79/1.69  tff(c_526, plain, (![B_319]: (~r2_hidden(k1_tarski(k3_tarski(B_319)), B_319))), inference(resolution, [status(thm)], [c_16, c_492])).
% 3.79/1.69  tff(c_607, plain, (![A_362, B_363]: (~r2_hidden(k1_tarski(k2_xboole_0(A_362, B_363)), k2_tarski(A_362, B_363)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_526])).
% 3.79/1.69  tff(c_619, plain, (![A_373]: (~r2_hidden(k1_tarski(k1_ordinal1(A_373)), k2_tarski(A_373, k1_tarski(A_373))))), inference(superposition, [status(thm), theory('equality')], [c_74, c_607])).
% 3.79/1.69  tff(c_622, plain, (~r2_hidden(k1_tarski('#skF_3'), k2_tarski('#skF_3', k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_619])).
% 3.79/1.69  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_999, c_622])).
% 3.79/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.69  
% 3.79/1.69  Inference rules
% 3.79/1.69  ----------------------
% 3.79/1.69  #Ref     : 0
% 3.79/1.69  #Sup     : 220
% 3.79/1.69  #Fact    : 0
% 3.79/1.69  #Define  : 0
% 3.79/1.69  #Split   : 0
% 3.79/1.69  #Chain   : 0
% 3.79/1.69  #Close   : 0
% 3.79/1.69  
% 3.79/1.69  Ordering : KBO
% 3.79/1.69  
% 3.79/1.69  Simplification rules
% 3.79/1.69  ----------------------
% 3.79/1.69  #Subsume      : 39
% 3.79/1.69  #Demod        : 8
% 3.79/1.69  #Tautology    : 37
% 3.79/1.69  #SimpNegUnit  : 0
% 3.79/1.69  #BackRed      : 1
% 3.79/1.69  
% 3.79/1.69  #Partial instantiations: 0
% 3.79/1.69  #Strategies tried      : 1
% 3.79/1.69  
% 3.79/1.69  Timing (in seconds)
% 3.79/1.69  ----------------------
% 3.79/1.69  Preprocessing        : 0.36
% 3.79/1.69  Parsing              : 0.18
% 3.79/1.69  CNF conversion       : 0.03
% 3.79/1.69  Main loop            : 0.50
% 3.79/1.69  Inferencing          : 0.19
% 3.79/1.69  Reduction            : 0.12
% 3.79/1.69  Demodulation         : 0.09
% 3.79/1.69  BG Simplification    : 0.03
% 3.79/1.69  Subsumption          : 0.13
% 3.79/1.69  Abstraction          : 0.03
% 3.79/1.69  MUC search           : 0.00
% 3.79/1.69  Cooper               : 0.00
% 3.79/1.69  Total                : 0.89
% 3.79/1.69  Index Insertion      : 0.00
% 3.79/1.69  Index Deletion       : 0.00
% 3.79/1.69  Index Matching       : 0.00
% 3.79/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------

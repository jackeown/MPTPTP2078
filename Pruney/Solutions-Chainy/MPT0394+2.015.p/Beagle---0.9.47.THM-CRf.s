%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:22 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 136 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   94 ( 173 expanded)
%              Number of equality atoms :   58 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_104,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_81,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_102,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k4_xboole_0(A_20,B_21) != A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_153,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_70)
      | r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_134,plain,(
    ! [A_15,C_64] :
      ( ~ r1_xboole_0(A_15,k1_xboole_0)
      | ~ r2_hidden(C_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_131])).

tff(c_141,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_164,plain,(
    ! [A_71] : r1_xboole_0(A_71,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_153,c_141])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_168,plain,(
    ! [A_71] : k4_xboole_0(A_71,k1_xboole_0) = A_71 ),
    inference(resolution,[status(thm)],[c_164,c_26])).

tff(c_226,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_245,plain,(
    ! [A_71] : k4_xboole_0(A_71,A_71) = k3_xboole_0(A_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_226])).

tff(c_255,plain,(
    ! [A_71] : k4_xboole_0(A_71,A_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_245])).

tff(c_120,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(A_57,B_58)
      | k4_xboole_0(A_57,B_58) != A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    ! [B_40] : ~ r1_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_124,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(resolution,[status(thm)],[c_120,c_42])).

tff(c_315,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_124])).

tff(c_46,plain,(
    ! [A_43] : k1_setfam_1(k1_tarski(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_754,plain,(
    ! [A_115,B_116,C_117,D_118] : k2_xboole_0(k1_enumset1(A_115,B_116,C_117),k1_tarski(D_118)) = k2_enumset1(A_115,B_116,C_117,D_118) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_763,plain,(
    ! [A_32,B_33,D_118] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(D_118)) = k2_enumset1(A_32,A_32,B_33,D_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_754])).

tff(c_1241,plain,(
    ! [A_148,B_149,D_150] : k2_xboole_0(k2_tarski(A_148,B_149),k1_tarski(D_150)) = k1_enumset1(A_148,B_149,D_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_763])).

tff(c_1250,plain,(
    ! [A_31,D_150] : k2_xboole_0(k1_tarski(A_31),k1_tarski(D_150)) = k1_enumset1(A_31,A_31,D_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1241])).

tff(c_1253,plain,(
    ! [A_31,D_150] : k2_xboole_0(k1_tarski(A_31),k1_tarski(D_150)) = k2_tarski(A_31,D_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1250])).

tff(c_947,plain,(
    ! [A_131,B_132] :
      ( k3_xboole_0(k1_setfam_1(A_131),k1_setfam_1(B_132)) = k1_setfam_1(k2_xboole_0(A_131,B_132))
      | k1_xboole_0 = B_132
      | k1_xboole_0 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1003,plain,(
    ! [A_43,B_132] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_43),B_132)) = k3_xboole_0(A_43,k1_setfam_1(B_132))
      | k1_xboole_0 = B_132
      | k1_tarski(A_43) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_947])).

tff(c_3444,plain,(
    ! [A_237,B_238] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_237),B_238)) = k3_xboole_0(A_237,k1_setfam_1(B_238))
      | k1_xboole_0 = B_238 ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_1003])).

tff(c_3465,plain,(
    ! [A_31,D_150] :
      ( k3_xboole_0(A_31,k1_setfam_1(k1_tarski(D_150))) = k1_setfam_1(k2_tarski(A_31,D_150))
      | k1_tarski(D_150) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_3444])).

tff(c_3474,plain,(
    ! [A_31,D_150] :
      ( k1_setfam_1(k2_tarski(A_31,D_150)) = k3_xboole_0(A_31,D_150)
      | k1_tarski(D_150) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3465])).

tff(c_3475,plain,(
    ! [A_31,D_150] : k1_setfam_1(k2_tarski(A_31,D_150)) = k3_xboole_0(A_31,D_150) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_3474])).

tff(c_48,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3475,c_48])).

tff(c_3484,plain,(
    ! [A_239] : ~ r1_xboole_0(A_239,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_3489,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) != A_20 ),
    inference(resolution,[status(thm)],[c_28,c_3484])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_77,plain,(
    ! [A_49,B_50] : r1_tarski(k3_xboole_0(A_49,B_50),A_49) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_77])).

tff(c_3510,plain,(
    ! [B_245,A_246] :
      ( B_245 = A_246
      | ~ r1_tarski(B_245,A_246)
      | ~ r1_tarski(A_246,B_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3523,plain,(
    ! [A_247] :
      ( k1_xboole_0 = A_247
      | ~ r1_tarski(A_247,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_80,c_3510])).

tff(c_3538,plain,(
    ! [B_14] : k3_xboole_0(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_3523])).

tff(c_3584,plain,(
    ! [A_250,B_251] : k4_xboole_0(A_250,k4_xboole_0(A_250,B_251)) = k3_xboole_0(A_250,B_251) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3541,plain,(
    ! [B_248] : k3_xboole_0(k1_xboole_0,B_248) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_3523])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3546,plain,(
    ! [B_248] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_248) ),
    inference(superposition,[status(thm),theory(equality)],[c_3541,c_22])).

tff(c_3594,plain,(
    ! [B_251] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_251) ),
    inference(superposition,[status(thm),theory(equality)],[c_3584,c_3546])).

tff(c_3616,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3538,c_3594])).

tff(c_3618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3489,c_3616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.80  
% 4.26/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.80  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.31/1.80  
% 4.31/1.80  %Foreground sorts:
% 4.31/1.80  
% 4.31/1.80  
% 4.31/1.80  %Background operators:
% 4.31/1.80  
% 4.31/1.80  
% 4.31/1.80  %Foreground operators:
% 4.31/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.31/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.31/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.31/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.31/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.31/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.31/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.31/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.31/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.31/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.31/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.31/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.31/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.31/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.31/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.31/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.31/1.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.31/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.31/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.31/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.31/1.80  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.31/1.80  
% 4.35/1.81  tff(f_75, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.35/1.81  tff(f_67, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.35/1.81  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.35/1.81  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.35/1.81  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.35/1.81  tff(f_92, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 4.35/1.82  tff(f_104, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.35/1.82  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.35/1.82  tff(f_81, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.35/1.82  tff(f_85, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.35/1.82  tff(f_77, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 4.35/1.82  tff(f_102, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 4.35/1.82  tff(f_107, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.35/1.82  tff(f_65, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.35/1.82  tff(f_63, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.35/1.82  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.35/1.82  tff(c_28, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k4_xboole_0(A_20, B_21)!=A_20)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.82  tff(c_20, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.35/1.82  tff(c_153, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), B_70) | r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.35/1.82  tff(c_131, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.35/1.82  tff(c_134, plain, (![A_15, C_64]: (~r1_xboole_0(A_15, k1_xboole_0) | ~r2_hidden(C_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_131])).
% 4.35/1.82  tff(c_141, plain, (![C_64]: (~r2_hidden(C_64, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_134])).
% 4.35/1.82  tff(c_164, plain, (![A_71]: (r1_xboole_0(A_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_153, c_141])).
% 4.35/1.82  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.82  tff(c_168, plain, (![A_71]: (k4_xboole_0(A_71, k1_xboole_0)=A_71)), inference(resolution, [status(thm)], [c_164, c_26])).
% 4.35/1.82  tff(c_226, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.35/1.82  tff(c_245, plain, (![A_71]: (k4_xboole_0(A_71, A_71)=k3_xboole_0(A_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_168, c_226])).
% 4.35/1.82  tff(c_255, plain, (![A_71]: (k4_xboole_0(A_71, A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_245])).
% 4.35/1.82  tff(c_120, plain, (![A_57, B_58]: (r1_xboole_0(A_57, B_58) | k4_xboole_0(A_57, B_58)!=A_57)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.82  tff(c_42, plain, (![B_40]: (~r1_xboole_0(k1_tarski(B_40), k1_tarski(B_40)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.35/1.82  tff(c_124, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(resolution, [status(thm)], [c_120, c_42])).
% 4.35/1.82  tff(c_315, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_255, c_124])).
% 4.35/1.82  tff(c_46, plain, (![A_43]: (k1_setfam_1(k1_tarski(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.35/1.82  tff(c_36, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.35/1.82  tff(c_34, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.35/1.82  tff(c_38, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.82  tff(c_754, plain, (![A_115, B_116, C_117, D_118]: (k2_xboole_0(k1_enumset1(A_115, B_116, C_117), k1_tarski(D_118))=k2_enumset1(A_115, B_116, C_117, D_118))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.35/1.82  tff(c_763, plain, (![A_32, B_33, D_118]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(D_118))=k2_enumset1(A_32, A_32, B_33, D_118))), inference(superposition, [status(thm), theory('equality')], [c_36, c_754])).
% 4.35/1.82  tff(c_1241, plain, (![A_148, B_149, D_150]: (k2_xboole_0(k2_tarski(A_148, B_149), k1_tarski(D_150))=k1_enumset1(A_148, B_149, D_150))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_763])).
% 4.35/1.82  tff(c_1250, plain, (![A_31, D_150]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(D_150))=k1_enumset1(A_31, A_31, D_150))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1241])).
% 4.35/1.82  tff(c_1253, plain, (![A_31, D_150]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(D_150))=k2_tarski(A_31, D_150))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1250])).
% 4.35/1.82  tff(c_947, plain, (![A_131, B_132]: (k3_xboole_0(k1_setfam_1(A_131), k1_setfam_1(B_132))=k1_setfam_1(k2_xboole_0(A_131, B_132)) | k1_xboole_0=B_132 | k1_xboole_0=A_131)), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.35/1.82  tff(c_1003, plain, (![A_43, B_132]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_43), B_132))=k3_xboole_0(A_43, k1_setfam_1(B_132)) | k1_xboole_0=B_132 | k1_tarski(A_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_947])).
% 4.35/1.82  tff(c_3444, plain, (![A_237, B_238]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_237), B_238))=k3_xboole_0(A_237, k1_setfam_1(B_238)) | k1_xboole_0=B_238)), inference(negUnitSimplification, [status(thm)], [c_315, c_1003])).
% 4.35/1.82  tff(c_3465, plain, (![A_31, D_150]: (k3_xboole_0(A_31, k1_setfam_1(k1_tarski(D_150)))=k1_setfam_1(k2_tarski(A_31, D_150)) | k1_tarski(D_150)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1253, c_3444])).
% 4.35/1.82  tff(c_3474, plain, (![A_31, D_150]: (k1_setfam_1(k2_tarski(A_31, D_150))=k3_xboole_0(A_31, D_150) | k1_tarski(D_150)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3465])).
% 4.35/1.82  tff(c_3475, plain, (![A_31, D_150]: (k1_setfam_1(k2_tarski(A_31, D_150))=k3_xboole_0(A_31, D_150))), inference(negUnitSimplification, [status(thm)], [c_315, c_3474])).
% 4.35/1.82  tff(c_48, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.35/1.82  tff(c_3482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3475, c_48])).
% 4.35/1.82  tff(c_3484, plain, (![A_239]: (~r1_xboole_0(A_239, k1_xboole_0))), inference(splitRight, [status(thm)], [c_134])).
% 4.35/1.82  tff(c_3489, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)!=A_20)), inference(resolution, [status(thm)], [c_28, c_3484])).
% 4.35/1.82  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k3_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.35/1.82  tff(c_77, plain, (![A_49, B_50]: (r1_tarski(k3_xboole_0(A_49, B_50), A_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.35/1.82  tff(c_80, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(superposition, [status(thm), theory('equality')], [c_20, c_77])).
% 4.35/1.82  tff(c_3510, plain, (![B_245, A_246]: (B_245=A_246 | ~r1_tarski(B_245, A_246) | ~r1_tarski(A_246, B_245))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.35/1.82  tff(c_3523, plain, (![A_247]: (k1_xboole_0=A_247 | ~r1_tarski(A_247, k1_xboole_0))), inference(resolution, [status(thm)], [c_80, c_3510])).
% 4.35/1.82  tff(c_3538, plain, (![B_14]: (k3_xboole_0(k1_xboole_0, B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_3523])).
% 4.35/1.82  tff(c_3584, plain, (![A_250, B_251]: (k4_xboole_0(A_250, k4_xboole_0(A_250, B_251))=k3_xboole_0(A_250, B_251))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.35/1.82  tff(c_3541, plain, (![B_248]: (k3_xboole_0(k1_xboole_0, B_248)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_3523])).
% 4.35/1.82  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.35/1.82  tff(c_3546, plain, (![B_248]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_248))), inference(superposition, [status(thm), theory('equality')], [c_3541, c_22])).
% 4.35/1.82  tff(c_3594, plain, (![B_251]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_251))), inference(superposition, [status(thm), theory('equality')], [c_3584, c_3546])).
% 4.35/1.82  tff(c_3616, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3538, c_3594])).
% 4.35/1.82  tff(c_3618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3489, c_3616])).
% 4.35/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.82  
% 4.35/1.82  Inference rules
% 4.35/1.82  ----------------------
% 4.35/1.82  #Ref     : 0
% 4.35/1.82  #Sup     : 899
% 4.35/1.82  #Fact    : 0
% 4.35/1.82  #Define  : 0
% 4.35/1.82  #Split   : 1
% 4.35/1.82  #Chain   : 0
% 4.35/1.82  #Close   : 0
% 4.35/1.82  
% 4.35/1.82  Ordering : KBO
% 4.35/1.82  
% 4.35/1.82  Simplification rules
% 4.35/1.82  ----------------------
% 4.35/1.82  #Subsume      : 311
% 4.35/1.82  #Demod        : 279
% 4.35/1.82  #Tautology    : 374
% 4.35/1.82  #SimpNegUnit  : 17
% 4.35/1.82  #BackRed      : 3
% 4.35/1.82  
% 4.35/1.82  #Partial instantiations: 0
% 4.35/1.82  #Strategies tried      : 1
% 4.35/1.82  
% 4.35/1.82  Timing (in seconds)
% 4.35/1.82  ----------------------
% 4.35/1.82  Preprocessing        : 0.34
% 4.35/1.82  Parsing              : 0.19
% 4.35/1.82  CNF conversion       : 0.02
% 4.35/1.82  Main loop            : 0.64
% 4.35/1.82  Inferencing          : 0.23
% 4.35/1.82  Reduction            : 0.22
% 4.35/1.82  Demodulation         : 0.16
% 4.35/1.82  BG Simplification    : 0.03
% 4.35/1.82  Subsumption          : 0.13
% 4.35/1.82  Abstraction          : 0.04
% 4.35/1.82  MUC search           : 0.00
% 4.35/1.82  Cooper               : 0.00
% 4.35/1.82  Total                : 1.02
% 4.35/1.82  Index Insertion      : 0.00
% 4.35/1.82  Index Deletion       : 0.00
% 4.35/1.82  Index Matching       : 0.00
% 4.35/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

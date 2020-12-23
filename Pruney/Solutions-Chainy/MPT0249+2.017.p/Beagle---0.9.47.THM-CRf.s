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
% DateTime   : Thu Dec  3 09:50:25 EST 2020

% Result     : Theorem 8.09s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 164 expanded)
%              Number of leaves         :   35 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 241 expanded)
%              Number of equality atoms :   55 ( 145 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k1_tarski(A_55),B_56)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_64,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_105,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_20])).

tff(c_250,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_260,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_250])).

tff(c_281,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_285,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_281])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(k1_tarski(A_50),B_51)
      | r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1760,plain,(
    ! [A_150,B_151,C_152] :
      ( k1_xboole_0 = A_150
      | ~ r1_xboole_0(B_151,C_152)
      | ~ r1_tarski(A_150,C_152)
      | ~ r1_tarski(A_150,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7842,plain,(
    ! [A_212,B_213,A_214] :
      ( k1_xboole_0 = A_212
      | ~ r1_tarski(A_212,B_213)
      | ~ r1_tarski(A_212,k1_tarski(A_214))
      | r2_hidden(A_214,B_213) ) ),
    inference(resolution,[status(thm)],[c_42,c_1760])).

tff(c_7861,plain,(
    ! [B_216,A_217] :
      ( k1_xboole_0 = B_216
      | ~ r1_tarski(B_216,k1_tarski(A_217))
      | r2_hidden(A_217,B_216) ) ),
    inference(resolution,[status(thm)],[c_14,c_7842])).

tff(c_7872,plain,
    ( k1_xboole_0 = '#skF_2'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_7861])).

tff(c_7882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_60,c_7872])).

tff(c_7883,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_7887,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7883,c_64])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_167,plain,(
    ! [A_75,B_76] :
      ( k2_xboole_0(A_75,B_76) = B_76
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_183,plain,(
    ! [B_8] : k2_xboole_0(B_8,B_8) = B_8 ),
    inference(resolution,[status(thm)],[c_14,c_167])).

tff(c_24,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8685,plain,(
    ! [A_262,B_263] : k5_xboole_0(k5_xboole_0(A_262,B_263),k2_xboole_0(A_262,B_263)) = k3_xboole_0(A_262,B_263) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8767,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_19,A_19)) = k3_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8685])).

tff(c_8777,plain,(
    ! [A_264] : k5_xboole_0(k1_xboole_0,A_264) = A_264 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_183,c_8767])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8808,plain,(
    ! [A_264] : k5_xboole_0(A_264,k1_xboole_0) = A_264 ),
    inference(superposition,[status(thm),theory(equality)],[c_8777,c_2])).

tff(c_8343,plain,(
    ! [A_252,B_253,C_254] : k5_xboole_0(k5_xboole_0(A_252,B_253),C_254) = k5_xboole_0(A_252,k5_xboole_0(B_253,C_254)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8359,plain,(
    ! [A_252,B_253] : k5_xboole_0(A_252,k5_xboole_0(B_253,k5_xboole_0(A_252,B_253))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8343,c_24])).

tff(c_8773,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_183,c_8767])).

tff(c_8382,plain,(
    ! [A_19,C_254] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_254)) = k5_xboole_0(k1_xboole_0,C_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8343])).

tff(c_8943,plain,(
    ! [A_266,C_267] : k5_xboole_0(A_266,k5_xboole_0(A_266,C_267)) = C_267 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8773,c_8382])).

tff(c_8999,plain,(
    ! [B_253,A_252] : k5_xboole_0(B_253,k5_xboole_0(A_252,B_253)) = k5_xboole_0(A_252,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8359,c_8943])).

tff(c_9033,plain,(
    ! [B_253,A_252] : k5_xboole_0(B_253,k5_xboole_0(A_252,B_253)) = A_252 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8808,c_8999])).

tff(c_8749,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7887,c_8685])).

tff(c_8771,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_8749])).

tff(c_9037,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9033,c_8771])).

tff(c_214,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = k1_xboole_0
      | ~ r1_xboole_0(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8159,plain,(
    ! [A_243,B_244] :
      ( k3_xboole_0(k1_tarski(A_243),B_244) = k1_xboole_0
      | r2_hidden(A_243,B_244) ) ),
    inference(resolution,[status(thm)],[c_42,c_214])).

tff(c_8172,plain,(
    ! [B_244] :
      ( k3_xboole_0('#skF_2',B_244) = k1_xboole_0
      | r2_hidden('#skF_1',B_244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7883,c_8159])).

tff(c_8186,plain,(
    ! [A_246,B_247] :
      ( k2_xboole_0(k1_tarski(A_246),B_247) = B_247
      | ~ r2_hidden(A_246,B_247) ) ),
    inference(resolution,[status(thm)],[c_50,c_167])).

tff(c_8236,plain,(
    ! [B_248] :
      ( k2_xboole_0('#skF_2',B_248) = B_248
      | ~ r2_hidden('#skF_1',B_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7883,c_8186])).

tff(c_8276,plain,(
    ! [B_244] :
      ( k2_xboole_0('#skF_2',B_244) = B_244
      | k3_xboole_0('#skF_2',B_244) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8172,c_8236])).

tff(c_9144,plain,
    ( k2_xboole_0('#skF_2','#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_9037,c_8276])).

tff(c_9150,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7887,c_9144])).

tff(c_9152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_62,c_9150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.09/2.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.77  
% 8.09/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.77  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.09/2.77  
% 8.09/2.77  %Foreground sorts:
% 8.09/2.77  
% 8.09/2.77  
% 8.09/2.77  %Background operators:
% 8.09/2.77  
% 8.09/2.77  
% 8.09/2.77  %Foreground operators:
% 8.09/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.09/2.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.09/2.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.09/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.09/2.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.09/2.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.09/2.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.09/2.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.09/2.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.09/2.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.09/2.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.09/2.77  tff('#skF_2', type, '#skF_2': $i).
% 8.09/2.77  tff('#skF_3', type, '#skF_3': $i).
% 8.09/2.77  tff('#skF_1', type, '#skF_1': $i).
% 8.09/2.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.09/2.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.09/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.09/2.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.09/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.09/2.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.09/2.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.09/2.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.09/2.77  
% 8.09/2.78  tff(f_105, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 8.09/2.78  tff(f_86, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 8.09/2.78  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.09/2.78  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.09/2.78  tff(f_78, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.09/2.78  tff(f_51, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 8.09/2.78  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.09/2.78  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.09/2.78  tff(f_57, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.09/2.78  tff(f_59, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.09/2.78  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.09/2.78  tff(f_55, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.09/2.78  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.09/2.78  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.09/2.78  tff(c_62, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.09/2.78  tff(c_50, plain, (![A_55, B_56]: (r1_tarski(k1_tarski(A_55), B_56) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.09/2.78  tff(c_64, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.09/2.78  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.09/2.78  tff(c_105, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_20])).
% 8.09/2.78  tff(c_250, plain, (![B_92, A_93]: (B_92=A_93 | ~r1_tarski(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.09/2.78  tff(c_260, plain, (k1_tarski('#skF_1')='#skF_2' | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_105, c_250])).
% 8.09/2.78  tff(c_281, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_260])).
% 8.09/2.78  tff(c_285, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_281])).
% 8.09/2.78  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.09/2.78  tff(c_14, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.09/2.78  tff(c_42, plain, (![A_50, B_51]: (r1_xboole_0(k1_tarski(A_50), B_51) | r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.09/2.78  tff(c_1760, plain, (![A_150, B_151, C_152]: (k1_xboole_0=A_150 | ~r1_xboole_0(B_151, C_152) | ~r1_tarski(A_150, C_152) | ~r1_tarski(A_150, B_151))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.09/2.78  tff(c_7842, plain, (![A_212, B_213, A_214]: (k1_xboole_0=A_212 | ~r1_tarski(A_212, B_213) | ~r1_tarski(A_212, k1_tarski(A_214)) | r2_hidden(A_214, B_213))), inference(resolution, [status(thm)], [c_42, c_1760])).
% 8.09/2.78  tff(c_7861, plain, (![B_216, A_217]: (k1_xboole_0=B_216 | ~r1_tarski(B_216, k1_tarski(A_217)) | r2_hidden(A_217, B_216))), inference(resolution, [status(thm)], [c_14, c_7842])).
% 8.09/2.78  tff(c_7872, plain, (k1_xboole_0='#skF_2' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_105, c_7861])).
% 8.09/2.78  tff(c_7882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_60, c_7872])).
% 8.09/2.78  tff(c_7883, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_260])).
% 8.09/2.78  tff(c_7887, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7883, c_64])).
% 8.09/2.78  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.09/2.78  tff(c_167, plain, (![A_75, B_76]: (k2_xboole_0(A_75, B_76)=B_76 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.09/2.78  tff(c_183, plain, (![B_8]: (k2_xboole_0(B_8, B_8)=B_8)), inference(resolution, [status(thm)], [c_14, c_167])).
% 8.09/2.78  tff(c_24, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.09/2.78  tff(c_8685, plain, (![A_262, B_263]: (k5_xboole_0(k5_xboole_0(A_262, B_263), k2_xboole_0(A_262, B_263))=k3_xboole_0(A_262, B_263))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.09/2.78  tff(c_8767, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_19, A_19))=k3_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_8685])).
% 8.09/2.78  tff(c_8777, plain, (![A_264]: (k5_xboole_0(k1_xboole_0, A_264)=A_264)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_183, c_8767])).
% 8.09/2.78  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.09/2.78  tff(c_8808, plain, (![A_264]: (k5_xboole_0(A_264, k1_xboole_0)=A_264)), inference(superposition, [status(thm), theory('equality')], [c_8777, c_2])).
% 8.09/2.78  tff(c_8343, plain, (![A_252, B_253, C_254]: (k5_xboole_0(k5_xboole_0(A_252, B_253), C_254)=k5_xboole_0(A_252, k5_xboole_0(B_253, C_254)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.09/2.78  tff(c_8359, plain, (![A_252, B_253]: (k5_xboole_0(A_252, k5_xboole_0(B_253, k5_xboole_0(A_252, B_253)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8343, c_24])).
% 8.09/2.78  tff(c_8773, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_183, c_8767])).
% 8.09/2.78  tff(c_8382, plain, (![A_19, C_254]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_254))=k5_xboole_0(k1_xboole_0, C_254))), inference(superposition, [status(thm), theory('equality')], [c_24, c_8343])).
% 8.09/2.78  tff(c_8943, plain, (![A_266, C_267]: (k5_xboole_0(A_266, k5_xboole_0(A_266, C_267))=C_267)), inference(demodulation, [status(thm), theory('equality')], [c_8773, c_8382])).
% 8.09/2.78  tff(c_8999, plain, (![B_253, A_252]: (k5_xboole_0(B_253, k5_xboole_0(A_252, B_253))=k5_xboole_0(A_252, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8359, c_8943])).
% 8.09/2.78  tff(c_9033, plain, (![B_253, A_252]: (k5_xboole_0(B_253, k5_xboole_0(A_252, B_253))=A_252)), inference(demodulation, [status(thm), theory('equality')], [c_8808, c_8999])).
% 8.09/2.78  tff(c_8749, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7887, c_8685])).
% 8.09/2.78  tff(c_8771, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_8749])).
% 8.09/2.78  tff(c_9037, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9033, c_8771])).
% 8.09/2.78  tff(c_214, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=k1_xboole_0 | ~r1_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/2.78  tff(c_8159, plain, (![A_243, B_244]: (k3_xboole_0(k1_tarski(A_243), B_244)=k1_xboole_0 | r2_hidden(A_243, B_244))), inference(resolution, [status(thm)], [c_42, c_214])).
% 8.09/2.78  tff(c_8172, plain, (![B_244]: (k3_xboole_0('#skF_2', B_244)=k1_xboole_0 | r2_hidden('#skF_1', B_244))), inference(superposition, [status(thm), theory('equality')], [c_7883, c_8159])).
% 8.09/2.78  tff(c_8186, plain, (![A_246, B_247]: (k2_xboole_0(k1_tarski(A_246), B_247)=B_247 | ~r2_hidden(A_246, B_247))), inference(resolution, [status(thm)], [c_50, c_167])).
% 8.09/2.78  tff(c_8236, plain, (![B_248]: (k2_xboole_0('#skF_2', B_248)=B_248 | ~r2_hidden('#skF_1', B_248))), inference(superposition, [status(thm), theory('equality')], [c_7883, c_8186])).
% 8.09/2.78  tff(c_8276, plain, (![B_244]: (k2_xboole_0('#skF_2', B_244)=B_244 | k3_xboole_0('#skF_2', B_244)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8172, c_8236])).
% 8.09/2.78  tff(c_9144, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_9037, c_8276])).
% 8.09/2.78  tff(c_9150, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7887, c_9144])).
% 8.09/2.78  tff(c_9152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_62, c_9150])).
% 8.09/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.78  
% 8.09/2.78  Inference rules
% 8.09/2.78  ----------------------
% 8.09/2.78  #Ref     : 0
% 8.09/2.78  #Sup     : 2317
% 8.09/2.78  #Fact    : 0
% 8.09/2.78  #Define  : 0
% 8.09/2.78  #Split   : 1
% 8.09/2.78  #Chain   : 0
% 8.09/2.78  #Close   : 0
% 8.09/2.78  
% 8.09/2.78  Ordering : KBO
% 8.09/2.78  
% 8.09/2.78  Simplification rules
% 8.09/2.78  ----------------------
% 8.09/2.78  #Subsume      : 87
% 8.09/2.78  #Demod        : 2414
% 8.09/2.78  #Tautology    : 1193
% 8.09/2.78  #SimpNegUnit  : 5
% 8.09/2.78  #BackRed      : 10
% 8.09/2.78  
% 8.09/2.78  #Partial instantiations: 0
% 8.09/2.78  #Strategies tried      : 1
% 8.09/2.78  
% 8.09/2.78  Timing (in seconds)
% 8.09/2.78  ----------------------
% 8.09/2.79  Preprocessing        : 0.35
% 8.09/2.79  Parsing              : 0.19
% 8.09/2.79  CNF conversion       : 0.02
% 8.09/2.79  Main loop            : 1.66
% 8.09/2.79  Inferencing          : 0.39
% 8.09/2.79  Reduction            : 0.91
% 8.09/2.79  Demodulation         : 0.79
% 8.09/2.79  BG Simplification    : 0.05
% 8.09/2.79  Subsumption          : 0.23
% 8.09/2.79  Abstraction          : 0.07
% 8.09/2.79  MUC search           : 0.00
% 8.09/2.79  Cooper               : 0.00
% 8.09/2.79  Total                : 2.04
% 8.09/2.79  Index Insertion      : 0.00
% 8.09/2.79  Index Deletion       : 0.00
% 8.09/2.79  Index Matching       : 0.00
% 8.09/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------

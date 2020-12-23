%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:59 EST 2020

% Result     : Theorem 5.49s
% Output     : CNFRefutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 259 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          :   82 ( 312 expanded)
%              Number of equality atoms :   58 ( 181 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_237,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_272,plain,(
    ! [A_93,B_94] :
      ( ~ r1_xboole_0(A_93,B_94)
      | k3_xboole_0(A_93,B_94) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_237])).

tff(c_282,plain,(
    ! [A_95,B_96] : k3_xboole_0(k4_xboole_0(A_95,B_96),B_96) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_272])).

tff(c_81,plain,(
    ! [B_68,A_69] : k3_xboole_0(B_68,A_69) = k3_xboole_0(A_69,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [B_68,A_69] : r1_tarski(k3_xboole_0(B_68,A_69),A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_14])).

tff(c_341,plain,(
    ! [B_99] : r1_tarski(k1_xboole_0,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_96])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_346,plain,(
    ! [B_100] : k3_xboole_0(k1_xboole_0,B_100) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_341,c_16])).

tff(c_407,plain,(
    ! [A_102] : k3_xboole_0(A_102,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_346])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_424,plain,(
    ! [A_102] : k5_xboole_0(A_102,k1_xboole_0) = k4_xboole_0(A_102,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_12])).

tff(c_586,plain,(
    ! [A_112] : k4_xboole_0(A_112,k1_xboole_0) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_424])).

tff(c_26,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_599,plain,(
    ! [A_112] : k5_xboole_0(k1_xboole_0,A_112) = k2_xboole_0(k1_xboole_0,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_26])).

tff(c_18,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_155,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1079,plain,(
    ! [A_151,B_152] : k3_xboole_0(k4_xboole_0(A_151,B_152),A_151) = k4_xboole_0(A_151,B_152) ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_281,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_272])).

tff(c_1102,plain,(
    ! [A_151] : k4_xboole_0(A_151,A_151) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_281])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_173,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_188,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_173])).

tff(c_1159,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_188])).

tff(c_487,plain,(
    ! [A_104,B_105,C_106] : k5_xboole_0(k5_xboole_0(A_104,B_105),C_106) = k5_xboole_0(A_104,k5_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2767,plain,(
    ! [A_191,B_192,C_193] : k5_xboole_0(A_191,k5_xboole_0(k3_xboole_0(A_191,B_192),C_193)) = k5_xboole_0(k4_xboole_0(A_191,B_192),C_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_487])).

tff(c_2809,plain,(
    ! [A_191,B_192] : k5_xboole_0(k4_xboole_0(A_191,B_192),k3_xboole_0(A_191,B_192)) = k5_xboole_0(A_191,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_2767])).

tff(c_6998,plain,(
    ! [A_242,B_243] : k5_xboole_0(k4_xboole_0(A_242,B_243),k3_xboole_0(A_242,B_243)) = A_242 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2809])).

tff(c_7115,plain,(
    ! [A_3] : k5_xboole_0(k4_xboole_0(A_3,A_3),A_3) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6998])).

tff(c_7143,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_1102,c_7115])).

tff(c_7276,plain,(
    ! [A_112] : k5_xboole_0(k1_xboole_0,A_112) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7143,c_599])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3076,plain,(
    ! [A_196,B_197,C_198] : k5_xboole_0(A_196,k5_xboole_0(k4_xboole_0(B_197,A_196),C_198)) = k5_xboole_0(k2_xboole_0(A_196,B_197),C_198) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_487])).

tff(c_3129,plain,(
    ! [A_196,B_197] : k5_xboole_0(k2_xboole_0(A_196,B_197),k4_xboole_0(B_197,A_196)) = k5_xboole_0(A_196,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_3076])).

tff(c_6166,plain,(
    ! [A_234,B_235] : k5_xboole_0(k2_xboole_0(A_234,B_235),k4_xboole_0(B_235,A_234)) = A_234 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3129])).

tff(c_6235,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3'))) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_6166])).

tff(c_24,plain,(
    ! [A_23,B_24,C_25] : k5_xboole_0(k5_xboole_0(A_23,B_24),C_25) = k5_xboole_0(A_23,k5_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7144,plain,(
    ! [C_244] : k5_xboole_0(k1_tarski('#skF_3'),k5_xboole_0(k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')),C_244)) = k5_xboole_0(k1_tarski('#skF_3'),C_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_6235,c_24])).

tff(c_4230,plain,(
    ! [A_212,B_213,B_214] : k5_xboole_0(A_212,k5_xboole_0(B_213,k3_xboole_0(k5_xboole_0(A_212,B_213),B_214))) = k4_xboole_0(k5_xboole_0(A_212,B_213),B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_12])).

tff(c_4372,plain,(
    ! [A_212,B_213] : k5_xboole_0(A_212,k5_xboole_0(B_213,k5_xboole_0(A_212,B_213))) = k4_xboole_0(k5_xboole_0(A_212,B_213),k5_xboole_0(A_212,B_213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4230])).

tff(c_4405,plain,(
    ! [A_212,B_213] : k5_xboole_0(A_212,k5_xboole_0(B_213,k5_xboole_0(A_212,B_213))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_4372])).

tff(c_7157,plain,(
    k5_xboole_0(k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')),k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7144,c_4405])).

tff(c_7255,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1159,c_7157])).

tff(c_7601,plain,(
    ! [A_247,B_248] : k5_xboole_0(k4_xboole_0(A_247,B_248),k3_xboole_0(B_248,A_247)) = A_247 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6998])).

tff(c_7629,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7255,c_7601])).

tff(c_7735,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7276,c_2,c_7629])).

tff(c_7966,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7735,c_96])).

tff(c_42,plain,(
    ! [B_57,A_56] :
      ( B_57 = A_56
      | ~ r1_tarski(k1_tarski(A_56),k1_tarski(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8015,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7966,c_42])).

tff(c_8021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_8015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:41:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.49/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.11  
% 5.55/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.58/2.11  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.58/2.11  
% 5.58/2.11  %Foreground sorts:
% 5.58/2.11  
% 5.58/2.11  
% 5.58/2.11  %Background operators:
% 5.58/2.11  
% 5.58/2.11  
% 5.58/2.11  %Foreground operators:
% 5.58/2.11  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.58/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.58/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.58/2.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.58/2.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.58/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.58/2.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.58/2.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.58/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.58/2.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.58/2.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.58/2.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.58/2.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.58/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.58/2.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.58/2.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.58/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.58/2.11  tff('#skF_4', type, '#skF_4': $i).
% 5.58/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.58/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.58/2.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.58/2.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.58/2.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.58/2.11  
% 5.58/2.13  tff(f_92, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 5.58/2.13  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.58/2.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.58/2.13  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.58/2.13  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.58/2.13  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.58/2.13  tff(f_55, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.58/2.13  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.58/2.13  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.58/2.13  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.58/2.13  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.58/2.13  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.58/2.13  tff(f_67, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.58/2.13  tff(f_87, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 5.58/2.13  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.58/2.13  tff(c_20, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.58/2.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.58/2.13  tff(c_22, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.58/2.13  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.58/2.13  tff(c_237, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.58/2.13  tff(c_272, plain, (![A_93, B_94]: (~r1_xboole_0(A_93, B_94) | k3_xboole_0(A_93, B_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_237])).
% 5.58/2.13  tff(c_282, plain, (![A_95, B_96]: (k3_xboole_0(k4_xboole_0(A_95, B_96), B_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_272])).
% 5.58/2.13  tff(c_81, plain, (![B_68, A_69]: (k3_xboole_0(B_68, A_69)=k3_xboole_0(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.58/2.13  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.58/2.13  tff(c_96, plain, (![B_68, A_69]: (r1_tarski(k3_xboole_0(B_68, A_69), A_69))), inference(superposition, [status(thm), theory('equality')], [c_81, c_14])).
% 5.58/2.13  tff(c_341, plain, (![B_99]: (r1_tarski(k1_xboole_0, B_99))), inference(superposition, [status(thm), theory('equality')], [c_282, c_96])).
% 5.58/2.13  tff(c_16, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.58/2.13  tff(c_346, plain, (![B_100]: (k3_xboole_0(k1_xboole_0, B_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_341, c_16])).
% 5.58/2.13  tff(c_407, plain, (![A_102]: (k3_xboole_0(A_102, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_346])).
% 5.58/2.13  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.58/2.13  tff(c_424, plain, (![A_102]: (k5_xboole_0(A_102, k1_xboole_0)=k4_xboole_0(A_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_407, c_12])).
% 5.58/2.13  tff(c_586, plain, (![A_112]: (k4_xboole_0(A_112, k1_xboole_0)=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_424])).
% 5.58/2.13  tff(c_26, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.58/2.13  tff(c_599, plain, (![A_112]: (k5_xboole_0(k1_xboole_0, A_112)=k2_xboole_0(k1_xboole_0, A_112))), inference(superposition, [status(thm), theory('equality')], [c_586, c_26])).
% 5.58/2.13  tff(c_18, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.58/2.13  tff(c_155, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.58/2.13  tff(c_1079, plain, (![A_151, B_152]: (k3_xboole_0(k4_xboole_0(A_151, B_152), A_151)=k4_xboole_0(A_151, B_152))), inference(resolution, [status(thm)], [c_18, c_155])).
% 5.58/2.13  tff(c_281, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_272])).
% 5.58/2.13  tff(c_1102, plain, (![A_151]: (k4_xboole_0(A_151, A_151)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1079, c_281])).
% 5.58/2.13  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.58/2.13  tff(c_173, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.58/2.13  tff(c_188, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_173])).
% 5.58/2.13  tff(c_1159, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_188])).
% 5.58/2.13  tff(c_487, plain, (![A_104, B_105, C_106]: (k5_xboole_0(k5_xboole_0(A_104, B_105), C_106)=k5_xboole_0(A_104, k5_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.58/2.13  tff(c_2767, plain, (![A_191, B_192, C_193]: (k5_xboole_0(A_191, k5_xboole_0(k3_xboole_0(A_191, B_192), C_193))=k5_xboole_0(k4_xboole_0(A_191, B_192), C_193))), inference(superposition, [status(thm), theory('equality')], [c_12, c_487])).
% 5.58/2.13  tff(c_2809, plain, (![A_191, B_192]: (k5_xboole_0(k4_xboole_0(A_191, B_192), k3_xboole_0(A_191, B_192))=k5_xboole_0(A_191, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1159, c_2767])).
% 5.58/2.13  tff(c_6998, plain, (![A_242, B_243]: (k5_xboole_0(k4_xboole_0(A_242, B_243), k3_xboole_0(A_242, B_243))=A_242)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2809])).
% 5.58/2.13  tff(c_7115, plain, (![A_3]: (k5_xboole_0(k4_xboole_0(A_3, A_3), A_3)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_6998])).
% 5.58/2.13  tff(c_7143, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_599, c_1102, c_7115])).
% 5.58/2.13  tff(c_7276, plain, (![A_112]: (k5_xboole_0(k1_xboole_0, A_112)=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_7143, c_599])).
% 5.58/2.13  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.58/2.13  tff(c_3076, plain, (![A_196, B_197, C_198]: (k5_xboole_0(A_196, k5_xboole_0(k4_xboole_0(B_197, A_196), C_198))=k5_xboole_0(k2_xboole_0(A_196, B_197), C_198))), inference(superposition, [status(thm), theory('equality')], [c_26, c_487])).
% 5.58/2.13  tff(c_3129, plain, (![A_196, B_197]: (k5_xboole_0(k2_xboole_0(A_196, B_197), k4_xboole_0(B_197, A_196))=k5_xboole_0(A_196, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1159, c_3076])).
% 5.58/2.13  tff(c_6166, plain, (![A_234, B_235]: (k5_xboole_0(k2_xboole_0(A_234, B_235), k4_xboole_0(B_235, A_234))=A_234)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3129])).
% 5.58/2.13  tff(c_6235, plain, (k5_xboole_0(k1_tarski('#skF_3'), k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3')))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_6166])).
% 5.58/2.13  tff(c_24, plain, (![A_23, B_24, C_25]: (k5_xboole_0(k5_xboole_0(A_23, B_24), C_25)=k5_xboole_0(A_23, k5_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.58/2.13  tff(c_7144, plain, (![C_244]: (k5_xboole_0(k1_tarski('#skF_3'), k5_xboole_0(k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3')), C_244))=k5_xboole_0(k1_tarski('#skF_3'), C_244))), inference(superposition, [status(thm), theory('equality')], [c_6235, c_24])).
% 5.58/2.13  tff(c_4230, plain, (![A_212, B_213, B_214]: (k5_xboole_0(A_212, k5_xboole_0(B_213, k3_xboole_0(k5_xboole_0(A_212, B_213), B_214)))=k4_xboole_0(k5_xboole_0(A_212, B_213), B_214))), inference(superposition, [status(thm), theory('equality')], [c_487, c_12])).
% 5.58/2.13  tff(c_4372, plain, (![A_212, B_213]: (k5_xboole_0(A_212, k5_xboole_0(B_213, k5_xboole_0(A_212, B_213)))=k4_xboole_0(k5_xboole_0(A_212, B_213), k5_xboole_0(A_212, B_213)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4230])).
% 5.58/2.13  tff(c_4405, plain, (![A_212, B_213]: (k5_xboole_0(A_212, k5_xboole_0(B_213, k5_xboole_0(A_212, B_213)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_4372])).
% 5.58/2.13  tff(c_7157, plain, (k5_xboole_0(k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3')), k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7144, c_4405])).
% 5.58/2.13  tff(c_7255, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1159, c_7157])).
% 5.58/2.13  tff(c_7601, plain, (![A_247, B_248]: (k5_xboole_0(k4_xboole_0(A_247, B_248), k3_xboole_0(B_248, A_247))=A_247)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6998])).
% 5.58/2.13  tff(c_7629, plain, (k5_xboole_0(k1_xboole_0, k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7255, c_7601])).
% 5.58/2.13  tff(c_7735, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7276, c_2, c_7629])).
% 5.58/2.13  tff(c_7966, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7735, c_96])).
% 5.58/2.13  tff(c_42, plain, (![B_57, A_56]: (B_57=A_56 | ~r1_tarski(k1_tarski(A_56), k1_tarski(B_57)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.58/2.13  tff(c_8015, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_7966, c_42])).
% 5.58/2.13  tff(c_8021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_8015])).
% 5.58/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.58/2.13  
% 5.58/2.13  Inference rules
% 5.58/2.13  ----------------------
% 5.58/2.13  #Ref     : 0
% 5.58/2.13  #Sup     : 1949
% 5.58/2.13  #Fact    : 0
% 5.58/2.13  #Define  : 0
% 5.58/2.13  #Split   : 0
% 5.58/2.13  #Chain   : 0
% 5.58/2.13  #Close   : 0
% 5.58/2.13  
% 5.58/2.13  Ordering : KBO
% 5.58/2.13  
% 5.58/2.13  Simplification rules
% 5.58/2.13  ----------------------
% 5.58/2.13  #Subsume      : 89
% 5.58/2.13  #Demod        : 2528
% 5.58/2.13  #Tautology    : 1409
% 5.58/2.13  #SimpNegUnit  : 17
% 5.58/2.13  #BackRed      : 6
% 5.58/2.13  
% 5.58/2.13  #Partial instantiations: 0
% 5.58/2.13  #Strategies tried      : 1
% 5.58/2.13  
% 5.58/2.13  Timing (in seconds)
% 5.58/2.13  ----------------------
% 5.58/2.13  Preprocessing        : 0.31
% 5.58/2.13  Parsing              : 0.17
% 5.58/2.13  CNF conversion       : 0.02
% 5.58/2.13  Main loop            : 1.06
% 5.58/2.13  Inferencing          : 0.30
% 5.58/2.13  Reduction            : 0.53
% 5.58/2.13  Demodulation         : 0.45
% 5.58/2.13  BG Simplification    : 0.04
% 5.58/2.13  Subsumption          : 0.13
% 5.58/2.13  Abstraction          : 0.05
% 5.58/2.13  MUC search           : 0.00
% 5.58/2.13  Cooper               : 0.00
% 5.58/2.13  Total                : 1.40
% 5.58/2.13  Index Insertion      : 0.00
% 5.58/2.13  Index Deletion       : 0.00
% 5.58/2.13  Index Matching       : 0.00
% 5.58/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

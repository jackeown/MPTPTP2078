%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:59 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 385 expanded)
%              Number of leaves         :   37 ( 145 expanded)
%              Depth                    :   18
%              Number of atoms          :   78 ( 506 expanded)
%              Number of equality atoms :   52 ( 268 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] : k5_xboole_0(k5_xboole_0(A_21,B_22),C_23) = k5_xboole_0(A_21,k5_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_142,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_591,plain,(
    ! [A_119,B_120] : k3_xboole_0(k4_xboole_0(A_119,B_120),A_119) = k4_xboole_0(A_119,B_120) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_165,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_181,plain,(
    ! [A_84,B_85] :
      ( ~ r1_xboole_0(A_84,B_85)
      | k3_xboole_0(A_84,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_185,plain,(
    ! [A_19,B_20] : k3_xboole_0(k4_xboole_0(A_19,B_20),B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_181])).

tff(c_610,plain,(
    ! [A_119] : k4_xboole_0(A_119,A_119) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_185])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_241,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_262,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_241])).

tff(c_738,plain,(
    ! [A_134] : k5_xboole_0(A_134,A_134) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_262])).

tff(c_757,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k5_xboole_0(B_22,k5_xboole_0(A_21,B_22))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_738])).

tff(c_655,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_262])).

tff(c_656,plain,(
    ! [A_125] : k4_xboole_0(A_125,A_125) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_185])).

tff(c_186,plain,(
    ! [A_86,B_87] : k3_xboole_0(k4_xboole_0(A_86,B_87),B_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_181])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [B_87,A_86] : k3_xboole_0(B_87,k4_xboole_0(A_86,B_87)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_2])).

tff(c_250,plain,(
    ! [B_87,A_86] : k4_xboole_0(B_87,k4_xboole_0(A_86,B_87)) = k5_xboole_0(B_87,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_241])).

tff(c_265,plain,(
    ! [B_87,A_86] : k4_xboole_0(B_87,k4_xboole_0(A_86,B_87)) = B_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_250])).

tff(c_950,plain,(
    ! [A_152] : k4_xboole_0(A_152,k1_xboole_0) = A_152 ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_265])).

tff(c_972,plain,(
    ! [A_152] : k5_xboole_0(k1_xboole_0,A_152) = k2_xboole_0(k1_xboole_0,A_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_24])).

tff(c_743,plain,(
    ! [A_134,C_23] : k5_xboole_0(A_134,k5_xboole_0(A_134,C_23)) = k5_xboole_0(k1_xboole_0,C_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_22])).

tff(c_1882,plain,(
    ! [A_177,C_178] : k5_xboole_0(A_177,k5_xboole_0(A_177,C_178)) = k2_xboole_0(k1_xboole_0,C_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_743])).

tff(c_1939,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_1882])).

tff(c_1972,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1939])).

tff(c_1881,plain,(
    ! [A_134,C_23] : k5_xboole_0(A_134,k5_xboole_0(A_134,C_23)) = k2_xboole_0(k1_xboole_0,C_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_743])).

tff(c_2158,plain,(
    ! [A_183,C_184] : k5_xboole_0(A_183,k5_xboole_0(A_183,C_184)) = C_184 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1972,c_1881])).

tff(c_2202,plain,(
    ! [B_22,A_21] : k5_xboole_0(B_22,k5_xboole_0(A_21,B_22)) = k5_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_2158])).

tff(c_2248,plain,(
    ! [B_185,A_186] : k5_xboole_0(B_185,k5_xboole_0(A_186,B_185)) = A_186 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2202])).

tff(c_1975,plain,(
    ! [A_134,C_23] : k5_xboole_0(A_134,k5_xboole_0(A_134,C_23)) = C_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1972,c_1881])).

tff(c_2257,plain,(
    ! [B_185,A_186] : k5_xboole_0(B_185,A_186) = k5_xboole_0(A_186,B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_2248,c_1975])).

tff(c_42,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_tarski(A_54),B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_149,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(k1_tarski(A_54),B_55) = k1_tarski(A_54)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_42,c_142])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_420,plain,(
    ! [A_107,B_108,C_109] : k5_xboole_0(k5_xboole_0(A_107,B_108),C_109) = k5_xboole_0(A_107,k5_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3178,plain,(
    ! [A_206,B_207,C_208] : k5_xboole_0(A_206,k5_xboole_0(k3_xboole_0(A_206,B_207),C_208)) = k5_xboole_0(k4_xboole_0(A_206,B_207),C_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_420])).

tff(c_3275,plain,(
    ! [A_206,B_207] : k5_xboole_0(k4_xboole_0(A_206,B_207),k3_xboole_0(A_206,B_207)) = k5_xboole_0(A_206,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_3178])).

tff(c_3328,plain,(
    ! [A_209,B_210] : k5_xboole_0(k4_xboole_0(A_209,B_210),k3_xboole_0(A_209,B_210)) = A_209 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3275])).

tff(c_3434,plain,(
    ! [A_211,B_212] : k5_xboole_0(k4_xboole_0(A_211,B_212),k3_xboole_0(B_212,A_211)) = A_211 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3328])).

tff(c_3484,plain,(
    ! [B_55,A_54] :
      ( k5_xboole_0(k4_xboole_0(B_55,k1_tarski(A_54)),k1_tarski(A_54)) = B_55
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_3434])).

tff(c_4543,plain,(
    ! [A_232,B_233] :
      ( k2_xboole_0(k1_tarski(A_232),B_233) = B_233
      | ~ r2_hidden(A_232,B_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2257,c_3484])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4584,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4543,c_46])).

tff(c_4618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4584])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:22:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.95  
% 4.62/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.96  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.62/1.96  
% 4.62/1.96  %Foreground sorts:
% 4.62/1.96  
% 4.62/1.96  
% 4.62/1.96  %Background operators:
% 4.62/1.96  
% 4.62/1.96  
% 4.62/1.96  %Foreground operators:
% 4.62/1.96  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.62/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.62/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.62/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.62/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.62/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.62/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.62/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.62/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.62/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.96  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.96  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.96  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.62/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.62/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.62/1.96  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.62/1.96  
% 4.62/1.97  tff(f_92, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.62/1.97  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.62/1.97  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.62/1.97  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.62/1.97  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.62/1.97  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.62/1.97  tff(f_63, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.62/1.97  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.62/1.97  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.62/1.97  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.62/1.97  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.62/1.97  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.62/1.97  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.62/1.97  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.62/1.97  tff(c_24, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.62/1.97  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.62/1.97  tff(c_22, plain, (![A_21, B_22, C_23]: (k5_xboole_0(k5_xboole_0(A_21, B_22), C_23)=k5_xboole_0(A_21, k5_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.62/1.97  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.62/1.97  tff(c_142, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.62/1.97  tff(c_591, plain, (![A_119, B_120]: (k3_xboole_0(k4_xboole_0(A_119, B_120), A_119)=k4_xboole_0(A_119, B_120))), inference(resolution, [status(thm)], [c_16, c_142])).
% 4.62/1.97  tff(c_20, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.62/1.97  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.62/1.97  tff(c_165, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.62/1.97  tff(c_181, plain, (![A_84, B_85]: (~r1_xboole_0(A_84, B_85) | k3_xboole_0(A_84, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_165])).
% 4.62/1.97  tff(c_185, plain, (![A_19, B_20]: (k3_xboole_0(k4_xboole_0(A_19, B_20), B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_181])).
% 4.62/1.97  tff(c_610, plain, (![A_119]: (k4_xboole_0(A_119, A_119)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_591, c_185])).
% 4.62/1.97  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.62/1.97  tff(c_241, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.62/1.97  tff(c_262, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_241])).
% 4.62/1.97  tff(c_738, plain, (![A_134]: (k5_xboole_0(A_134, A_134)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_610, c_262])).
% 4.62/1.97  tff(c_757, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k5_xboole_0(B_22, k5_xboole_0(A_21, B_22)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_738])).
% 4.62/1.97  tff(c_655, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_610, c_262])).
% 4.62/1.97  tff(c_656, plain, (![A_125]: (k4_xboole_0(A_125, A_125)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_591, c_185])).
% 4.62/1.97  tff(c_186, plain, (![A_86, B_87]: (k3_xboole_0(k4_xboole_0(A_86, B_87), B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_181])).
% 4.62/1.97  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.62/1.97  tff(c_197, plain, (![B_87, A_86]: (k3_xboole_0(B_87, k4_xboole_0(A_86, B_87))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_186, c_2])).
% 4.62/1.97  tff(c_250, plain, (![B_87, A_86]: (k4_xboole_0(B_87, k4_xboole_0(A_86, B_87))=k5_xboole_0(B_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_197, c_241])).
% 4.62/1.97  tff(c_265, plain, (![B_87, A_86]: (k4_xboole_0(B_87, k4_xboole_0(A_86, B_87))=B_87)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_250])).
% 4.62/1.97  tff(c_950, plain, (![A_152]: (k4_xboole_0(A_152, k1_xboole_0)=A_152)), inference(superposition, [status(thm), theory('equality')], [c_656, c_265])).
% 4.62/1.97  tff(c_972, plain, (![A_152]: (k5_xboole_0(k1_xboole_0, A_152)=k2_xboole_0(k1_xboole_0, A_152))), inference(superposition, [status(thm), theory('equality')], [c_950, c_24])).
% 4.62/1.97  tff(c_743, plain, (![A_134, C_23]: (k5_xboole_0(A_134, k5_xboole_0(A_134, C_23))=k5_xboole_0(k1_xboole_0, C_23))), inference(superposition, [status(thm), theory('equality')], [c_738, c_22])).
% 4.62/1.97  tff(c_1882, plain, (![A_177, C_178]: (k5_xboole_0(A_177, k5_xboole_0(A_177, C_178))=k2_xboole_0(k1_xboole_0, C_178))), inference(demodulation, [status(thm), theory('equality')], [c_972, c_743])).
% 4.62/1.97  tff(c_1939, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_655, c_1882])).
% 4.62/1.97  tff(c_1972, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1939])).
% 4.62/1.97  tff(c_1881, plain, (![A_134, C_23]: (k5_xboole_0(A_134, k5_xboole_0(A_134, C_23))=k2_xboole_0(k1_xboole_0, C_23))), inference(demodulation, [status(thm), theory('equality')], [c_972, c_743])).
% 4.62/1.97  tff(c_2158, plain, (![A_183, C_184]: (k5_xboole_0(A_183, k5_xboole_0(A_183, C_184))=C_184)), inference(demodulation, [status(thm), theory('equality')], [c_1972, c_1881])).
% 4.62/1.97  tff(c_2202, plain, (![B_22, A_21]: (k5_xboole_0(B_22, k5_xboole_0(A_21, B_22))=k5_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_757, c_2158])).
% 4.62/1.97  tff(c_2248, plain, (![B_185, A_186]: (k5_xboole_0(B_185, k5_xboole_0(A_186, B_185))=A_186)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2202])).
% 4.62/1.97  tff(c_1975, plain, (![A_134, C_23]: (k5_xboole_0(A_134, k5_xboole_0(A_134, C_23))=C_23)), inference(demodulation, [status(thm), theory('equality')], [c_1972, c_1881])).
% 4.62/1.97  tff(c_2257, plain, (![B_185, A_186]: (k5_xboole_0(B_185, A_186)=k5_xboole_0(A_186, B_185))), inference(superposition, [status(thm), theory('equality')], [c_2248, c_1975])).
% 4.62/1.97  tff(c_42, plain, (![A_54, B_55]: (r1_tarski(k1_tarski(A_54), B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.62/1.97  tff(c_149, plain, (![A_54, B_55]: (k3_xboole_0(k1_tarski(A_54), B_55)=k1_tarski(A_54) | ~r2_hidden(A_54, B_55))), inference(resolution, [status(thm)], [c_42, c_142])).
% 4.62/1.97  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.62/1.97  tff(c_420, plain, (![A_107, B_108, C_109]: (k5_xboole_0(k5_xboole_0(A_107, B_108), C_109)=k5_xboole_0(A_107, k5_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.62/1.97  tff(c_3178, plain, (![A_206, B_207, C_208]: (k5_xboole_0(A_206, k5_xboole_0(k3_xboole_0(A_206, B_207), C_208))=k5_xboole_0(k4_xboole_0(A_206, B_207), C_208))), inference(superposition, [status(thm), theory('equality')], [c_12, c_420])).
% 4.62/1.97  tff(c_3275, plain, (![A_206, B_207]: (k5_xboole_0(k4_xboole_0(A_206, B_207), k3_xboole_0(A_206, B_207))=k5_xboole_0(A_206, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_655, c_3178])).
% 4.62/1.97  tff(c_3328, plain, (![A_209, B_210]: (k5_xboole_0(k4_xboole_0(A_209, B_210), k3_xboole_0(A_209, B_210))=A_209)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3275])).
% 4.62/1.97  tff(c_3434, plain, (![A_211, B_212]: (k5_xboole_0(k4_xboole_0(A_211, B_212), k3_xboole_0(B_212, A_211))=A_211)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3328])).
% 4.62/1.97  tff(c_3484, plain, (![B_55, A_54]: (k5_xboole_0(k4_xboole_0(B_55, k1_tarski(A_54)), k1_tarski(A_54))=B_55 | ~r2_hidden(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_149, c_3434])).
% 4.62/1.97  tff(c_4543, plain, (![A_232, B_233]: (k2_xboole_0(k1_tarski(A_232), B_233)=B_233 | ~r2_hidden(A_232, B_233))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2257, c_3484])).
% 4.62/1.97  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.62/1.97  tff(c_4584, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4543, c_46])).
% 4.62/1.97  tff(c_4618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_4584])).
% 4.62/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.97  
% 4.62/1.97  Inference rules
% 4.62/1.97  ----------------------
% 4.62/1.97  #Ref     : 0
% 4.62/1.97  #Sup     : 1101
% 4.62/1.97  #Fact    : 0
% 4.62/1.97  #Define  : 0
% 4.62/1.97  #Split   : 0
% 4.62/1.97  #Chain   : 0
% 4.62/1.97  #Close   : 0
% 4.62/1.97  
% 4.62/1.97  Ordering : KBO
% 4.62/1.97  
% 4.62/1.97  Simplification rules
% 4.62/1.97  ----------------------
% 4.62/1.97  #Subsume      : 53
% 4.62/1.97  #Demod        : 973
% 4.62/1.97  #Tautology    : 727
% 4.62/1.97  #SimpNegUnit  : 8
% 4.62/1.97  #BackRed      : 8
% 4.62/1.97  
% 4.62/1.97  #Partial instantiations: 0
% 4.62/1.97  #Strategies tried      : 1
% 4.62/1.97  
% 4.62/1.97  Timing (in seconds)
% 4.62/1.97  ----------------------
% 4.62/1.98  Preprocessing        : 0.33
% 4.62/1.98  Parsing              : 0.18
% 4.62/1.98  CNF conversion       : 0.02
% 4.62/1.98  Main loop            : 0.86
% 4.62/1.98  Inferencing          : 0.29
% 4.62/1.98  Reduction            : 0.36
% 4.62/1.98  Demodulation         : 0.28
% 4.62/1.98  BG Simplification    : 0.03
% 4.62/1.98  Subsumption          : 0.11
% 4.62/1.98  Abstraction          : 0.06
% 4.62/1.98  MUC search           : 0.00
% 4.62/1.98  Cooper               : 0.00
% 4.62/1.98  Total                : 1.22
% 4.62/1.98  Index Insertion      : 0.00
% 4.62/1.98  Index Deletion       : 0.00
% 4.62/1.98  Index Matching       : 0.00
% 4.62/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------

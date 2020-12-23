%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:15 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 288 expanded)
%              Number of leaves         :   37 ( 111 expanded)
%              Depth                    :   15
%              Number of atoms          :   96 ( 415 expanded)
%              Number of equality atoms :   81 ( 397 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_84,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_64,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_126,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_129,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_119,plain,(
    ! [A_71,B_72] : r1_tarski(A_71,k2_xboole_0(A_71,B_72)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_122,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_119])).

tff(c_536,plain,(
    ! [B_118,A_119] :
      ( k1_tarski(B_118) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k1_tarski(B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_547,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_122,c_536])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_129,c_547])).

tff(c_559,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_594,plain,(
    ! [B_124,A_125] : k5_xboole_0(B_124,A_125) = k5_xboole_0(A_125,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_610,plain,(
    ! [A_125] : k5_xboole_0(k1_xboole_0,A_125) = A_125 ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_26])).

tff(c_36,plain,(
    ! [A_30] : k5_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1112,plain,(
    ! [A_171,B_172,C_173] : k5_xboole_0(k5_xboole_0(A_171,B_172),C_173) = k5_xboole_0(A_171,k5_xboole_0(B_172,C_173)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1176,plain,(
    ! [A_30,C_173] : k5_xboole_0(A_30,k5_xboole_0(A_30,C_173)) = k5_xboole_0(k1_xboole_0,C_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1112])).

tff(c_1190,plain,(
    ! [A_174,C_175] : k5_xboole_0(A_174,k5_xboole_0(A_174,C_175)) = C_175 ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_1176])).

tff(c_1255,plain,(
    ! [A_176,B_177] : k5_xboole_0(A_176,k5_xboole_0(B_177,A_176)) = B_177 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1190])).

tff(c_1233,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1190])).

tff(c_1258,plain,(
    ! [B_177,A_176] : k5_xboole_0(k5_xboole_0(B_177,A_176),B_177) = A_176 ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_1233])).

tff(c_560,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_562,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_68])).

tff(c_1335,plain,(
    ! [A_178,B_179] : k5_xboole_0(k5_xboole_0(A_178,B_179),k2_xboole_0(A_178,B_179)) = k3_xboole_0(A_178,B_179) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1411,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_1335])).

tff(c_1713,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_1411])).

tff(c_66,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_689,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_560,c_66])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_930,plain,(
    ! [B_156,A_157] :
      ( k1_tarski(B_156) = A_157
      | k1_xboole_0 = A_157
      | ~ r1_tarski(A_157,k1_tarski(B_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_941,plain,(
    ! [A_157] :
      ( k1_tarski('#skF_3') = A_157
      | k1_xboole_0 = A_157
      | ~ r1_tarski(A_157,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_930])).

tff(c_953,plain,(
    ! [A_158] :
      ( A_158 = '#skF_4'
      | k1_xboole_0 = A_158
      | ~ r1_tarski(A_158,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_941])).

tff(c_970,plain,(
    ! [B_22] :
      ( k4_xboole_0('#skF_4',B_22) = '#skF_4'
      | k4_xboole_0('#skF_4',B_22) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_953])).

tff(c_20,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1717,plain,(
    k5_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1713,c_20])).

tff(c_1189,plain,(
    ! [A_30,C_173] : k5_xboole_0(A_30,k5_xboole_0(A_30,C_173)) = C_173 ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_1176])).

tff(c_1288,plain,(
    ! [A_30,C_173] : k5_xboole_0(k5_xboole_0(A_30,C_173),C_173) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_1189,c_1255])).

tff(c_1726,plain,(
    k5_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1717,c_1288])).

tff(c_1774,plain,
    ( k5_xboole_0(k1_xboole_0,'#skF_5') = '#skF_4'
    | k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_1726])).

tff(c_1784,plain,
    ( '#skF_5' = '#skF_4'
    | k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2,c_1774])).

tff(c_1785,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_689,c_1784])).

tff(c_1786,plain,(
    k5_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1785,c_1726])).

tff(c_38,plain,(
    ! [A_31,B_32] : k5_xboole_0(k5_xboole_0(A_31,B_32),k2_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1828,plain,(
    k5_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_5')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_38])).

tff(c_1841,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1713,c_36,c_562,c_1828])).

tff(c_1843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_1841])).

tff(c_1844,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1845,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1847,plain,(
    ! [A_30] : k5_xboole_0(A_30,A_30) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_36])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2085,plain,(
    ! [A_224,B_225] : k5_xboole_0(A_224,k3_xboole_0(A_224,B_225)) = k4_xboole_0(A_224,B_225) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2102,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k4_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2085])).

tff(c_2106,plain,(
    ! [A_226] : k4_xboole_0(A_226,A_226) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_2102])).

tff(c_2022,plain,(
    ! [A_209,B_210] :
      ( k2_xboole_0(A_209,B_210) = B_210
      | ~ r1_tarski(A_209,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2035,plain,(
    ! [A_21,B_22] : k2_xboole_0(k4_xboole_0(A_21,B_22),A_21) = A_21 ),
    inference(resolution,[status(thm)],[c_24,c_2022])).

tff(c_2111,plain,(
    ! [A_226] : k2_xboole_0('#skF_4',A_226) = A_226 ),
    inference(superposition,[status(thm),theory(equality)],[c_2106,c_2035])).

tff(c_2136,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2111,c_68])).

tff(c_2138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1844,c_2136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/2.15  
% 4.51/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/2.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.51/2.15  
% 4.51/2.15  %Foreground sorts:
% 4.51/2.15  
% 4.51/2.15  
% 4.51/2.15  %Background operators:
% 4.51/2.15  
% 4.51/2.15  
% 4.51/2.15  %Foreground operators:
% 4.51/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/2.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.51/2.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.51/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/2.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.51/2.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.51/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/2.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.51/2.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/2.15  tff('#skF_5', type, '#skF_5': $i).
% 4.51/2.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.51/2.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.51/2.15  tff('#skF_3', type, '#skF_3': $i).
% 4.51/2.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.51/2.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.51/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/2.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.51/2.15  tff('#skF_4', type, '#skF_4': $i).
% 4.51/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/2.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.51/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.51/2.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.51/2.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.51/2.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.51/2.15  
% 4.51/2.17  tff(f_127, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.51/2.17  tff(f_80, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.51/2.17  tff(f_106, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.51/2.17  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.51/2.17  tff(f_66, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.51/2.17  tff(f_84, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.51/2.17  tff(f_82, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.51/2.17  tff(f_86, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.51/2.17  tff(f_64, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.51/2.17  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.51/2.17  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.51/2.17  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.51/2.17  tff(c_64, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.51/2.17  tff(c_126, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 4.51/2.17  tff(c_62, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.51/2.17  tff(c_129, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 4.51/2.17  tff(c_68, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.51/2.17  tff(c_119, plain, (![A_71, B_72]: (r1_tarski(A_71, k2_xboole_0(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.51/2.17  tff(c_122, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_119])).
% 4.51/2.17  tff(c_536, plain, (![B_118, A_119]: (k1_tarski(B_118)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k1_tarski(B_118)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/2.17  tff(c_547, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_122, c_536])).
% 4.51/2.17  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_129, c_547])).
% 4.51/2.17  tff(c_559, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 4.51/2.17  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.51/2.17  tff(c_594, plain, (![B_124, A_125]: (k5_xboole_0(B_124, A_125)=k5_xboole_0(A_125, B_124))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.51/2.17  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.51/2.17  tff(c_610, plain, (![A_125]: (k5_xboole_0(k1_xboole_0, A_125)=A_125)), inference(superposition, [status(thm), theory('equality')], [c_594, c_26])).
% 4.51/2.17  tff(c_36, plain, (![A_30]: (k5_xboole_0(A_30, A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.51/2.17  tff(c_1112, plain, (![A_171, B_172, C_173]: (k5_xboole_0(k5_xboole_0(A_171, B_172), C_173)=k5_xboole_0(A_171, k5_xboole_0(B_172, C_173)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.51/2.17  tff(c_1176, plain, (![A_30, C_173]: (k5_xboole_0(A_30, k5_xboole_0(A_30, C_173))=k5_xboole_0(k1_xboole_0, C_173))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1112])).
% 4.51/2.17  tff(c_1190, plain, (![A_174, C_175]: (k5_xboole_0(A_174, k5_xboole_0(A_174, C_175))=C_175)), inference(demodulation, [status(thm), theory('equality')], [c_610, c_1176])).
% 4.51/2.17  tff(c_1255, plain, (![A_176, B_177]: (k5_xboole_0(A_176, k5_xboole_0(B_177, A_176))=B_177)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1190])).
% 4.51/2.17  tff(c_1233, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1190])).
% 4.51/2.17  tff(c_1258, plain, (![B_177, A_176]: (k5_xboole_0(k5_xboole_0(B_177, A_176), B_177)=A_176)), inference(superposition, [status(thm), theory('equality')], [c_1255, c_1233])).
% 4.51/2.17  tff(c_560, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 4.51/2.17  tff(c_562, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_68])).
% 4.51/2.17  tff(c_1335, plain, (![A_178, B_179]: (k5_xboole_0(k5_xboole_0(A_178, B_179), k2_xboole_0(A_178, B_179))=k3_xboole_0(A_178, B_179))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.51/2.17  tff(c_1411, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_562, c_1335])).
% 4.51/2.17  tff(c_1713, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_1411])).
% 4.51/2.17  tff(c_66, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.51/2.17  tff(c_689, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_560, c_66])).
% 4.51/2.17  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.51/2.17  tff(c_930, plain, (![B_156, A_157]: (k1_tarski(B_156)=A_157 | k1_xboole_0=A_157 | ~r1_tarski(A_157, k1_tarski(B_156)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/2.17  tff(c_941, plain, (![A_157]: (k1_tarski('#skF_3')=A_157 | k1_xboole_0=A_157 | ~r1_tarski(A_157, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_560, c_930])).
% 4.51/2.17  tff(c_953, plain, (![A_158]: (A_158='#skF_4' | k1_xboole_0=A_158 | ~r1_tarski(A_158, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_941])).
% 4.51/2.17  tff(c_970, plain, (![B_22]: (k4_xboole_0('#skF_4', B_22)='#skF_4' | k4_xboole_0('#skF_4', B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_953])).
% 4.51/2.17  tff(c_20, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/2.17  tff(c_1717, plain, (k5_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1713, c_20])).
% 4.51/2.17  tff(c_1189, plain, (![A_30, C_173]: (k5_xboole_0(A_30, k5_xboole_0(A_30, C_173))=C_173)), inference(demodulation, [status(thm), theory('equality')], [c_610, c_1176])).
% 4.51/2.17  tff(c_1288, plain, (![A_30, C_173]: (k5_xboole_0(k5_xboole_0(A_30, C_173), C_173)=A_30)), inference(superposition, [status(thm), theory('equality')], [c_1189, c_1255])).
% 4.51/2.17  tff(c_1726, plain, (k5_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1717, c_1288])).
% 4.51/2.17  tff(c_1774, plain, (k5_xboole_0(k1_xboole_0, '#skF_5')='#skF_4' | k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_970, c_1726])).
% 4.51/2.17  tff(c_1784, plain, ('#skF_5'='#skF_4' | k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2, c_1774])).
% 4.51/2.17  tff(c_1785, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_689, c_1784])).
% 4.51/2.17  tff(c_1786, plain, (k5_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1785, c_1726])).
% 4.51/2.18  tff(c_38, plain, (![A_31, B_32]: (k5_xboole_0(k5_xboole_0(A_31, B_32), k2_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.51/2.18  tff(c_1828, plain, (k5_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_5'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1786, c_38])).
% 4.51/2.18  tff(c_1841, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1713, c_36, c_562, c_1828])).
% 4.51/2.18  tff(c_1843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_559, c_1841])).
% 4.51/2.18  tff(c_1844, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 4.51/2.18  tff(c_1845, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 4.51/2.18  tff(c_1847, plain, (![A_30]: (k5_xboole_0(A_30, A_30)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_36])).
% 4.51/2.18  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.51/2.18  tff(c_2085, plain, (![A_224, B_225]: (k5_xboole_0(A_224, k3_xboole_0(A_224, B_225))=k4_xboole_0(A_224, B_225))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/2.18  tff(c_2102, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k4_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2085])).
% 4.51/2.18  tff(c_2106, plain, (![A_226]: (k4_xboole_0(A_226, A_226)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_2102])).
% 4.51/2.18  tff(c_2022, plain, (![A_209, B_210]: (k2_xboole_0(A_209, B_210)=B_210 | ~r1_tarski(A_209, B_210))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.51/2.18  tff(c_2035, plain, (![A_21, B_22]: (k2_xboole_0(k4_xboole_0(A_21, B_22), A_21)=A_21)), inference(resolution, [status(thm)], [c_24, c_2022])).
% 4.51/2.18  tff(c_2111, plain, (![A_226]: (k2_xboole_0('#skF_4', A_226)=A_226)), inference(superposition, [status(thm), theory('equality')], [c_2106, c_2035])).
% 4.51/2.18  tff(c_2136, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2111, c_68])).
% 4.51/2.18  tff(c_2138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1844, c_2136])).
% 4.51/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/2.18  
% 4.51/2.18  Inference rules
% 4.51/2.18  ----------------------
% 4.51/2.18  #Ref     : 0
% 4.51/2.18  #Sup     : 490
% 4.51/2.18  #Fact    : 1
% 4.51/2.18  #Define  : 0
% 4.51/2.18  #Split   : 3
% 4.51/2.18  #Chain   : 0
% 4.51/2.18  #Close   : 0
% 4.51/2.18  
% 4.51/2.18  Ordering : KBO
% 4.51/2.18  
% 4.51/2.18  Simplification rules
% 4.51/2.18  ----------------------
% 4.51/2.18  #Subsume      : 9
% 4.51/2.18  #Demod        : 240
% 4.51/2.18  #Tautology    : 361
% 4.51/2.18  #SimpNegUnit  : 10
% 4.51/2.18  #BackRed      : 12
% 4.51/2.18  
% 4.51/2.18  #Partial instantiations: 0
% 4.51/2.18  #Strategies tried      : 1
% 4.51/2.18  
% 4.51/2.18  Timing (in seconds)
% 4.51/2.18  ----------------------
% 4.51/2.18  Preprocessing        : 0.57
% 4.51/2.18  Parsing              : 0.30
% 4.51/2.18  CNF conversion       : 0.04
% 4.51/2.18  Main loop            : 0.80
% 4.51/2.18  Inferencing          : 0.29
% 4.51/2.18  Reduction            : 0.30
% 4.51/2.18  Demodulation         : 0.23
% 4.51/2.18  BG Simplification    : 0.04
% 4.51/2.18  Subsumption          : 0.11
% 4.51/2.18  Abstraction          : 0.04
% 4.51/2.18  MUC search           : 0.00
% 4.51/2.18  Cooper               : 0.00
% 4.51/2.18  Total                : 1.43
% 4.51/2.18  Index Insertion      : 0.00
% 4.51/2.18  Index Deletion       : 0.00
% 4.51/2.18  Index Matching       : 0.00
% 4.51/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

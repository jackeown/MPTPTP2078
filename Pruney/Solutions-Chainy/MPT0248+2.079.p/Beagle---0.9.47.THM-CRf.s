%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:15 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 131 expanded)
%              Number of leaves         :   41 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 243 expanded)
%              Number of equality atoms :   61 ( 199 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_64,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_105,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_111,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_112,plain,(
    ! [A_72,B_73] : r1_tarski(A_72,k2_xboole_0(A_72,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_115,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_112])).

tff(c_470,plain,(
    ! [B_121,A_122] :
      ( k1_tarski(B_121) = A_122
      | k1_xboole_0 = A_122
      | ~ r1_tarski(A_122,k1_tarski(B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_485,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_115,c_470])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_111,c_485])).

tff(c_498,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_499,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_517,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_499,c_66])).

tff(c_500,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_68])).

tff(c_30,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_16] : k3_xboole_0(A_16,A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_14] : k2_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1454,plain,(
    ! [A_213,B_214] : k5_xboole_0(k5_xboole_0(A_213,B_214),k2_xboole_0(A_213,B_214)) = k3_xboole_0(A_213,B_214) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1499,plain,(
    ! [A_14] : k5_xboole_0(k5_xboole_0(A_14,A_14),A_14) = k3_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1454])).

tff(c_1506,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_1499])).

tff(c_1642,plain,(
    ! [A_218,B_219,C_220] : k5_xboole_0(k5_xboole_0(A_218,B_219),C_220) = k5_xboole_0(A_218,k5_xboole_0(B_219,C_220)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1720,plain,(
    ! [A_25,C_220] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_220)) = k5_xboole_0(k1_xboole_0,C_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1642])).

tff(c_1736,plain,(
    ! [A_25,C_220] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_220)) = C_220 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_1720])).

tff(c_1496,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_1454])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1602,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_5')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_2])).

tff(c_1737,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1736,c_1602])).

tff(c_640,plain,(
    ! [A_139,B_140] :
      ( r1_xboole_0(k1_tarski(A_139),B_140)
      | r2_hidden(A_139,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_643,plain,(
    ! [B_140] :
      ( r1_xboole_0('#skF_4',B_140)
      | r2_hidden('#skF_3',B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_640])).

tff(c_754,plain,(
    ! [A_157,B_158] :
      ( r1_tarski(k1_tarski(A_157),B_158)
      | ~ r2_hidden(A_157,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_782,plain,(
    ! [B_160] :
      ( r1_tarski('#skF_4',B_160)
      | ~ r2_hidden('#skF_3',B_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_754])).

tff(c_813,plain,(
    ! [B_161] :
      ( r1_tarski('#skF_4',B_161)
      | r1_xboole_0('#skF_4',B_161) ) ),
    inference(resolution,[status(thm)],[c_643,c_782])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_818,plain,(
    ! [B_162] :
      ( k3_xboole_0('#skF_4',B_162) = k1_xboole_0
      | r1_tarski('#skF_4',B_162) ) ),
    inference(resolution,[status(thm)],[c_813,c_14])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_825,plain,(
    ! [B_162] :
      ( k2_xboole_0('#skF_4',B_162) = B_162
      | k3_xboole_0('#skF_4',B_162) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_818,c_24])).

tff(c_1813,plain,
    ( k2_xboole_0('#skF_4','#skF_5') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1737,c_825])).

tff(c_1819,plain,
    ( '#skF_5' = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_1813])).

tff(c_1821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_517,c_1819])).

tff(c_1822,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1823,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1826,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_18])).

tff(c_2006,plain,(
    ! [A_257,B_258] :
      ( r2_hidden('#skF_2'(A_257,B_258),A_257)
      | r1_tarski(A_257,B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2011,plain,(
    ! [A_259,B_260] :
      ( ~ v1_xboole_0(A_259)
      | r1_tarski(A_259,B_260) ) ),
    inference(resolution,[status(thm)],[c_2006,c_4])).

tff(c_2021,plain,(
    ! [A_261,B_262] :
      ( k2_xboole_0(A_261,B_262) = B_262
      | ~ v1_xboole_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_2011,c_24])).

tff(c_2024,plain,(
    ! [B_262] : k2_xboole_0('#skF_4',B_262) = B_262 ),
    inference(resolution,[status(thm)],[c_1826,c_2021])).

tff(c_2033,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2024,c_68])).

tff(c_2035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1822,c_2033])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:27:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.55  
% 3.52/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.55  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.52/1.55  
% 3.52/1.55  %Foreground sorts:
% 3.52/1.55  
% 3.52/1.55  
% 3.52/1.55  %Background operators:
% 3.52/1.55  
% 3.52/1.55  
% 3.52/1.55  %Foreground operators:
% 3.52/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.52/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.52/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.52/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.52/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.52/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.52/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.52/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.52/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.52/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.52/1.55  
% 3.52/1.57  tff(f_111, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.52/1.57  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.52/1.57  tff(f_90, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.52/1.57  tff(f_59, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.52/1.57  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.52/1.57  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.52/1.57  tff(f_61, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.52/1.57  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.52/1.57  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.52/1.57  tff(f_84, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.52/1.57  tff(f_79, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.52/1.57  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.52/1.57  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.52/1.57  tff(f_45, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.52/1.57  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.52/1.57  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.52/1.57  tff(c_64, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.52/1.57  tff(c_105, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 3.52/1.57  tff(c_62, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.52/1.57  tff(c_111, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 3.52/1.57  tff(c_68, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.52/1.57  tff(c_112, plain, (![A_72, B_73]: (r1_tarski(A_72, k2_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.52/1.57  tff(c_115, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_112])).
% 3.52/1.57  tff(c_470, plain, (![B_121, A_122]: (k1_tarski(B_121)=A_122 | k1_xboole_0=A_122 | ~r1_tarski(A_122, k1_tarski(B_121)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.52/1.57  tff(c_485, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_115, c_470])).
% 3.52/1.57  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_111, c_485])).
% 3.52/1.57  tff(c_498, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 3.52/1.57  tff(c_499, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 3.52/1.57  tff(c_66, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.52/1.57  tff(c_517, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_499, c_499, c_66])).
% 3.52/1.57  tff(c_500, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_499, c_68])).
% 3.52/1.57  tff(c_30, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.57  tff(c_22, plain, (![A_16]: (k3_xboole_0(A_16, A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.52/1.57  tff(c_20, plain, (![A_14]: (k2_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.52/1.57  tff(c_1454, plain, (![A_213, B_214]: (k5_xboole_0(k5_xboole_0(A_213, B_214), k2_xboole_0(A_213, B_214))=k3_xboole_0(A_213, B_214))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.52/1.57  tff(c_1499, plain, (![A_14]: (k5_xboole_0(k5_xboole_0(A_14, A_14), A_14)=k3_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1454])).
% 3.52/1.57  tff(c_1506, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22, c_1499])).
% 3.52/1.57  tff(c_1642, plain, (![A_218, B_219, C_220]: (k5_xboole_0(k5_xboole_0(A_218, B_219), C_220)=k5_xboole_0(A_218, k5_xboole_0(B_219, C_220)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.57  tff(c_1720, plain, (![A_25, C_220]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_220))=k5_xboole_0(k1_xboole_0, C_220))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1642])).
% 3.52/1.57  tff(c_1736, plain, (![A_25, C_220]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_220))=C_220)), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_1720])).
% 3.52/1.57  tff(c_1496, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_500, c_1454])).
% 3.52/1.57  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.57  tff(c_1602, plain, (k5_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_5'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1496, c_2])).
% 3.52/1.57  tff(c_1737, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1736, c_1602])).
% 3.52/1.57  tff(c_640, plain, (![A_139, B_140]: (r1_xboole_0(k1_tarski(A_139), B_140) | r2_hidden(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.52/1.57  tff(c_643, plain, (![B_140]: (r1_xboole_0('#skF_4', B_140) | r2_hidden('#skF_3', B_140))), inference(superposition, [status(thm), theory('equality')], [c_499, c_640])).
% 3.52/1.57  tff(c_754, plain, (![A_157, B_158]: (r1_tarski(k1_tarski(A_157), B_158) | ~r2_hidden(A_157, B_158))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.52/1.57  tff(c_782, plain, (![B_160]: (r1_tarski('#skF_4', B_160) | ~r2_hidden('#skF_3', B_160))), inference(superposition, [status(thm), theory('equality')], [c_499, c_754])).
% 3.52/1.57  tff(c_813, plain, (![B_161]: (r1_tarski('#skF_4', B_161) | r1_xboole_0('#skF_4', B_161))), inference(resolution, [status(thm)], [c_643, c_782])).
% 3.52/1.57  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.52/1.57  tff(c_818, plain, (![B_162]: (k3_xboole_0('#skF_4', B_162)=k1_xboole_0 | r1_tarski('#skF_4', B_162))), inference(resolution, [status(thm)], [c_813, c_14])).
% 3.52/1.57  tff(c_24, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.52/1.57  tff(c_825, plain, (![B_162]: (k2_xboole_0('#skF_4', B_162)=B_162 | k3_xboole_0('#skF_4', B_162)=k1_xboole_0)), inference(resolution, [status(thm)], [c_818, c_24])).
% 3.52/1.57  tff(c_1813, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1737, c_825])).
% 3.52/1.57  tff(c_1819, plain, ('#skF_5'='#skF_4' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_500, c_1813])).
% 3.52/1.57  tff(c_1821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_498, c_517, c_1819])).
% 3.52/1.57  tff(c_1822, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 3.52/1.57  tff(c_1823, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 3.52/1.57  tff(c_18, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.57  tff(c_1826, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_18])).
% 3.52/1.57  tff(c_2006, plain, (![A_257, B_258]: (r2_hidden('#skF_2'(A_257, B_258), A_257) | r1_tarski(A_257, B_258))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.52/1.57  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.52/1.57  tff(c_2011, plain, (![A_259, B_260]: (~v1_xboole_0(A_259) | r1_tarski(A_259, B_260))), inference(resolution, [status(thm)], [c_2006, c_4])).
% 3.52/1.57  tff(c_2021, plain, (![A_261, B_262]: (k2_xboole_0(A_261, B_262)=B_262 | ~v1_xboole_0(A_261))), inference(resolution, [status(thm)], [c_2011, c_24])).
% 3.52/1.57  tff(c_2024, plain, (![B_262]: (k2_xboole_0('#skF_4', B_262)=B_262)), inference(resolution, [status(thm)], [c_1826, c_2021])).
% 3.52/1.57  tff(c_2033, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2024, c_68])).
% 3.52/1.57  tff(c_2035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1822, c_2033])).
% 3.52/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.57  
% 3.52/1.57  Inference rules
% 3.52/1.57  ----------------------
% 3.52/1.57  #Ref     : 0
% 3.52/1.57  #Sup     : 449
% 3.52/1.57  #Fact    : 0
% 3.52/1.57  #Define  : 0
% 3.52/1.57  #Split   : 3
% 3.52/1.57  #Chain   : 0
% 3.52/1.57  #Close   : 0
% 3.52/1.57  
% 3.52/1.57  Ordering : KBO
% 3.52/1.57  
% 3.52/1.57  Simplification rules
% 3.52/1.57  ----------------------
% 3.52/1.57  #Subsume      : 51
% 3.52/1.57  #Demod        : 173
% 3.52/1.57  #Tautology    : 272
% 3.52/1.57  #SimpNegUnit  : 16
% 3.52/1.57  #BackRed      : 7
% 3.52/1.57  
% 3.52/1.57  #Partial instantiations: 0
% 3.52/1.57  #Strategies tried      : 1
% 3.52/1.57  
% 3.52/1.57  Timing (in seconds)
% 3.52/1.57  ----------------------
% 3.52/1.57  Preprocessing        : 0.34
% 3.52/1.57  Parsing              : 0.18
% 3.52/1.57  CNF conversion       : 0.02
% 3.52/1.57  Main loop            : 0.48
% 3.52/1.57  Inferencing          : 0.18
% 3.52/1.57  Reduction            : 0.17
% 3.52/1.57  Demodulation         : 0.12
% 3.52/1.57  BG Simplification    : 0.02
% 3.52/1.57  Subsumption          : 0.07
% 3.52/1.57  Abstraction          : 0.02
% 3.52/1.57  MUC search           : 0.00
% 3.52/1.57  Cooper               : 0.00
% 3.52/1.57  Total                : 0.85
% 3.52/1.57  Index Insertion      : 0.00
% 3.52/1.57  Index Deletion       : 0.00
% 3.52/1.57  Index Matching       : 0.00
% 3.52/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

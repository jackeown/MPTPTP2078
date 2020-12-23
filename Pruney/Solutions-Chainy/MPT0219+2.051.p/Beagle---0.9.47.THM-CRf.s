%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:56 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 228 expanded)
%              Number of leaves         :   39 (  94 expanded)
%              Depth                    :   20
%              Number of atoms          :   72 ( 237 expanded)
%              Number of equality atoms :   56 ( 180 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_90,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ! [C_37] : r2_hidden(C_37,k1_tarski(C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_192,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(A_88,B_89) = A_88
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_197,plain,(
    ! [A_90] : k3_xboole_0(k1_xboole_0,A_90) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_192])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [A_90] : k3_xboole_0(A_90,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_2])).

tff(c_272,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_281,plain,(
    ! [A_90] : k5_xboole_0(A_90,k1_xboole_0) = k4_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_272])).

tff(c_296,plain,(
    ! [A_90] : k4_xboole_0(A_90,k1_xboole_0) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_281])).

tff(c_331,plain,(
    ! [A_98,B_99] : k4_xboole_0(k2_xboole_0(A_98,B_99),B_99) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_338,plain,(
    ! [A_98] : k4_xboole_0(A_98,k1_xboole_0) = k2_xboole_0(A_98,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_296])).

tff(c_350,plain,(
    ! [A_98] : k2_xboole_0(A_98,k1_xboole_0) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_338])).

tff(c_196,plain,(
    ! [A_15] : k3_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_192])).

tff(c_284,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_272])).

tff(c_297,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_284])).

tff(c_473,plain,(
    ! [A_110,B_111] : k2_xboole_0(k3_xboole_0(A_110,B_111),k4_xboole_0(A_110,B_111)) = A_110 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_494,plain,(
    ! [A_90] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_90,k1_xboole_0)) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_473])).

tff(c_515,plain,(
    ! [A_112] : k2_xboole_0(k1_xboole_0,A_112) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_494])).

tff(c_30,plain,(
    ! [A_16,B_17] : k4_xboole_0(k2_xboole_0(A_16,B_17),B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_525,plain,(
    ! [A_112] : k4_xboole_0(k1_xboole_0,A_112) = k4_xboole_0(A_112,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_30])).

tff(c_535,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_525])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_293,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_272])).

tff(c_555,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_293])).

tff(c_92,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_512,plain,(
    ! [A_90] : k2_xboole_0(k1_xboole_0,A_90) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_494])).

tff(c_404,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k4_xboole_0(B_108,A_107)) = k2_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_416,plain,(
    ! [A_90] : k5_xboole_0(k1_xboole_0,A_90) = k2_xboole_0(k1_xboole_0,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_404])).

tff(c_514,plain,(
    ! [A_90] : k5_xboole_0(k1_xboole_0,A_90) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_416])).

tff(c_747,plain,(
    ! [A_125,B_126,C_127] : k5_xboole_0(k5_xboole_0(A_125,B_126),C_127) = k5_xboole_0(A_125,k5_xboole_0(B_126,C_127)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_789,plain,(
    ! [A_9,C_127] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_127)) = k5_xboole_0(k1_xboole_0,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_747])).

tff(c_827,plain,(
    ! [A_128,C_129] : k5_xboole_0(A_128,k5_xboole_0(A_128,C_129)) = C_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_789])).

tff(c_1560,plain,(
    ! [A_157,B_158] : k5_xboole_0(A_157,k2_xboole_0(A_157,B_158)) = k4_xboole_0(B_158,A_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_827])).

tff(c_1618,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_1560])).

tff(c_1630,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_1618])).

tff(c_500,plain,(
    ! [B_2,A_1] : k2_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_473])).

tff(c_1634,plain,(
    k2_xboole_0(k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')),k1_xboole_0) = k1_tarski('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_500])).

tff(c_1643,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_2,c_1634])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2065,plain,(
    ! [D_169] :
      ( r2_hidden(D_169,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_169,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1643,c_6])).

tff(c_64,plain,(
    ! [C_37,A_33] :
      ( C_37 = A_33
      | ~ r2_hidden(C_37,k1_tarski(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2075,plain,(
    ! [D_170] :
      ( D_170 = '#skF_7'
      | ~ r2_hidden(D_170,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2065,c_64])).

tff(c_2079,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_66,c_2075])).

tff(c_2083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2079])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.66  
% 3.93/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.67  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 3.93/1.67  
% 3.93/1.67  %Foreground sorts:
% 3.93/1.67  
% 3.93/1.67  
% 3.93/1.67  %Background operators:
% 3.93/1.67  
% 3.93/1.67  
% 3.93/1.67  %Foreground operators:
% 3.93/1.67  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.93/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.93/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.93/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.93/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.93/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.93/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.93/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.93/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.93/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.93/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.93/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.93/1.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.93/1.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.93/1.67  tff('#skF_8', type, '#skF_8': $i).
% 3.93/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.93/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.93/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.93/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.93/1.67  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.93/1.67  
% 4.23/1.69  tff(f_97, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 4.23/1.69  tff(f_78, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.23/1.69  tff(f_52, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.23/1.69  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.23/1.69  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.23/1.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.23/1.69  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.23/1.69  tff(f_48, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.23/1.69  tff(f_50, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.23/1.69  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.23/1.69  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.23/1.69  tff(f_54, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.23/1.69  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.23/1.69  tff(c_90, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.23/1.69  tff(c_66, plain, (![C_37]: (r2_hidden(C_37, k1_tarski(C_37)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.23/1.69  tff(c_34, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.23/1.69  tff(c_28, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.23/1.69  tff(c_192, plain, (![A_88, B_89]: (k3_xboole_0(A_88, B_89)=A_88 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.23/1.69  tff(c_197, plain, (![A_90]: (k3_xboole_0(k1_xboole_0, A_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_192])).
% 4.23/1.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.23/1.69  tff(c_202, plain, (![A_90]: (k3_xboole_0(A_90, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_197, c_2])).
% 4.23/1.69  tff(c_272, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.23/1.69  tff(c_281, plain, (![A_90]: (k5_xboole_0(A_90, k1_xboole_0)=k4_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_202, c_272])).
% 4.23/1.69  tff(c_296, plain, (![A_90]: (k4_xboole_0(A_90, k1_xboole_0)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_281])).
% 4.23/1.69  tff(c_331, plain, (![A_98, B_99]: (k4_xboole_0(k2_xboole_0(A_98, B_99), B_99)=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.23/1.69  tff(c_338, plain, (![A_98]: (k4_xboole_0(A_98, k1_xboole_0)=k2_xboole_0(A_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_331, c_296])).
% 4.23/1.69  tff(c_350, plain, (![A_98]: (k2_xboole_0(A_98, k1_xboole_0)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_296, c_338])).
% 4.23/1.69  tff(c_196, plain, (![A_15]: (k3_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_192])).
% 4.23/1.69  tff(c_284, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_15))), inference(superposition, [status(thm), theory('equality')], [c_196, c_272])).
% 4.23/1.69  tff(c_297, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_284])).
% 4.23/1.69  tff(c_473, plain, (![A_110, B_111]: (k2_xboole_0(k3_xboole_0(A_110, B_111), k4_xboole_0(A_110, B_111))=A_110)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.23/1.69  tff(c_494, plain, (![A_90]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_90, k1_xboole_0))=A_90)), inference(superposition, [status(thm), theory('equality')], [c_202, c_473])).
% 4.23/1.69  tff(c_515, plain, (![A_112]: (k2_xboole_0(k1_xboole_0, A_112)=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_296, c_494])).
% 4.23/1.69  tff(c_30, plain, (![A_16, B_17]: (k4_xboole_0(k2_xboole_0(A_16, B_17), B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.23/1.69  tff(c_525, plain, (![A_112]: (k4_xboole_0(k1_xboole_0, A_112)=k4_xboole_0(A_112, A_112))), inference(superposition, [status(thm), theory('equality')], [c_515, c_30])).
% 4.23/1.69  tff(c_535, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_525])).
% 4.23/1.69  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.23/1.69  tff(c_293, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_272])).
% 4.23/1.69  tff(c_555, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_535, c_293])).
% 4.23/1.69  tff(c_92, plain, (k2_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.23/1.69  tff(c_38, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.23/1.69  tff(c_512, plain, (![A_90]: (k2_xboole_0(k1_xboole_0, A_90)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_296, c_494])).
% 4.23/1.69  tff(c_404, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k4_xboole_0(B_108, A_107))=k2_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.23/1.69  tff(c_416, plain, (![A_90]: (k5_xboole_0(k1_xboole_0, A_90)=k2_xboole_0(k1_xboole_0, A_90))), inference(superposition, [status(thm), theory('equality')], [c_296, c_404])).
% 4.23/1.69  tff(c_514, plain, (![A_90]: (k5_xboole_0(k1_xboole_0, A_90)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_512, c_416])).
% 4.23/1.69  tff(c_747, plain, (![A_125, B_126, C_127]: (k5_xboole_0(k5_xboole_0(A_125, B_126), C_127)=k5_xboole_0(A_125, k5_xboole_0(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.23/1.69  tff(c_789, plain, (![A_9, C_127]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_127))=k5_xboole_0(k1_xboole_0, C_127))), inference(superposition, [status(thm), theory('equality')], [c_555, c_747])).
% 4.23/1.69  tff(c_827, plain, (![A_128, C_129]: (k5_xboole_0(A_128, k5_xboole_0(A_128, C_129))=C_129)), inference(demodulation, [status(thm), theory('equality')], [c_514, c_789])).
% 4.23/1.69  tff(c_1560, plain, (![A_157, B_158]: (k5_xboole_0(A_157, k2_xboole_0(A_157, B_158))=k4_xboole_0(B_158, A_157))), inference(superposition, [status(thm), theory('equality')], [c_38, c_827])).
% 4.23/1.69  tff(c_1618, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_1560])).
% 4.23/1.69  tff(c_1630, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_555, c_1618])).
% 4.23/1.69  tff(c_500, plain, (![B_2, A_1]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_473])).
% 4.23/1.69  tff(c_1634, plain, (k2_xboole_0(k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8')), k1_xboole_0)=k1_tarski('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1630, c_500])).
% 4.23/1.69  tff(c_1643, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_2, c_1634])).
% 4.23/1.69  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.23/1.69  tff(c_2065, plain, (![D_169]: (r2_hidden(D_169, k1_tarski('#skF_7')) | ~r2_hidden(D_169, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1643, c_6])).
% 4.23/1.69  tff(c_64, plain, (![C_37, A_33]: (C_37=A_33 | ~r2_hidden(C_37, k1_tarski(A_33)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.23/1.69  tff(c_2075, plain, (![D_170]: (D_170='#skF_7' | ~r2_hidden(D_170, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_2065, c_64])).
% 4.23/1.69  tff(c_2079, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_66, c_2075])).
% 4.23/1.69  tff(c_2083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2079])).
% 4.23/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.69  
% 4.23/1.69  Inference rules
% 4.23/1.69  ----------------------
% 4.23/1.69  #Ref     : 0
% 4.23/1.69  #Sup     : 492
% 4.23/1.69  #Fact    : 0
% 4.23/1.69  #Define  : 0
% 4.23/1.69  #Split   : 0
% 4.23/1.69  #Chain   : 0
% 4.23/1.69  #Close   : 0
% 4.23/1.69  
% 4.23/1.69  Ordering : KBO
% 4.23/1.69  
% 4.23/1.69  Simplification rules
% 4.23/1.69  ----------------------
% 4.23/1.69  #Subsume      : 15
% 4.23/1.69  #Demod        : 327
% 4.23/1.69  #Tautology    : 340
% 4.23/1.69  #SimpNegUnit  : 1
% 4.23/1.69  #BackRed      : 4
% 4.23/1.69  
% 4.23/1.69  #Partial instantiations: 0
% 4.23/1.69  #Strategies tried      : 1
% 4.23/1.69  
% 4.23/1.69  Timing (in seconds)
% 4.23/1.69  ----------------------
% 4.23/1.70  Preprocessing        : 0.37
% 4.23/1.70  Parsing              : 0.18
% 4.23/1.70  CNF conversion       : 0.03
% 4.23/1.70  Main loop            : 0.54
% 4.23/1.70  Inferencing          : 0.18
% 4.23/1.70  Reduction            : 0.21
% 4.23/1.70  Demodulation         : 0.17
% 4.23/1.70  BG Simplification    : 0.03
% 4.23/1.70  Subsumption          : 0.08
% 4.23/1.70  Abstraction          : 0.03
% 4.23/1.70  MUC search           : 0.00
% 4.23/1.70  Cooper               : 0.00
% 4.23/1.70  Total                : 0.96
% 4.23/1.70  Index Insertion      : 0.00
% 4.23/1.70  Index Deletion       : 0.00
% 4.23/1.70  Index Matching       : 0.00
% 4.23/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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

% Result     : Theorem 3.73s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 457 expanded)
%              Number of leaves         :   39 ( 170 expanded)
%              Depth                    :   22
%              Number of atoms          :   73 ( 507 expanded)
%              Number of equality atoms :   54 ( 379 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_56,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    ! [C_38] : r2_hidden(C_38,k1_tarski(C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_9] : k2_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_200,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(A_91,B_92) = A_91
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_338,plain,(
    ! [A_113,B_114] : k3_xboole_0(k4_xboole_0(A_113,B_114),A_113) = k4_xboole_0(A_113,B_114) ),
    inference(resolution,[status(thm)],[c_30,c_200])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_221,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k4_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_230,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_221])).

tff(c_549,plain,(
    ! [A_127,B_128] : k5_xboole_0(A_127,k4_xboole_0(A_127,B_128)) = k4_xboole_0(A_127,k4_xboole_0(A_127,B_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_230])).

tff(c_38,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_567,plain,(
    ! [B_128] : k4_xboole_0(B_128,k4_xboole_0(B_128,B_128)) = k2_xboole_0(B_128,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_38])).

tff(c_587,plain,(
    ! [B_129] : k4_xboole_0(B_129,k4_xboole_0(B_129,B_129)) = B_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_567])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k4_xboole_0(B_20,A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_608,plain,(
    ! [B_129] :
      ( k4_xboole_0(B_129,B_129) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(B_129,B_129),B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_32])).

tff(c_623,plain,(
    ! [B_129] : k4_xboole_0(B_129,B_129) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_608])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_236,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k4_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_221])).

tff(c_635,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_236])).

tff(c_92,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_583,plain,(
    ! [B_128] : k4_xboole_0(B_128,k4_xboole_0(B_128,B_128)) = B_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_567])).

tff(c_703,plain,(
    ! [B_136] : k4_xboole_0(B_136,k1_xboole_0) = B_136 ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_583])).

tff(c_725,plain,(
    ! [B_136] : k5_xboole_0(k1_xboole_0,B_136) = k2_xboole_0(k1_xboole_0,B_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_38])).

tff(c_750,plain,(
    ! [A_137] : k5_xboole_0(A_137,A_137) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_236])).

tff(c_36,plain,(
    ! [A_22,B_23,C_24] : k5_xboole_0(k5_xboole_0(A_22,B_23),C_24) = k5_xboole_0(A_22,k5_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_763,plain,(
    ! [A_137,C_24] : k5_xboole_0(A_137,k5_xboole_0(A_137,C_24)) = k5_xboole_0(k1_xboole_0,C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_36])).

tff(c_1314,plain,(
    ! [A_173,C_174] : k5_xboole_0(A_173,k5_xboole_0(A_173,C_174)) = k2_xboole_0(k1_xboole_0,C_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_763])).

tff(c_1350,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_1314])).

tff(c_1380,plain,(
    ! [A_11] : k2_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1350])).

tff(c_1313,plain,(
    ! [A_137,C_24] : k5_xboole_0(A_137,k5_xboole_0(A_137,C_24)) = k2_xboole_0(k1_xboole_0,C_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_763])).

tff(c_1546,plain,(
    ! [A_180,C_181] : k5_xboole_0(A_180,k5_xboole_0(A_180,C_181)) = C_181 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1313])).

tff(c_2391,plain,(
    ! [A_219,B_220] : k5_xboole_0(A_219,k2_xboole_0(A_219,B_220)) = k4_xboole_0(B_220,A_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1546])).

tff(c_2440,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2391])).

tff(c_2451,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_2440])).

tff(c_26,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1595,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1546])).

tff(c_2456,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k5_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2451,c_1595])).

tff(c_2480,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2456])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2699,plain,(
    ! [D_229] :
      ( r2_hidden(D_229,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_229,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_6])).

tff(c_64,plain,(
    ! [C_38,A_34] :
      ( C_38 = A_34
      | ~ r2_hidden(C_38,k1_tarski(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2986,plain,(
    ! [D_242] :
      ( D_242 = '#skF_7'
      | ~ r2_hidden(D_242,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2699,c_64])).

tff(c_3018,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_66,c_2986])).

tff(c_3029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_3018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n020.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % DateTime   : Tue Dec  1 14:49:37 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.70  
% 4.04/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.71  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 4.04/1.71  
% 4.04/1.71  %Foreground sorts:
% 4.04/1.71  
% 4.04/1.71  
% 4.04/1.71  %Background operators:
% 4.04/1.71  
% 4.04/1.71  
% 4.04/1.71  %Foreground operators:
% 4.04/1.71  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.04/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.04/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.04/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.04/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.04/1.71  tff('#skF_7', type, '#skF_7': $i).
% 4.04/1.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.04/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.04/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.04/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.04/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.04/1.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.04/1.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.71  tff('#skF_8', type, '#skF_8': $i).
% 4.04/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.04/1.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.04/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.04/1.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.71  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.04/1.71  
% 4.04/1.72  tff(f_99, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 4.04/1.72  tff(f_80, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.04/1.72  tff(f_54, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.04/1.72  tff(f_48, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.04/1.72  tff(f_38, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.04/1.72  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.04/1.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.04/1.72  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.04/1.72  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.04/1.72  tff(f_52, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.04/1.72  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.04/1.72  tff(f_56, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.04/1.72  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.04/1.72  tff(c_90, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.04/1.72  tff(c_66, plain, (![C_38]: (r2_hidden(C_38, k1_tarski(C_38)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.04/1.72  tff(c_34, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.04/1.72  tff(c_30, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.04/1.72  tff(c_22, plain, (![A_9]: (k2_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.04/1.72  tff(c_200, plain, (![A_91, B_92]: (k3_xboole_0(A_91, B_92)=A_91 | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.04/1.72  tff(c_338, plain, (![A_113, B_114]: (k3_xboole_0(k4_xboole_0(A_113, B_114), A_113)=k4_xboole_0(A_113, B_114))), inference(resolution, [status(thm)], [c_30, c_200])).
% 4.04/1.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/1.72  tff(c_221, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k4_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.04/1.72  tff(c_230, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_221])).
% 4.04/1.72  tff(c_549, plain, (![A_127, B_128]: (k5_xboole_0(A_127, k4_xboole_0(A_127, B_128))=k4_xboole_0(A_127, k4_xboole_0(A_127, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_338, c_230])).
% 4.04/1.72  tff(c_38, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.04/1.72  tff(c_567, plain, (![B_128]: (k4_xboole_0(B_128, k4_xboole_0(B_128, B_128))=k2_xboole_0(B_128, B_128))), inference(superposition, [status(thm), theory('equality')], [c_549, c_38])).
% 4.04/1.72  tff(c_587, plain, (![B_129]: (k4_xboole_0(B_129, k4_xboole_0(B_129, B_129))=B_129)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_567])).
% 4.04/1.72  tff(c_32, plain, (![A_19, B_20]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k4_xboole_0(B_20, A_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.04/1.72  tff(c_608, plain, (![B_129]: (k4_xboole_0(B_129, B_129)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(B_129, B_129), B_129))), inference(superposition, [status(thm), theory('equality')], [c_587, c_32])).
% 4.04/1.72  tff(c_623, plain, (![B_129]: (k4_xboole_0(B_129, B_129)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_608])).
% 4.04/1.72  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.04/1.72  tff(c_236, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k4_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_24, c_221])).
% 4.04/1.72  tff(c_635, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_623, c_236])).
% 4.04/1.72  tff(c_92, plain, (k2_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.04/1.72  tff(c_583, plain, (![B_128]: (k4_xboole_0(B_128, k4_xboole_0(B_128, B_128))=B_128)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_567])).
% 4.04/1.72  tff(c_703, plain, (![B_136]: (k4_xboole_0(B_136, k1_xboole_0)=B_136)), inference(demodulation, [status(thm), theory('equality')], [c_623, c_583])).
% 4.04/1.72  tff(c_725, plain, (![B_136]: (k5_xboole_0(k1_xboole_0, B_136)=k2_xboole_0(k1_xboole_0, B_136))), inference(superposition, [status(thm), theory('equality')], [c_703, c_38])).
% 4.04/1.72  tff(c_750, plain, (![A_137]: (k5_xboole_0(A_137, A_137)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_623, c_236])).
% 4.04/1.72  tff(c_36, plain, (![A_22, B_23, C_24]: (k5_xboole_0(k5_xboole_0(A_22, B_23), C_24)=k5_xboole_0(A_22, k5_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.04/1.72  tff(c_763, plain, (![A_137, C_24]: (k5_xboole_0(A_137, k5_xboole_0(A_137, C_24))=k5_xboole_0(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_750, c_36])).
% 4.04/1.72  tff(c_1314, plain, (![A_173, C_174]: (k5_xboole_0(A_173, k5_xboole_0(A_173, C_174))=k2_xboole_0(k1_xboole_0, C_174))), inference(demodulation, [status(thm), theory('equality')], [c_725, c_763])).
% 4.04/1.72  tff(c_1350, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_635, c_1314])).
% 4.04/1.72  tff(c_1380, plain, (![A_11]: (k2_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1350])).
% 4.04/1.72  tff(c_1313, plain, (![A_137, C_24]: (k5_xboole_0(A_137, k5_xboole_0(A_137, C_24))=k2_xboole_0(k1_xboole_0, C_24))), inference(demodulation, [status(thm), theory('equality')], [c_725, c_763])).
% 4.04/1.72  tff(c_1546, plain, (![A_180, C_181]: (k5_xboole_0(A_180, k5_xboole_0(A_180, C_181))=C_181)), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1313])).
% 4.04/1.72  tff(c_2391, plain, (![A_219, B_220]: (k5_xboole_0(A_219, k2_xboole_0(A_219, B_220))=k4_xboole_0(B_220, A_219))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1546])).
% 4.04/1.72  tff(c_2440, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2391])).
% 4.04/1.72  tff(c_2451, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_635, c_2440])).
% 4.04/1.72  tff(c_26, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.04/1.72  tff(c_1595, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1546])).
% 4.04/1.72  tff(c_2456, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k5_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2451, c_1595])).
% 4.04/1.72  tff(c_2480, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2456])).
% 4.04/1.72  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.04/1.72  tff(c_2699, plain, (![D_229]: (r2_hidden(D_229, k1_tarski('#skF_7')) | ~r2_hidden(D_229, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2480, c_6])).
% 4.04/1.72  tff(c_64, plain, (![C_38, A_34]: (C_38=A_34 | ~r2_hidden(C_38, k1_tarski(A_34)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.04/1.72  tff(c_2986, plain, (![D_242]: (D_242='#skF_7' | ~r2_hidden(D_242, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_2699, c_64])).
% 4.04/1.72  tff(c_3018, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_66, c_2986])).
% 4.04/1.72  tff(c_3029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_3018])).
% 4.04/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.72  
% 4.04/1.72  Inference rules
% 4.04/1.72  ----------------------
% 4.04/1.72  #Ref     : 0
% 4.04/1.72  #Sup     : 694
% 4.04/1.72  #Fact    : 0
% 4.04/1.72  #Define  : 0
% 4.04/1.72  #Split   : 0
% 4.04/1.72  #Chain   : 0
% 4.04/1.72  #Close   : 0
% 4.04/1.72  
% 4.04/1.72  Ordering : KBO
% 4.04/1.72  
% 4.04/1.72  Simplification rules
% 4.04/1.72  ----------------------
% 4.04/1.72  #Subsume      : 18
% 4.04/1.72  #Demod        : 463
% 4.04/1.72  #Tautology    : 460
% 4.04/1.72  #SimpNegUnit  : 1
% 4.04/1.72  #BackRed      : 10
% 4.04/1.72  
% 4.04/1.72  #Partial instantiations: 0
% 4.04/1.72  #Strategies tried      : 1
% 4.04/1.72  
% 4.04/1.72  Timing (in seconds)
% 4.04/1.72  ----------------------
% 4.04/1.72  Preprocessing        : 0.46
% 4.04/1.72  Parsing              : 0.24
% 4.04/1.72  CNF conversion       : 0.03
% 4.04/1.72  Main loop            : 0.59
% 4.04/1.72  Inferencing          : 0.21
% 4.04/1.72  Reduction            : 0.22
% 4.04/1.72  Demodulation         : 0.17
% 4.04/1.72  BG Simplification    : 0.03
% 4.04/1.72  Subsumption          : 0.10
% 4.04/1.72  Abstraction          : 0.03
% 4.04/1.73  MUC search           : 0.00
% 4.04/1.73  Cooper               : 0.00
% 4.04/1.73  Total                : 1.09
% 4.04/1.73  Index Insertion      : 0.00
% 4.04/1.73  Index Deletion       : 0.00
% 4.04/1.73  Index Matching       : 0.00
% 4.04/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------

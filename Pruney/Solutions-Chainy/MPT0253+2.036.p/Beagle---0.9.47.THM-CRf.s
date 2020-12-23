%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:18 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 406 expanded)
%              Number of leaves         :   31 ( 150 expanded)
%              Depth                    :   17
%              Number of atoms          :   73 ( 492 expanded)
%              Number of equality atoms :   48 ( 357 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(c_48,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_869,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_tarski(k2_tarski(A_105,B_106),C_107)
      | ~ r2_hidden(B_106,C_107)
      | ~ r2_hidden(A_105,C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2127,plain,(
    ! [A_158,B_159,C_160] :
      ( k4_xboole_0(k2_tarski(A_158,B_159),C_160) = k1_xboole_0
      | ~ r2_hidden(B_159,C_160)
      | ~ r2_hidden(A_158,C_160) ) ),
    inference(resolution,[status(thm)],[c_869,c_14])).

tff(c_22,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2155,plain,(
    ! [C_160,A_158,B_159] :
      ( k2_xboole_0(C_160,k2_tarski(A_158,B_159)) = k5_xboole_0(C_160,k1_xboole_0)
      | ~ r2_hidden(B_159,C_160)
      | ~ r2_hidden(A_158,C_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2127,c_22])).

tff(c_2178,plain,(
    ! [C_160,A_158,B_159] :
      ( k2_xboole_0(C_160,k2_tarski(A_158,B_159)) = C_160
      | ~ r2_hidden(B_159,C_160)
      | ~ r2_hidden(A_158,C_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2155])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_137,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_146,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_137])).

tff(c_16,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_277,plain,(
    ! [A_89,B_90,C_91] : k5_xboole_0(k5_xboole_0(A_89,B_90),C_91) = k5_xboole_0(A_89,k5_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3291,plain,(
    ! [A_182,B_183,C_184] : k5_xboole_0(A_182,k5_xboole_0(k3_xboole_0(A_182,B_183),C_184)) = k5_xboole_0(k4_xboole_0(A_182,B_183),C_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_277])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_111])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_152,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_137])).

tff(c_155,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_152])).

tff(c_295,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k5_xboole_0(B_90,k5_xboole_0(A_89,B_90))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_155])).

tff(c_666,plain,(
    ! [A_102,C_103] : k5_xboole_0(A_102,k5_xboole_0(A_102,C_103)) = k5_xboole_0(k1_xboole_0,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_277])).

tff(c_756,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = k5_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_666])).

tff(c_785,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_756])).

tff(c_326,plain,(
    ! [A_3,C_91] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_277])).

tff(c_885,plain,(
    ! [A_108,C_109] : k5_xboole_0(A_108,k5_xboole_0(A_108,C_109)) = C_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_326])).

tff(c_929,plain,(
    ! [B_90,A_89] : k5_xboole_0(B_90,k5_xboole_0(A_89,B_90)) = k5_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_885])).

tff(c_968,plain,(
    ! [B_90,A_89] : k5_xboole_0(B_90,k5_xboole_0(A_89,B_90)) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_929])).

tff(c_3460,plain,(
    ! [C_185,B_186] : k5_xboole_0(k4_xboole_0(C_185,B_186),C_185) = k3_xboole_0(C_185,B_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_3291,c_968])).

tff(c_319,plain,(
    ! [A_15,B_16,C_91] : k5_xboole_0(A_15,k5_xboole_0(k4_xboole_0(B_16,A_15),C_91)) = k5_xboole_0(k2_xboole_0(A_15,B_16),C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_277])).

tff(c_3466,plain,(
    ! [B_186,C_185] : k5_xboole_0(k2_xboole_0(B_186,C_185),C_185) = k5_xboole_0(B_186,k3_xboole_0(C_185,B_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3460,c_319])).

tff(c_5773,plain,(
    ! [B_217,C_218] : k5_xboole_0(k2_xboole_0(B_217,C_218),C_218) = k4_xboole_0(B_217,C_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_3466])).

tff(c_787,plain,(
    ! [A_3,C_91] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_326])).

tff(c_1044,plain,(
    ! [B_117,A_118] : k5_xboole_0(B_117,k5_xboole_0(A_118,B_117)) = A_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_929])).

tff(c_1077,plain,(
    ! [A_3,C_91] : k5_xboole_0(k5_xboole_0(A_3,C_91),C_91) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_1044])).

tff(c_7710,plain,(
    ! [B_235,C_236] : k5_xboole_0(k4_xboole_0(B_235,C_236),C_236) = k2_xboole_0(B_235,C_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_5773,c_1077])).

tff(c_2572,plain,(
    ! [A_168,B_169,C_170] : k5_xboole_0(A_168,k5_xboole_0(k4_xboole_0(B_169,A_168),C_170)) = k5_xboole_0(k2_xboole_0(A_168,B_169),C_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_277])).

tff(c_3030,plain,(
    ! [B_177,B_178] : k5_xboole_0(k2_xboole_0(B_177,B_178),B_177) = k4_xboole_0(B_178,B_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_2572])).

tff(c_3045,plain,(
    ! [B_178,B_177] : k5_xboole_0(k4_xboole_0(B_178,B_177),B_177) = k2_xboole_0(B_177,B_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_3030,c_1077])).

tff(c_7727,plain,(
    ! [C_236,B_235] : k2_xboole_0(C_236,B_235) = k2_xboole_0(B_235,C_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_7710,c_3045])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7844,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7727,c_44])).

tff(c_8108,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2178,c_7844])).

tff(c_8112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_8108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:10:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.47/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.40  
% 6.52/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.41  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.52/2.41  
% 6.52/2.41  %Foreground sorts:
% 6.52/2.41  
% 6.52/2.41  
% 6.52/2.41  %Background operators:
% 6.52/2.41  
% 6.52/2.41  
% 6.52/2.41  %Foreground operators:
% 6.52/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.52/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.52/2.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.52/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.52/2.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.52/2.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.52/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.52/2.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.52/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.52/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.52/2.41  tff('#skF_2', type, '#skF_2': $i).
% 6.52/2.41  tff('#skF_3', type, '#skF_3': $i).
% 6.52/2.41  tff('#skF_1', type, '#skF_1': $i).
% 6.52/2.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.52/2.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.52/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.52/2.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.52/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.52/2.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.52/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.52/2.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.52/2.41  
% 6.52/2.42  tff(f_74, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 6.52/2.42  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.52/2.42  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.52/2.42  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.52/2.42  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.52/2.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.52/2.42  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.52/2.42  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.52/2.42  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.52/2.42  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.52/2.42  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.52/2.42  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.52/2.42  tff(c_18, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.52/2.42  tff(c_869, plain, (![A_105, B_106, C_107]: (r1_tarski(k2_tarski(A_105, B_106), C_107) | ~r2_hidden(B_106, C_107) | ~r2_hidden(A_105, C_107))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.52/2.42  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.52/2.42  tff(c_2127, plain, (![A_158, B_159, C_160]: (k4_xboole_0(k2_tarski(A_158, B_159), C_160)=k1_xboole_0 | ~r2_hidden(B_159, C_160) | ~r2_hidden(A_158, C_160))), inference(resolution, [status(thm)], [c_869, c_14])).
% 6.52/2.42  tff(c_22, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.52/2.42  tff(c_2155, plain, (![C_160, A_158, B_159]: (k2_xboole_0(C_160, k2_tarski(A_158, B_159))=k5_xboole_0(C_160, k1_xboole_0) | ~r2_hidden(B_159, C_160) | ~r2_hidden(A_158, C_160))), inference(superposition, [status(thm), theory('equality')], [c_2127, c_22])).
% 6.52/2.42  tff(c_2178, plain, (![C_160, A_158, B_159]: (k2_xboole_0(C_160, k2_tarski(A_158, B_159))=C_160 | ~r2_hidden(B_159, C_160) | ~r2_hidden(A_158, C_160))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2155])).
% 6.52/2.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.52/2.42  tff(c_137, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.52/2.42  tff(c_146, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_137])).
% 6.52/2.42  tff(c_16, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.52/2.42  tff(c_277, plain, (![A_89, B_90, C_91]: (k5_xboole_0(k5_xboole_0(A_89, B_90), C_91)=k5_xboole_0(A_89, k5_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.52/2.42  tff(c_3291, plain, (![A_182, B_183, C_184]: (k5_xboole_0(A_182, k5_xboole_0(k3_xboole_0(A_182, B_183), C_184))=k5_xboole_0(k4_xboole_0(A_182, B_183), C_184))), inference(superposition, [status(thm), theory('equality')], [c_16, c_277])).
% 6.52/2.42  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.52/2.42  tff(c_111, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.52/2.42  tff(c_115, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_111])).
% 6.52/2.42  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.52/2.42  tff(c_152, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_137])).
% 6.52/2.42  tff(c_155, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_152])).
% 6.52/2.42  tff(c_295, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k5_xboole_0(B_90, k5_xboole_0(A_89, B_90)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_277, c_155])).
% 6.52/2.42  tff(c_666, plain, (![A_102, C_103]: (k5_xboole_0(A_102, k5_xboole_0(A_102, C_103))=k5_xboole_0(k1_xboole_0, C_103))), inference(superposition, [status(thm), theory('equality')], [c_155, c_277])).
% 6.52/2.42  tff(c_756, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=k5_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_155, c_666])).
% 6.52/2.42  tff(c_785, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_756])).
% 6.52/2.42  tff(c_326, plain, (![A_3, C_91]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_155, c_277])).
% 6.52/2.42  tff(c_885, plain, (![A_108, C_109]: (k5_xboole_0(A_108, k5_xboole_0(A_108, C_109))=C_109)), inference(demodulation, [status(thm), theory('equality')], [c_785, c_326])).
% 6.52/2.42  tff(c_929, plain, (![B_90, A_89]: (k5_xboole_0(B_90, k5_xboole_0(A_89, B_90))=k5_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_295, c_885])).
% 6.52/2.42  tff(c_968, plain, (![B_90, A_89]: (k5_xboole_0(B_90, k5_xboole_0(A_89, B_90))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_929])).
% 6.52/2.42  tff(c_3460, plain, (![C_185, B_186]: (k5_xboole_0(k4_xboole_0(C_185, B_186), C_185)=k3_xboole_0(C_185, B_186))), inference(superposition, [status(thm), theory('equality')], [c_3291, c_968])).
% 6.52/2.42  tff(c_319, plain, (![A_15, B_16, C_91]: (k5_xboole_0(A_15, k5_xboole_0(k4_xboole_0(B_16, A_15), C_91))=k5_xboole_0(k2_xboole_0(A_15, B_16), C_91))), inference(superposition, [status(thm), theory('equality')], [c_22, c_277])).
% 6.52/2.42  tff(c_3466, plain, (![B_186, C_185]: (k5_xboole_0(k2_xboole_0(B_186, C_185), C_185)=k5_xboole_0(B_186, k3_xboole_0(C_185, B_186)))), inference(superposition, [status(thm), theory('equality')], [c_3460, c_319])).
% 6.52/2.42  tff(c_5773, plain, (![B_217, C_218]: (k5_xboole_0(k2_xboole_0(B_217, C_218), C_218)=k4_xboole_0(B_217, C_218))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_3466])).
% 6.52/2.42  tff(c_787, plain, (![A_3, C_91]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_785, c_326])).
% 6.52/2.42  tff(c_1044, plain, (![B_117, A_118]: (k5_xboole_0(B_117, k5_xboole_0(A_118, B_117))=A_118)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_929])).
% 6.52/2.42  tff(c_1077, plain, (![A_3, C_91]: (k5_xboole_0(k5_xboole_0(A_3, C_91), C_91)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_787, c_1044])).
% 6.52/2.42  tff(c_7710, plain, (![B_235, C_236]: (k5_xboole_0(k4_xboole_0(B_235, C_236), C_236)=k2_xboole_0(B_235, C_236))), inference(superposition, [status(thm), theory('equality')], [c_5773, c_1077])).
% 6.52/2.42  tff(c_2572, plain, (![A_168, B_169, C_170]: (k5_xboole_0(A_168, k5_xboole_0(k4_xboole_0(B_169, A_168), C_170))=k5_xboole_0(k2_xboole_0(A_168, B_169), C_170))), inference(superposition, [status(thm), theory('equality')], [c_22, c_277])).
% 6.52/2.42  tff(c_3030, plain, (![B_177, B_178]: (k5_xboole_0(k2_xboole_0(B_177, B_178), B_177)=k4_xboole_0(B_178, B_177))), inference(superposition, [status(thm), theory('equality')], [c_968, c_2572])).
% 6.52/2.42  tff(c_3045, plain, (![B_178, B_177]: (k5_xboole_0(k4_xboole_0(B_178, B_177), B_177)=k2_xboole_0(B_177, B_178))), inference(superposition, [status(thm), theory('equality')], [c_3030, c_1077])).
% 6.52/2.42  tff(c_7727, plain, (![C_236, B_235]: (k2_xboole_0(C_236, B_235)=k2_xboole_0(B_235, C_236))), inference(superposition, [status(thm), theory('equality')], [c_7710, c_3045])).
% 6.52/2.42  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.52/2.42  tff(c_7844, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7727, c_44])).
% 6.52/2.42  tff(c_8108, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2178, c_7844])).
% 6.52/2.42  tff(c_8112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_8108])).
% 6.52/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.42  
% 6.52/2.42  Inference rules
% 6.52/2.42  ----------------------
% 6.52/2.42  #Ref     : 0
% 6.52/2.42  #Sup     : 1910
% 6.52/2.42  #Fact    : 0
% 6.52/2.42  #Define  : 0
% 6.52/2.42  #Split   : 0
% 6.52/2.42  #Chain   : 0
% 6.52/2.42  #Close   : 0
% 6.52/2.42  
% 6.52/2.42  Ordering : KBO
% 6.52/2.42  
% 6.52/2.42  Simplification rules
% 6.52/2.42  ----------------------
% 6.52/2.42  #Subsume      : 46
% 6.52/2.42  #Demod        : 1799
% 6.52/2.42  #Tautology    : 1140
% 6.52/2.42  #SimpNegUnit  : 0
% 6.52/2.42  #BackRed      : 5
% 6.52/2.42  
% 6.52/2.42  #Partial instantiations: 0
% 6.52/2.42  #Strategies tried      : 1
% 6.52/2.42  
% 6.52/2.42  Timing (in seconds)
% 6.52/2.42  ----------------------
% 6.52/2.42  Preprocessing        : 0.34
% 6.52/2.42  Parsing              : 0.18
% 6.52/2.42  CNF conversion       : 0.02
% 6.52/2.43  Main loop            : 1.26
% 6.52/2.43  Inferencing          : 0.36
% 6.52/2.43  Reduction            : 0.61
% 6.52/2.43  Demodulation         : 0.52
% 6.52/2.43  BG Simplification    : 0.05
% 6.52/2.43  Subsumption          : 0.18
% 6.52/2.43  Abstraction          : 0.07
% 6.52/2.43  MUC search           : 0.00
% 6.52/2.43  Cooper               : 0.00
% 6.52/2.43  Total                : 1.63
% 6.52/2.43  Index Insertion      : 0.00
% 6.52/2.43  Index Deletion       : 0.00
% 6.52/2.43  Index Matching       : 0.00
% 6.52/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

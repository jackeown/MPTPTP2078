%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:10 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 131 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 232 expanded)
%              Number of equality atoms :   67 ( 201 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_60,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_132,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_133,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_134,plain,(
    ! [A_72,B_73] : r1_tarski(A_72,k2_xboole_0(A_72,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_137,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_134])).

tff(c_2004,plain,(
    ! [B_157,A_158] :
      ( k1_tarski(B_157) = A_158
      | k1_xboole_0 = A_158
      | ~ r1_tarski(A_158,k1_tarski(B_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2037,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_137,c_2004])).

tff(c_2051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_133,c_2037])).

tff(c_2052,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2053,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2070,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_2053,c_62])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2082,plain,(
    ! [B_163,A_164] : k5_xboole_0(B_163,A_164) = k5_xboole_0(A_164,B_163) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2098,plain,(
    ! [A_164] : k5_xboole_0(k1_xboole_0,A_164) = A_164 ),
    inference(superposition,[status(thm),theory(equality)],[c_2082,c_28])).

tff(c_34,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4309,plain,(
    ! [A_253,B_254,C_255] : k5_xboole_0(k5_xboole_0(A_253,B_254),C_255) = k5_xboole_0(A_253,k5_xboole_0(B_254,C_255)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4373,plain,(
    ! [A_32,C_255] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_255)) = k5_xboole_0(k1_xboole_0,C_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4309])).

tff(c_4387,plain,(
    ! [A_256,C_257] : k5_xboole_0(A_256,k5_xboole_0(A_256,C_257)) = C_257 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_4373])).

tff(c_4430,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4387])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2054,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_64])).

tff(c_4817,plain,(
    ! [A_266,B_267] : k4_xboole_0(k2_xboole_0(A_266,B_267),k3_xboole_0(A_266,B_267)) = k5_xboole_0(A_266,B_267) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4874,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2054,c_4817])).

tff(c_4885,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) = k5_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_4874])).

tff(c_26,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2951,plain,(
    ! [A_205,B_206] :
      ( k2_xboole_0(A_205,B_206) = B_206
      | ~ r1_tarski(A_205,B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2997,plain,(
    ! [A_24,B_25] : k2_xboole_0(k4_xboole_0(A_24,B_25),A_24) = A_24 ),
    inference(resolution,[status(thm)],[c_26,c_2951])).

tff(c_4968,plain,(
    k2_xboole_0(k5_xboole_0('#skF_3','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4885,c_2997])).

tff(c_5073,plain,(
    ! [A_274,B_275] : r1_tarski(k5_xboole_0(A_274,B_275),k2_xboole_0(A_274,B_275)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4817,c_26])).

tff(c_5085,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0('#skF_3','#skF_2'),'#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4968,c_5073])).

tff(c_5140,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4430,c_4,c_5085])).

tff(c_4157,plain,(
    ! [B_246,A_247] :
      ( k1_tarski(B_246) = A_247
      | k1_xboole_0 = A_247
      | ~ r1_tarski(A_247,k1_tarski(B_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4184,plain,(
    ! [A_247] :
      ( k1_tarski('#skF_1') = A_247
      | k1_xboole_0 = A_247
      | ~ r1_tarski(A_247,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2053,c_4157])).

tff(c_4192,plain,(
    ! [A_247] :
      ( A_247 = '#skF_2'
      | k1_xboole_0 = A_247
      | ~ r1_tarski(A_247,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_4184])).

tff(c_5151,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5140,c_4192])).

tff(c_5164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2052,c_2070,c_5151])).

tff(c_5165,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_5599,plain,(
    ! [A_309,B_310] :
      ( k2_xboole_0(A_309,B_310) = B_310
      | ~ r1_tarski(A_309,B_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5636,plain,(
    ! [A_311,B_312] : k2_xboole_0(k4_xboole_0(A_311,B_312),A_311) = A_311 ),
    inference(resolution,[status(thm)],[c_26,c_5599])).

tff(c_5166,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_24,plain,(
    ! [A_23] : k3_xboole_0(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5167,plain,(
    ! [A_23] : k3_xboole_0(A_23,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5166,c_5166,c_24])).

tff(c_5503,plain,(
    ! [A_298,B_299,C_300] : r1_tarski(k3_xboole_0(A_298,B_299),k2_xboole_0(A_298,C_300)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5524,plain,(
    ! [A_23,C_300] : r1_tarski('#skF_2',k2_xboole_0(A_23,C_300)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5167,c_5503])).

tff(c_5660,plain,(
    ! [A_313] : r1_tarski('#skF_2',A_313) ),
    inference(superposition,[status(thm),theory(equality)],[c_5636,c_5524])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5667,plain,(
    ! [A_313] : k2_xboole_0('#skF_2',A_313) = A_313 ),
    inference(resolution,[status(thm)],[c_5660,c_16])).

tff(c_5700,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5667,c_64])).

tff(c_5702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5165,c_5700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:48:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.17  
% 5.29/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.17  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.29/2.17  
% 5.29/2.17  %Foreground sorts:
% 5.29/2.17  
% 5.29/2.17  
% 5.29/2.17  %Background operators:
% 5.29/2.17  
% 5.29/2.17  
% 5.29/2.17  %Foreground operators:
% 5.29/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/2.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.29/2.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.29/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.29/2.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.29/2.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.29/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/2.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.29/2.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.29/2.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.29/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.29/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.29/2.17  tff('#skF_1', type, '#skF_1': $i).
% 5.29/2.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.29/2.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.29/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/2.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.29/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/2.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.29/2.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.29/2.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.29/2.17  
% 5.29/2.19  tff(f_106, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.29/2.19  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.29/2.19  tff(f_85, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.29/2.19  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.29/2.19  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.29/2.19  tff(f_65, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.29/2.19  tff(f_63, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.29/2.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.29/2.19  tff(f_37, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 5.29/2.19  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.29/2.19  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.29/2.19  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.29/2.19  tff(f_53, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 5.29/2.19  tff(c_60, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.29/2.19  tff(c_132, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_60])).
% 5.29/2.19  tff(c_58, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.29/2.19  tff(c_133, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 5.29/2.19  tff(c_64, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.29/2.19  tff(c_134, plain, (![A_72, B_73]: (r1_tarski(A_72, k2_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.29/2.19  tff(c_137, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_134])).
% 5.29/2.19  tff(c_2004, plain, (![B_157, A_158]: (k1_tarski(B_157)=A_158 | k1_xboole_0=A_158 | ~r1_tarski(A_158, k1_tarski(B_157)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.29/2.19  tff(c_2037, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_137, c_2004])).
% 5.29/2.19  tff(c_2051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_133, c_2037])).
% 5.29/2.19  tff(c_2052, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_58])).
% 5.29/2.19  tff(c_2053, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 5.29/2.19  tff(c_62, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.29/2.19  tff(c_2070, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_2053, c_62])).
% 5.29/2.19  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.29/2.19  tff(c_2082, plain, (![B_163, A_164]: (k5_xboole_0(B_163, A_164)=k5_xboole_0(A_164, B_163))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.29/2.19  tff(c_28, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.29/2.19  tff(c_2098, plain, (![A_164]: (k5_xboole_0(k1_xboole_0, A_164)=A_164)), inference(superposition, [status(thm), theory('equality')], [c_2082, c_28])).
% 5.29/2.19  tff(c_34, plain, (![A_32]: (k5_xboole_0(A_32, A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.29/2.19  tff(c_4309, plain, (![A_253, B_254, C_255]: (k5_xboole_0(k5_xboole_0(A_253, B_254), C_255)=k5_xboole_0(A_253, k5_xboole_0(B_254, C_255)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.29/2.19  tff(c_4373, plain, (![A_32, C_255]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_255))=k5_xboole_0(k1_xboole_0, C_255))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4309])).
% 5.29/2.19  tff(c_4387, plain, (![A_256, C_257]: (k5_xboole_0(A_256, k5_xboole_0(A_256, C_257))=C_257)), inference(demodulation, [status(thm), theory('equality')], [c_2098, c_4373])).
% 5.29/2.19  tff(c_4430, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_4387])).
% 5.29/2.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.29/2.19  tff(c_2054, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_64])).
% 5.29/2.19  tff(c_4817, plain, (![A_266, B_267]: (k4_xboole_0(k2_xboole_0(A_266, B_267), k3_xboole_0(A_266, B_267))=k5_xboole_0(A_266, B_267))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.29/2.19  tff(c_4874, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2054, c_4817])).
% 5.29/2.19  tff(c_4885, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))=k5_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_4874])).
% 5.29/2.19  tff(c_26, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.29/2.19  tff(c_2951, plain, (![A_205, B_206]: (k2_xboole_0(A_205, B_206)=B_206 | ~r1_tarski(A_205, B_206))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.29/2.19  tff(c_2997, plain, (![A_24, B_25]: (k2_xboole_0(k4_xboole_0(A_24, B_25), A_24)=A_24)), inference(resolution, [status(thm)], [c_26, c_2951])).
% 5.29/2.19  tff(c_4968, plain, (k2_xboole_0(k5_xboole_0('#skF_3', '#skF_2'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4885, c_2997])).
% 5.29/2.19  tff(c_5073, plain, (![A_274, B_275]: (r1_tarski(k5_xboole_0(A_274, B_275), k2_xboole_0(A_274, B_275)))), inference(superposition, [status(thm), theory('equality')], [c_4817, c_26])).
% 5.29/2.19  tff(c_5085, plain, (r1_tarski(k5_xboole_0(k5_xboole_0('#skF_3', '#skF_2'), '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4968, c_5073])).
% 5.29/2.19  tff(c_5140, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4430, c_4, c_5085])).
% 5.29/2.19  tff(c_4157, plain, (![B_246, A_247]: (k1_tarski(B_246)=A_247 | k1_xboole_0=A_247 | ~r1_tarski(A_247, k1_tarski(B_246)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.29/2.19  tff(c_4184, plain, (![A_247]: (k1_tarski('#skF_1')=A_247 | k1_xboole_0=A_247 | ~r1_tarski(A_247, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2053, c_4157])).
% 5.29/2.19  tff(c_4192, plain, (![A_247]: (A_247='#skF_2' | k1_xboole_0=A_247 | ~r1_tarski(A_247, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_4184])).
% 5.29/2.19  tff(c_5151, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5140, c_4192])).
% 5.29/2.19  tff(c_5164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2052, c_2070, c_5151])).
% 5.29/2.19  tff(c_5165, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_60])).
% 5.29/2.19  tff(c_5599, plain, (![A_309, B_310]: (k2_xboole_0(A_309, B_310)=B_310 | ~r1_tarski(A_309, B_310))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.29/2.19  tff(c_5636, plain, (![A_311, B_312]: (k2_xboole_0(k4_xboole_0(A_311, B_312), A_311)=A_311)), inference(resolution, [status(thm)], [c_26, c_5599])).
% 5.29/2.19  tff(c_5166, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_60])).
% 5.29/2.19  tff(c_24, plain, (![A_23]: (k3_xboole_0(A_23, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.29/2.19  tff(c_5167, plain, (![A_23]: (k3_xboole_0(A_23, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5166, c_5166, c_24])).
% 5.29/2.19  tff(c_5503, plain, (![A_298, B_299, C_300]: (r1_tarski(k3_xboole_0(A_298, B_299), k2_xboole_0(A_298, C_300)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.29/2.19  tff(c_5524, plain, (![A_23, C_300]: (r1_tarski('#skF_2', k2_xboole_0(A_23, C_300)))), inference(superposition, [status(thm), theory('equality')], [c_5167, c_5503])).
% 5.29/2.19  tff(c_5660, plain, (![A_313]: (r1_tarski('#skF_2', A_313))), inference(superposition, [status(thm), theory('equality')], [c_5636, c_5524])).
% 5.29/2.19  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.29/2.19  tff(c_5667, plain, (![A_313]: (k2_xboole_0('#skF_2', A_313)=A_313)), inference(resolution, [status(thm)], [c_5660, c_16])).
% 5.29/2.19  tff(c_5700, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5667, c_64])).
% 5.29/2.19  tff(c_5702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5165, c_5700])).
% 5.29/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.19  
% 5.29/2.19  Inference rules
% 5.29/2.19  ----------------------
% 5.29/2.19  #Ref     : 1
% 5.29/2.19  #Sup     : 1368
% 5.29/2.19  #Fact    : 0
% 5.29/2.19  #Define  : 0
% 5.29/2.19  #Split   : 3
% 5.29/2.19  #Chain   : 0
% 5.29/2.19  #Close   : 0
% 5.29/2.19  
% 5.29/2.19  Ordering : KBO
% 5.29/2.19  
% 5.29/2.19  Simplification rules
% 5.29/2.19  ----------------------
% 5.29/2.19  #Subsume      : 47
% 5.29/2.19  #Demod        : 717
% 5.29/2.19  #Tautology    : 1030
% 5.29/2.19  #SimpNegUnit  : 6
% 5.29/2.19  #BackRed      : 21
% 5.29/2.19  
% 5.29/2.19  #Partial instantiations: 0
% 5.29/2.19  #Strategies tried      : 1
% 5.29/2.19  
% 5.29/2.19  Timing (in seconds)
% 5.29/2.19  ----------------------
% 5.29/2.19  Preprocessing        : 0.40
% 5.29/2.19  Parsing              : 0.19
% 5.29/2.19  CNF conversion       : 0.03
% 5.29/2.19  Main loop            : 0.96
% 5.29/2.19  Inferencing          : 0.33
% 5.29/2.19  Reduction            : 0.38
% 5.29/2.19  Demodulation         : 0.29
% 5.29/2.19  BG Simplification    : 0.05
% 5.29/2.19  Subsumption          : 0.13
% 5.29/2.19  Abstraction          : 0.04
% 5.29/2.19  MUC search           : 0.00
% 5.29/2.19  Cooper               : 0.00
% 5.29/2.19  Total                : 1.40
% 5.29/2.19  Index Insertion      : 0.00
% 5.29/2.19  Index Deletion       : 0.00
% 5.29/2.19  Index Matching       : 0.00
% 5.29/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

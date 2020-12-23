%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:14 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 146 expanded)
%              Number of leaves         :   39 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 266 expanded)
%              Number of equality atoms :   71 ( 221 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_68,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_80,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_76,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_142,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_74,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_143,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_144,plain,(
    ! [A_93,B_94] : r1_tarski(A_93,k2_xboole_0(A_93,B_94)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_147,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_144])).

tff(c_826,plain,(
    ! [B_169,A_170] :
      ( k1_tarski(B_169) = A_170
      | k1_xboole_0 = A_170
      | ~ r1_tarski(A_170,k1_tarski(B_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_841,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_147,c_826])).

tff(c_854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_143,c_841])).

tff(c_855,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_856,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_973,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_856,c_78])).

tff(c_857,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_80])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_877,plain,(
    ! [B_173,A_174] : k5_xboole_0(B_173,A_174) = k5_xboole_0(A_174,B_173) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_893,plain,(
    ! [A_174] : k5_xboole_0(k1_xboole_0,A_174) = A_174 ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_30])).

tff(c_38,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2577,plain,(
    ! [A_289,B_290,C_291] : k5_xboole_0(k5_xboole_0(A_289,B_290),C_291) = k5_xboole_0(A_289,k5_xboole_0(B_290,C_291)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2630,plain,(
    ! [A_32,C_291] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_291)) = k5_xboole_0(k1_xboole_0,C_291) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2577])).

tff(c_2688,plain,(
    ! [A_293,C_294] : k5_xboole_0(A_293,k5_xboole_0(A_293,C_294)) = C_294 ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_2630])).

tff(c_2781,plain,(
    ! [A_297,B_298] : k5_xboole_0(A_297,k5_xboole_0(B_298,A_297)) = B_298 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2688])).

tff(c_2728,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2688])).

tff(c_2784,plain,(
    ! [B_298,A_297] : k5_xboole_0(k5_xboole_0(B_298,A_297),B_298) = A_297 ),
    inference(superposition,[status(thm),theory(equality)],[c_2781,c_2728])).

tff(c_3232,plain,(
    ! [A_310,B_311] : k5_xboole_0(k5_xboole_0(A_310,B_311),k2_xboole_0(A_310,B_311)) = k3_xboole_0(A_310,B_311) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3317,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_3232])).

tff(c_3334,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_3317])).

tff(c_1100,plain,(
    ! [A_194,B_195] :
      ( r1_xboole_0(k1_tarski(A_194),B_195)
      | r2_hidden(A_194,B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1566,plain,(
    ! [A_241,B_242] :
      ( k3_xboole_0(k1_tarski(A_241),B_242) = k1_xboole_0
      | r2_hidden(A_241,B_242) ) ),
    inference(resolution,[status(thm)],[c_1100,c_10])).

tff(c_1596,plain,(
    ! [B_243] :
      ( k3_xboole_0('#skF_4',B_243) = k1_xboole_0
      | r2_hidden('#skF_3',B_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_1566])).

tff(c_62,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_tarski(A_78),B_79)
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1025,plain,(
    ! [A_188,B_189] :
      ( k2_xboole_0(A_188,B_189) = B_189
      | ~ r1_tarski(A_188,B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1456,plain,(
    ! [A_234,B_235] :
      ( k2_xboole_0(k1_tarski(A_234),B_235) = B_235
      | ~ r2_hidden(A_234,B_235) ) ),
    inference(resolution,[status(thm)],[c_62,c_1025])).

tff(c_1484,plain,(
    ! [B_235] :
      ( k2_xboole_0('#skF_4',B_235) = B_235
      | ~ r2_hidden('#skF_3',B_235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_1456])).

tff(c_1613,plain,(
    ! [B_243] :
      ( k2_xboole_0('#skF_4',B_243) = B_243
      | k3_xboole_0('#skF_4',B_243) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1596,c_1484])).

tff(c_3343,plain,
    ( k2_xboole_0('#skF_4','#skF_5') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3334,c_1613])).

tff(c_3367,plain,
    ( '#skF_5' = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_3343])).

tff(c_3369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_855,c_973,c_3367])).

tff(c_3370,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3371,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k3_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3606,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k3_xboole_0(A_8,B_9) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3371,c_12])).

tff(c_3629,plain,(
    ! [A_345,B_346,C_347] :
      ( ~ r1_xboole_0(A_345,B_346)
      | ~ r2_hidden(C_347,k3_xboole_0(A_345,B_346)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3638,plain,(
    ! [A_348,C_349] :
      ( ~ r1_xboole_0(A_348,A_348)
      | ~ r2_hidden(C_349,A_348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3629])).

tff(c_3641,plain,(
    ! [C_349,B_9] :
      ( ~ r2_hidden(C_349,B_9)
      | k3_xboole_0(B_9,B_9) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_3606,c_3638])).

tff(c_3650,plain,(
    ! [C_350,B_351] :
      ( ~ r2_hidden(C_350,B_351)
      | B_351 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3641])).

tff(c_3673,plain,(
    ! [A_355,B_356] :
      ( A_355 != '#skF_4'
      | r1_tarski(A_355,B_356) ) ),
    inference(resolution,[status(thm)],[c_8,c_3650])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3691,plain,(
    ! [B_356] : k2_xboole_0('#skF_4',B_356) = B_356 ),
    inference(resolution,[status(thm)],[c_3673,c_28])).

tff(c_3693,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3691,c_80])).

tff(c_3695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3370,c_3693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:51:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.28/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.87  
% 4.28/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.88  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.28/1.88  
% 4.28/1.88  %Foreground sorts:
% 4.28/1.88  
% 4.28/1.88  
% 4.28/1.88  %Background operators:
% 4.28/1.88  
% 4.28/1.88  
% 4.28/1.88  %Foreground operators:
% 4.28/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.28/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.28/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.28/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.28/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.28/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.28/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.28/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.28/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.28/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.28/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.28/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.28/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.28/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.88  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.28/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.28/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.28/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.28/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.28/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.28/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.28/1.88  
% 4.28/1.89  tff(f_136, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.28/1.89  tff(f_76, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.28/1.89  tff(f_115, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.28/1.89  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.28/1.89  tff(f_68, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.28/1.89  tff(f_80, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.28/1.89  tff(f_78, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.28/1.89  tff(f_82, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.28/1.89  tff(f_109, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.28/1.89  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.28/1.89  tff(f_104, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.28/1.89  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.28/1.89  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.28/1.89  tff(f_42, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.28/1.89  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.28/1.89  tff(c_76, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.28/1.89  tff(c_142, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_76])).
% 4.28/1.89  tff(c_74, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.28/1.89  tff(c_143, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_74])).
% 4.28/1.89  tff(c_80, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.28/1.89  tff(c_144, plain, (![A_93, B_94]: (r1_tarski(A_93, k2_xboole_0(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.28/1.89  tff(c_147, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_144])).
% 4.28/1.89  tff(c_826, plain, (![B_169, A_170]: (k1_tarski(B_169)=A_170 | k1_xboole_0=A_170 | ~r1_tarski(A_170, k1_tarski(B_169)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.28/1.89  tff(c_841, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_147, c_826])).
% 4.28/1.89  tff(c_854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_143, c_841])).
% 4.28/1.89  tff(c_855, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_74])).
% 4.28/1.89  tff(c_856, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_74])).
% 4.28/1.89  tff(c_78, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.28/1.89  tff(c_973, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_856, c_856, c_78])).
% 4.28/1.89  tff(c_857, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_856, c_80])).
% 4.28/1.89  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.28/1.89  tff(c_877, plain, (![B_173, A_174]: (k5_xboole_0(B_173, A_174)=k5_xboole_0(A_174, B_173))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.28/1.89  tff(c_30, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.28/1.89  tff(c_893, plain, (![A_174]: (k5_xboole_0(k1_xboole_0, A_174)=A_174)), inference(superposition, [status(thm), theory('equality')], [c_877, c_30])).
% 4.28/1.89  tff(c_38, plain, (![A_32]: (k5_xboole_0(A_32, A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.28/1.89  tff(c_2577, plain, (![A_289, B_290, C_291]: (k5_xboole_0(k5_xboole_0(A_289, B_290), C_291)=k5_xboole_0(A_289, k5_xboole_0(B_290, C_291)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.28/1.89  tff(c_2630, plain, (![A_32, C_291]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_291))=k5_xboole_0(k1_xboole_0, C_291))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2577])).
% 4.28/1.89  tff(c_2688, plain, (![A_293, C_294]: (k5_xboole_0(A_293, k5_xboole_0(A_293, C_294))=C_294)), inference(demodulation, [status(thm), theory('equality')], [c_893, c_2630])).
% 4.28/1.89  tff(c_2781, plain, (![A_297, B_298]: (k5_xboole_0(A_297, k5_xboole_0(B_298, A_297))=B_298)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2688])).
% 4.28/1.89  tff(c_2728, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2688])).
% 4.28/1.89  tff(c_2784, plain, (![B_298, A_297]: (k5_xboole_0(k5_xboole_0(B_298, A_297), B_298)=A_297)), inference(superposition, [status(thm), theory('equality')], [c_2781, c_2728])).
% 4.28/1.89  tff(c_3232, plain, (![A_310, B_311]: (k5_xboole_0(k5_xboole_0(A_310, B_311), k2_xboole_0(A_310, B_311))=k3_xboole_0(A_310, B_311))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.28/1.89  tff(c_3317, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_857, c_3232])).
% 4.28/1.89  tff(c_3334, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2784, c_3317])).
% 4.28/1.89  tff(c_1100, plain, (![A_194, B_195]: (r1_xboole_0(k1_tarski(A_194), B_195) | r2_hidden(A_194, B_195))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.28/1.89  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.28/1.89  tff(c_1566, plain, (![A_241, B_242]: (k3_xboole_0(k1_tarski(A_241), B_242)=k1_xboole_0 | r2_hidden(A_241, B_242))), inference(resolution, [status(thm)], [c_1100, c_10])).
% 4.28/1.89  tff(c_1596, plain, (![B_243]: (k3_xboole_0('#skF_4', B_243)=k1_xboole_0 | r2_hidden('#skF_3', B_243))), inference(superposition, [status(thm), theory('equality')], [c_856, c_1566])).
% 4.28/1.89  tff(c_62, plain, (![A_78, B_79]: (r1_tarski(k1_tarski(A_78), B_79) | ~r2_hidden(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.28/1.89  tff(c_1025, plain, (![A_188, B_189]: (k2_xboole_0(A_188, B_189)=B_189 | ~r1_tarski(A_188, B_189))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.28/1.89  tff(c_1456, plain, (![A_234, B_235]: (k2_xboole_0(k1_tarski(A_234), B_235)=B_235 | ~r2_hidden(A_234, B_235))), inference(resolution, [status(thm)], [c_62, c_1025])).
% 4.28/1.89  tff(c_1484, plain, (![B_235]: (k2_xboole_0('#skF_4', B_235)=B_235 | ~r2_hidden('#skF_3', B_235))), inference(superposition, [status(thm), theory('equality')], [c_856, c_1456])).
% 4.28/1.89  tff(c_1613, plain, (![B_243]: (k2_xboole_0('#skF_4', B_243)=B_243 | k3_xboole_0('#skF_4', B_243)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1596, c_1484])).
% 4.28/1.89  tff(c_3343, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3334, c_1613])).
% 4.28/1.89  tff(c_3367, plain, ('#skF_5'='#skF_4' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_857, c_3343])).
% 4.28/1.89  tff(c_3369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_855, c_973, c_3367])).
% 4.28/1.89  tff(c_3370, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_76])).
% 4.28/1.89  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.28/1.89  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.28/1.89  tff(c_3371, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_76])).
% 4.28/1.89  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k3_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.28/1.89  tff(c_3606, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k3_xboole_0(A_8, B_9)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3371, c_12])).
% 4.28/1.89  tff(c_3629, plain, (![A_345, B_346, C_347]: (~r1_xboole_0(A_345, B_346) | ~r2_hidden(C_347, k3_xboole_0(A_345, B_346)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.28/1.89  tff(c_3638, plain, (![A_348, C_349]: (~r1_xboole_0(A_348, A_348) | ~r2_hidden(C_349, A_348))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3629])).
% 4.28/1.89  tff(c_3641, plain, (![C_349, B_9]: (~r2_hidden(C_349, B_9) | k3_xboole_0(B_9, B_9)!='#skF_4')), inference(resolution, [status(thm)], [c_3606, c_3638])).
% 4.28/1.89  tff(c_3650, plain, (![C_350, B_351]: (~r2_hidden(C_350, B_351) | B_351!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3641])).
% 4.28/1.89  tff(c_3673, plain, (![A_355, B_356]: (A_355!='#skF_4' | r1_tarski(A_355, B_356))), inference(resolution, [status(thm)], [c_8, c_3650])).
% 4.28/1.89  tff(c_28, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.28/1.89  tff(c_3691, plain, (![B_356]: (k2_xboole_0('#skF_4', B_356)=B_356)), inference(resolution, [status(thm)], [c_3673, c_28])).
% 4.28/1.89  tff(c_3693, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3691, c_80])).
% 4.28/1.89  tff(c_3695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3370, c_3693])).
% 4.28/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.89  
% 4.28/1.89  Inference rules
% 4.28/1.89  ----------------------
% 4.28/1.89  #Ref     : 2
% 4.28/1.89  #Sup     : 833
% 4.28/1.89  #Fact    : 0
% 4.28/1.89  #Define  : 0
% 4.28/1.89  #Split   : 4
% 4.28/1.89  #Chain   : 0
% 4.28/1.89  #Close   : 0
% 4.28/1.89  
% 4.28/1.89  Ordering : KBO
% 4.28/1.89  
% 4.28/1.89  Simplification rules
% 4.28/1.89  ----------------------
% 4.28/1.89  #Subsume      : 196
% 4.28/1.89  #Demod        : 314
% 4.28/1.89  #Tautology    : 419
% 4.28/1.89  #SimpNegUnit  : 50
% 4.28/1.89  #BackRed      : 14
% 4.28/1.89  
% 4.28/1.89  #Partial instantiations: 0
% 4.28/1.89  #Strategies tried      : 1
% 4.28/1.89  
% 4.28/1.89  Timing (in seconds)
% 4.28/1.89  ----------------------
% 4.28/1.89  Preprocessing        : 0.37
% 4.28/1.89  Parsing              : 0.20
% 4.28/1.89  CNF conversion       : 0.03
% 4.28/1.89  Main loop            : 0.66
% 4.28/1.89  Inferencing          : 0.22
% 4.28/1.89  Reduction            : 0.24
% 4.28/1.89  Demodulation         : 0.17
% 4.28/1.89  BG Simplification    : 0.03
% 4.28/1.89  Subsumption          : 0.12
% 4.28/1.89  Abstraction          : 0.03
% 4.28/1.90  MUC search           : 0.00
% 4.28/1.90  Cooper               : 0.00
% 4.28/1.90  Total                : 1.06
% 4.28/1.90  Index Insertion      : 0.00
% 4.28/1.90  Index Deletion       : 0.00
% 4.28/1.90  Index Matching       : 0.00
% 4.28/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------

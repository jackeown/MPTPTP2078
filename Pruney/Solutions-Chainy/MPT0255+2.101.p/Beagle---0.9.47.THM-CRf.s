%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:52 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 202 expanded)
%              Number of leaves         :   37 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :   75 ( 191 expanded)
%              Number of equality atoms :   59 ( 175 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_231,plain,(
    ! [A_86,B_87] : k1_enumset1(A_86,A_86,B_87) = k2_tarski(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [E_31,A_25,C_27] : r2_hidden(E_31,k1_enumset1(A_25,E_31,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_243,plain,(
    ! [A_86,B_87] : r2_hidden(A_86,k2_tarski(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_32])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_331,plain,(
    ! [A_97,B_98,C_99] :
      ( ~ r1_xboole_0(A_97,B_98)
      | ~ r2_hidden(C_99,k3_xboole_0(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_346,plain,(
    ! [A_101,C_102] :
      ( ~ r1_xboole_0(A_101,A_101)
      | ~ r2_hidden(C_102,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_331])).

tff(c_352,plain,(
    ! [C_102,B_4] :
      ( ~ r2_hidden(C_102,B_4)
      | k3_xboole_0(B_4,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_346])).

tff(c_537,plain,(
    ! [C_113,B_114] :
      ( ~ r2_hidden(C_113,B_114)
      | k1_xboole_0 != B_114 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_352])).

tff(c_553,plain,(
    ! [A_86,B_87] : k2_tarski(A_86,B_87) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_243,c_537])).

tff(c_66,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_559,plain,(
    ! [A_117,B_118] : k5_xboole_0(k5_xboole_0(A_117,B_118),k3_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6142,plain,(
    ! [A_13268,B_13269] : k5_xboole_0(k3_xboole_0(A_13268,B_13269),k5_xboole_0(A_13268,B_13269)) = k2_xboole_0(A_13268,B_13269) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_559])).

tff(c_713,plain,(
    ! [A_127,B_128,C_129] : k5_xboole_0(k5_xboole_0(A_127,B_128),C_129) = k5_xboole_0(A_127,k5_xboole_0(B_128,C_129)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_780,plain,(
    ! [B_2,A_127,B_128] : k5_xboole_0(B_2,k5_xboole_0(A_127,B_128)) = k5_xboole_0(A_127,k5_xboole_0(B_128,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_713])).

tff(c_6172,plain,(
    ! [B_13269,A_13268] : k5_xboole_0(B_13269,k5_xboole_0(k3_xboole_0(A_13268,B_13269),A_13268)) = k2_xboole_0(A_13268,B_13269) ),
    inference(superposition,[status(thm),theory(equality)],[c_6142,c_780])).

tff(c_6331,plain,(
    ! [B_13432,A_13433] : k5_xboole_0(B_13432,k4_xboole_0(A_13433,B_13432)) = k2_xboole_0(A_13433,B_13432) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_6172])).

tff(c_110,plain,(
    ! [B_75,A_76] : k5_xboole_0(B_75,A_76) = k5_xboole_0(A_76,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_126,plain,(
    ! [A_76] : k5_xboole_0(k1_xboole_0,A_76) = A_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_20])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_250,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_273,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_250])).

tff(c_277,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_273])).

tff(c_356,plain,(
    ! [A_103,B_104] : k4_xboole_0(A_103,k4_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_377,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_356])).

tff(c_380,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_377])).

tff(c_270,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_250])).

tff(c_381,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_270])).

tff(c_759,plain,(
    ! [A_5,C_129] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_129)) = k5_xboole_0(k1_xboole_0,C_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_713])).

tff(c_800,plain,(
    ! [A_5,C_129] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_129)) = C_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_759])).

tff(c_6631,plain,(
    ! [B_13924,A_13925] : k5_xboole_0(B_13924,k2_xboole_0(A_13925,B_13924)) = k4_xboole_0(A_13925,B_13924) ),
    inference(superposition,[status(thm),theory(equality)],[c_6331,c_800])).

tff(c_6725,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6631])).

tff(c_6744,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6725])).

tff(c_806,plain,(
    ! [A_130,C_131] : k5_xboole_0(A_130,k5_xboole_0(A_130,C_131)) = C_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_759])).

tff(c_886,plain,(
    ! [A_136,B_137] : k5_xboole_0(A_136,k5_xboole_0(B_137,A_136)) = B_137 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_806])).

tff(c_922,plain,(
    ! [A_5,C_129] : k5_xboole_0(k5_xboole_0(A_5,C_129),C_129) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_886])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1444,plain,(
    ! [A_172,B_173] : k5_xboole_0(A_172,k4_xboole_0(A_172,B_173)) = k3_xboole_0(A_172,B_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_806])).

tff(c_1492,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1444])).

tff(c_1662,plain,(
    ! [A_182,B_183] : k3_xboole_0(A_182,k4_xboole_0(A_182,B_183)) = k4_xboole_0(A_182,B_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1492])).

tff(c_26,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1683,plain,(
    ! [A_182,B_183] : k5_xboole_0(k5_xboole_0(A_182,k4_xboole_0(A_182,B_183)),k4_xboole_0(A_182,B_183)) = k2_xboole_0(A_182,k4_xboole_0(A_182,B_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1662,c_26])).

tff(c_1721,plain,(
    ! [A_182,B_183] : k2_xboole_0(A_182,k4_xboole_0(A_182,B_183)) = A_182 ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_1683])).

tff(c_6773,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6744,c_1721])).

tff(c_6812,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6773])).

tff(c_6814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_553,c_6812])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:52:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.22  
% 5.90/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.22  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 5.90/2.22  
% 5.90/2.22  %Foreground sorts:
% 5.90/2.22  
% 5.90/2.22  
% 5.90/2.22  %Background operators:
% 5.90/2.22  
% 5.90/2.22  
% 5.90/2.22  %Foreground operators:
% 5.90/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.90/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.90/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.90/2.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.90/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.90/2.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.90/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.90/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.90/2.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.90/2.22  tff('#skF_6', type, '#skF_6': $i).
% 5.90/2.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.90/2.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.90/2.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.90/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.90/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.90/2.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.90/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.90/2.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.90/2.22  
% 5.90/2.24  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.90/2.24  tff(f_76, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.90/2.24  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.90/2.24  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.90/2.24  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.90/2.24  tff(f_94, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 5.90/2.24  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.90/2.24  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.90/2.24  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.90/2.24  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.90/2.24  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.90/2.24  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.90/2.24  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.90/2.24  tff(c_231, plain, (![A_86, B_87]: (k1_enumset1(A_86, A_86, B_87)=k2_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.90/2.24  tff(c_32, plain, (![E_31, A_25, C_27]: (r2_hidden(E_31, k1_enumset1(A_25, E_31, C_27)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.90/2.24  tff(c_243, plain, (![A_86, B_87]: (r2_hidden(A_86, k2_tarski(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_231, c_32])).
% 5.90/2.24  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.90/2.24  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.90/2.24  tff(c_331, plain, (![A_97, B_98, C_99]: (~r1_xboole_0(A_97, B_98) | ~r2_hidden(C_99, k3_xboole_0(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.90/2.24  tff(c_346, plain, (![A_101, C_102]: (~r1_xboole_0(A_101, A_101) | ~r2_hidden(C_102, A_101))), inference(superposition, [status(thm), theory('equality')], [c_8, c_331])).
% 5.90/2.24  tff(c_352, plain, (![C_102, B_4]: (~r2_hidden(C_102, B_4) | k3_xboole_0(B_4, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_346])).
% 5.90/2.24  tff(c_537, plain, (![C_113, B_114]: (~r2_hidden(C_113, B_114) | k1_xboole_0!=B_114)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_352])).
% 5.90/2.24  tff(c_553, plain, (![A_86, B_87]: (k2_tarski(A_86, B_87)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_243, c_537])).
% 5.90/2.24  tff(c_66, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.90/2.24  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.90/2.24  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.90/2.24  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.90/2.24  tff(c_559, plain, (![A_117, B_118]: (k5_xboole_0(k5_xboole_0(A_117, B_118), k3_xboole_0(A_117, B_118))=k2_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.90/2.24  tff(c_6142, plain, (![A_13268, B_13269]: (k5_xboole_0(k3_xboole_0(A_13268, B_13269), k5_xboole_0(A_13268, B_13269))=k2_xboole_0(A_13268, B_13269))), inference(superposition, [status(thm), theory('equality')], [c_2, c_559])).
% 5.90/2.24  tff(c_713, plain, (![A_127, B_128, C_129]: (k5_xboole_0(k5_xboole_0(A_127, B_128), C_129)=k5_xboole_0(A_127, k5_xboole_0(B_128, C_129)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.90/2.24  tff(c_780, plain, (![B_2, A_127, B_128]: (k5_xboole_0(B_2, k5_xboole_0(A_127, B_128))=k5_xboole_0(A_127, k5_xboole_0(B_128, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_713])).
% 5.90/2.24  tff(c_6172, plain, (![B_13269, A_13268]: (k5_xboole_0(B_13269, k5_xboole_0(k3_xboole_0(A_13268, B_13269), A_13268))=k2_xboole_0(A_13268, B_13269))), inference(superposition, [status(thm), theory('equality')], [c_6142, c_780])).
% 5.90/2.24  tff(c_6331, plain, (![B_13432, A_13433]: (k5_xboole_0(B_13432, k4_xboole_0(A_13433, B_13432))=k2_xboole_0(A_13433, B_13432))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_6172])).
% 5.90/2.24  tff(c_110, plain, (![B_75, A_76]: (k5_xboole_0(B_75, A_76)=k5_xboole_0(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.90/2.24  tff(c_126, plain, (![A_76]: (k5_xboole_0(k1_xboole_0, A_76)=A_76)), inference(superposition, [status(thm), theory('equality')], [c_110, c_20])).
% 5.90/2.24  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.90/2.24  tff(c_250, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.90/2.24  tff(c_273, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_250])).
% 5.90/2.24  tff(c_277, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_273])).
% 5.90/2.24  tff(c_356, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k4_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.90/2.24  tff(c_377, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_277, c_356])).
% 5.90/2.24  tff(c_380, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_377])).
% 5.90/2.24  tff(c_270, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_250])).
% 5.90/2.24  tff(c_381, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_380, c_270])).
% 5.90/2.24  tff(c_759, plain, (![A_5, C_129]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_129))=k5_xboole_0(k1_xboole_0, C_129))), inference(superposition, [status(thm), theory('equality')], [c_381, c_713])).
% 5.90/2.24  tff(c_800, plain, (![A_5, C_129]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_129))=C_129)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_759])).
% 5.90/2.24  tff(c_6631, plain, (![B_13924, A_13925]: (k5_xboole_0(B_13924, k2_xboole_0(A_13925, B_13924))=k4_xboole_0(A_13925, B_13924))), inference(superposition, [status(thm), theory('equality')], [c_6331, c_800])).
% 5.90/2.24  tff(c_6725, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_66, c_6631])).
% 5.90/2.24  tff(c_6744, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6725])).
% 5.90/2.24  tff(c_806, plain, (![A_130, C_131]: (k5_xboole_0(A_130, k5_xboole_0(A_130, C_131))=C_131)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_759])).
% 5.90/2.24  tff(c_886, plain, (![A_136, B_137]: (k5_xboole_0(A_136, k5_xboole_0(B_137, A_136))=B_137)), inference(superposition, [status(thm), theory('equality')], [c_2, c_806])).
% 5.90/2.24  tff(c_922, plain, (![A_5, C_129]: (k5_xboole_0(k5_xboole_0(A_5, C_129), C_129)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_800, c_886])).
% 5.90/2.24  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.90/2.24  tff(c_1444, plain, (![A_172, B_173]: (k5_xboole_0(A_172, k4_xboole_0(A_172, B_173))=k3_xboole_0(A_172, B_173))), inference(superposition, [status(thm), theory('equality')], [c_14, c_806])).
% 5.90/2.24  tff(c_1492, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k4_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1444])).
% 5.90/2.24  tff(c_1662, plain, (![A_182, B_183]: (k3_xboole_0(A_182, k4_xboole_0(A_182, B_183))=k4_xboole_0(A_182, B_183))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1492])).
% 5.90/2.24  tff(c_26, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.90/2.24  tff(c_1683, plain, (![A_182, B_183]: (k5_xboole_0(k5_xboole_0(A_182, k4_xboole_0(A_182, B_183)), k4_xboole_0(A_182, B_183))=k2_xboole_0(A_182, k4_xboole_0(A_182, B_183)))), inference(superposition, [status(thm), theory('equality')], [c_1662, c_26])).
% 5.90/2.24  tff(c_1721, plain, (![A_182, B_183]: (k2_xboole_0(A_182, k4_xboole_0(A_182, B_183))=A_182)), inference(demodulation, [status(thm), theory('equality')], [c_922, c_1683])).
% 5.90/2.24  tff(c_6773, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6744, c_1721])).
% 5.90/2.24  tff(c_6812, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6773])).
% 5.90/2.24  tff(c_6814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_553, c_6812])).
% 5.90/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.24  
% 5.90/2.24  Inference rules
% 5.90/2.24  ----------------------
% 5.90/2.24  #Ref     : 0
% 5.90/2.24  #Sup     : 1267
% 5.90/2.24  #Fact    : 18
% 5.90/2.24  #Define  : 0
% 5.90/2.24  #Split   : 0
% 5.90/2.24  #Chain   : 0
% 5.90/2.24  #Close   : 0
% 5.90/2.24  
% 5.90/2.24  Ordering : KBO
% 5.90/2.24  
% 5.90/2.24  Simplification rules
% 5.90/2.24  ----------------------
% 5.90/2.24  #Subsume      : 117
% 5.90/2.24  #Demod        : 1036
% 5.90/2.24  #Tautology    : 695
% 5.90/2.24  #SimpNegUnit  : 19
% 5.90/2.24  #BackRed      : 1
% 5.90/2.24  
% 5.90/2.24  #Partial instantiations: 4902
% 5.90/2.24  #Strategies tried      : 1
% 5.90/2.24  
% 5.90/2.24  Timing (in seconds)
% 5.90/2.24  ----------------------
% 5.90/2.24  Preprocessing        : 0.34
% 5.90/2.24  Parsing              : 0.17
% 5.90/2.24  CNF conversion       : 0.03
% 5.90/2.24  Main loop            : 1.12
% 5.90/2.24  Inferencing          : 0.52
% 6.19/2.24  Reduction            : 0.39
% 6.19/2.24  Demodulation         : 0.33
% 6.19/2.24  BG Simplification    : 0.04
% 6.19/2.24  Subsumption          : 0.12
% 6.19/2.24  Abstraction          : 0.07
% 6.19/2.24  MUC search           : 0.00
% 6.19/2.24  Cooper               : 0.00
% 6.19/2.24  Total                : 1.49
% 6.19/2.24  Index Insertion      : 0.00
% 6.19/2.24  Index Deletion       : 0.00
% 6.19/2.24  Index Matching       : 0.00
% 6.19/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

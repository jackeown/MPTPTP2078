%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:14 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 203 expanded)
%              Number of leaves         :   34 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 341 expanded)
%              Number of equality atoms :   75 ( 322 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_103,axiom,(
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

tff(f_72,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_68,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_126,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_66,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_127,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_145,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_30])).

tff(c_448,plain,(
    ! [B_119,A_120] :
      ( k1_tarski(B_119) = A_120
      | k1_xboole_0 = A_120
      | ~ r1_tarski(A_120,k1_tarski(B_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_463,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_145,c_448])).

tff(c_479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_127,c_463])).

tff(c_480,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_481,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_70,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_592,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_481,c_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_544,plain,(
    ! [B_126,A_127] : k5_xboole_0(B_126,A_127) = k5_xboole_0(A_127,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_560,plain,(
    ! [A_127] : k5_xboole_0(k1_xboole_0,A_127) = A_127 ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_28])).

tff(c_34,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1519,plain,(
    ! [A_209,B_210,C_211] : k5_xboole_0(k5_xboole_0(A_209,B_210),C_211) = k5_xboole_0(A_209,k5_xboole_0(B_210,C_211)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1572,plain,(
    ! [A_28,C_211] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_211)) = k5_xboole_0(k1_xboole_0,C_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1519])).

tff(c_1586,plain,(
    ! [A_212,C_213] : k5_xboole_0(A_212,k5_xboole_0(A_212,C_213)) = C_213 ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_1572])).

tff(c_1648,plain,(
    ! [A_214,B_215] : k5_xboole_0(A_214,k5_xboole_0(B_215,A_214)) = B_215 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1586])).

tff(c_1626,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1586])).

tff(c_1651,plain,(
    ! [B_215,A_214] : k5_xboole_0(k5_xboole_0(B_215,A_214),B_215) = A_214 ),
    inference(superposition,[status(thm),theory(equality)],[c_1648,c_1626])).

tff(c_488,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_72])).

tff(c_1959,plain,(
    ! [A_222,B_223] : k5_xboole_0(k5_xboole_0(A_222,B_223),k2_xboole_0(A_222,B_223)) = k3_xboole_0(A_222,B_223) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2032,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_1959])).

tff(c_2045,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1651,c_2032])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1161,plain,(
    ! [B_191,A_192] :
      ( k1_tarski(B_191) = A_192
      | k1_xboole_0 = A_192
      | ~ r1_tarski(A_192,k1_tarski(B_191)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1180,plain,(
    ! [A_192] :
      ( k1_tarski('#skF_3') = A_192
      | k1_xboole_0 = A_192
      | ~ r1_tarski(A_192,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_1161])).

tff(c_1200,plain,(
    ! [A_193] :
      ( A_193 = '#skF_4'
      | k1_xboole_0 = A_193
      | ~ r1_tarski(A_193,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_1180])).

tff(c_1235,plain,(
    ! [B_20] :
      ( k3_xboole_0('#skF_4',B_20) = '#skF_4'
      | k3_xboole_0('#skF_4',B_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_1200])).

tff(c_2054,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2045,c_1235])).

tff(c_2080,plain,
    ( '#skF_5' = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2045,c_2054])).

tff(c_2082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_480,c_592,c_2080])).

tff(c_2083,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2084,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2086,plain,(
    ! [A_22] : k5_xboole_0(A_22,'#skF_4') = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_28])).

tff(c_2177,plain,(
    ! [B_232,A_233] : k5_xboole_0(B_232,A_233) = k5_xboole_0(A_233,B_232) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2193,plain,(
    ! [A_233] : k5_xboole_0('#skF_4',A_233) = A_233 ),
    inference(superposition,[status(thm),theory(equality)],[c_2177,c_2086])).

tff(c_26,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2136,plain,(
    ! [A_230] :
      ( A_230 = '#skF_4'
      | ~ r1_tarski(A_230,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_2084,c_26])).

tff(c_2145,plain,(
    ! [B_20] : k3_xboole_0('#skF_4',B_20) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_2136])).

tff(c_2503,plain,(
    ! [A_280,B_281] : k5_xboole_0(k5_xboole_0(A_280,B_281),k2_xboole_0(A_280,B_281)) = k3_xboole_0(A_280,B_281) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2539,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2503])).

tff(c_2552,plain,(
    k5_xboole_0('#skF_5',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2193,c_2145,c_2539])).

tff(c_2087,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_34])).

tff(c_2735,plain,(
    ! [A_288,B_289,C_290] : k5_xboole_0(k5_xboole_0(A_288,B_289),C_290) = k5_xboole_0(A_288,k5_xboole_0(B_289,C_290)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2826,plain,(
    ! [A_28,C_290] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_290)) = k5_xboole_0('#skF_4',C_290) ),
    inference(superposition,[status(thm),theory(equality)],[c_2087,c_2735])).

tff(c_2842,plain,(
    ! [A_291,C_292] : k5_xboole_0(A_291,k5_xboole_0(A_291,C_292)) = C_292 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2193,c_2826])).

tff(c_2884,plain,(
    k5_xboole_0('#skF_5','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2552,c_2842])).

tff(c_2916,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2086,c_2884])).

tff(c_2918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2083,c_2916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.66  
% 3.67/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.67/1.67  
% 3.67/1.67  %Foreground sorts:
% 3.67/1.67  
% 3.67/1.67  
% 3.67/1.67  %Background operators:
% 3.67/1.67  
% 3.67/1.67  
% 3.67/1.67  %Foreground operators:
% 3.67/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.67/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.67/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.67/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.67/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.67/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.67/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.67/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.67/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.67/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.67/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.67/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.67/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.67/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.67/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.67/1.67  
% 3.98/1.68  tff(f_124, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.98/1.68  tff(f_68, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.98/1.68  tff(f_103, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.98/1.68  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.98/1.68  tff(f_66, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.98/1.68  tff(f_72, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.98/1.68  tff(f_70, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.98/1.68  tff(f_74, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.98/1.68  tff(f_60, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.98/1.68  tff(f_64, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.98/1.68  tff(c_68, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.98/1.68  tff(c_126, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_68])).
% 3.98/1.68  tff(c_66, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.98/1.68  tff(c_127, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 3.98/1.68  tff(c_72, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.98/1.68  tff(c_30, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.98/1.68  tff(c_145, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_30])).
% 3.98/1.68  tff(c_448, plain, (![B_119, A_120]: (k1_tarski(B_119)=A_120 | k1_xboole_0=A_120 | ~r1_tarski(A_120, k1_tarski(B_119)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.98/1.68  tff(c_463, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_145, c_448])).
% 3.98/1.68  tff(c_479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_127, c_463])).
% 3.98/1.68  tff(c_480, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_66])).
% 3.98/1.68  tff(c_481, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 3.98/1.68  tff(c_70, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.98/1.68  tff(c_592, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_481, c_70])).
% 3.98/1.68  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/1.68  tff(c_544, plain, (![B_126, A_127]: (k5_xboole_0(B_126, A_127)=k5_xboole_0(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/1.68  tff(c_28, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/1.68  tff(c_560, plain, (![A_127]: (k5_xboole_0(k1_xboole_0, A_127)=A_127)), inference(superposition, [status(thm), theory('equality')], [c_544, c_28])).
% 3.98/1.68  tff(c_34, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.98/1.68  tff(c_1519, plain, (![A_209, B_210, C_211]: (k5_xboole_0(k5_xboole_0(A_209, B_210), C_211)=k5_xboole_0(A_209, k5_xboole_0(B_210, C_211)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.68  tff(c_1572, plain, (![A_28, C_211]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_211))=k5_xboole_0(k1_xboole_0, C_211))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1519])).
% 3.98/1.68  tff(c_1586, plain, (![A_212, C_213]: (k5_xboole_0(A_212, k5_xboole_0(A_212, C_213))=C_213)), inference(demodulation, [status(thm), theory('equality')], [c_560, c_1572])).
% 3.98/1.68  tff(c_1648, plain, (![A_214, B_215]: (k5_xboole_0(A_214, k5_xboole_0(B_215, A_214))=B_215)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1586])).
% 3.98/1.68  tff(c_1626, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1586])).
% 3.98/1.68  tff(c_1651, plain, (![B_215, A_214]: (k5_xboole_0(k5_xboole_0(B_215, A_214), B_215)=A_214)), inference(superposition, [status(thm), theory('equality')], [c_1648, c_1626])).
% 3.98/1.68  tff(c_488, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_72])).
% 3.98/1.68  tff(c_1959, plain, (![A_222, B_223]: (k5_xboole_0(k5_xboole_0(A_222, B_223), k2_xboole_0(A_222, B_223))=k3_xboole_0(A_222, B_223))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.98/1.68  tff(c_2032, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_488, c_1959])).
% 3.98/1.68  tff(c_2045, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1651, c_2032])).
% 3.98/1.68  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.98/1.68  tff(c_1161, plain, (![B_191, A_192]: (k1_tarski(B_191)=A_192 | k1_xboole_0=A_192 | ~r1_tarski(A_192, k1_tarski(B_191)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.98/1.68  tff(c_1180, plain, (![A_192]: (k1_tarski('#skF_3')=A_192 | k1_xboole_0=A_192 | ~r1_tarski(A_192, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_481, c_1161])).
% 3.98/1.68  tff(c_1200, plain, (![A_193]: (A_193='#skF_4' | k1_xboole_0=A_193 | ~r1_tarski(A_193, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_1180])).
% 3.98/1.68  tff(c_1235, plain, (![B_20]: (k3_xboole_0('#skF_4', B_20)='#skF_4' | k3_xboole_0('#skF_4', B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_1200])).
% 3.98/1.68  tff(c_2054, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2045, c_1235])).
% 3.98/1.68  tff(c_2080, plain, ('#skF_5'='#skF_4' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2045, c_2054])).
% 3.98/1.68  tff(c_2082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_480, c_592, c_2080])).
% 3.98/1.68  tff(c_2083, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_68])).
% 3.98/1.68  tff(c_2084, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_68])).
% 3.98/1.68  tff(c_2086, plain, (![A_22]: (k5_xboole_0(A_22, '#skF_4')=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_28])).
% 3.98/1.68  tff(c_2177, plain, (![B_232, A_233]: (k5_xboole_0(B_232, A_233)=k5_xboole_0(A_233, B_232))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/1.68  tff(c_2193, plain, (![A_233]: (k5_xboole_0('#skF_4', A_233)=A_233)), inference(superposition, [status(thm), theory('equality')], [c_2177, c_2086])).
% 3.98/1.68  tff(c_26, plain, (![A_21]: (k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.68  tff(c_2136, plain, (![A_230]: (A_230='#skF_4' | ~r1_tarski(A_230, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_2084, c_26])).
% 3.98/1.68  tff(c_2145, plain, (![B_20]: (k3_xboole_0('#skF_4', B_20)='#skF_4')), inference(resolution, [status(thm)], [c_24, c_2136])).
% 3.98/1.68  tff(c_2503, plain, (![A_280, B_281]: (k5_xboole_0(k5_xboole_0(A_280, B_281), k2_xboole_0(A_280, B_281))=k3_xboole_0(A_280, B_281))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.98/1.68  tff(c_2539, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_72, c_2503])).
% 3.98/1.68  tff(c_2552, plain, (k5_xboole_0('#skF_5', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2193, c_2145, c_2539])).
% 3.98/1.68  tff(c_2087, plain, (![A_28]: (k5_xboole_0(A_28, A_28)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_34])).
% 3.98/1.68  tff(c_2735, plain, (![A_288, B_289, C_290]: (k5_xboole_0(k5_xboole_0(A_288, B_289), C_290)=k5_xboole_0(A_288, k5_xboole_0(B_289, C_290)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.68  tff(c_2826, plain, (![A_28, C_290]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_290))=k5_xboole_0('#skF_4', C_290))), inference(superposition, [status(thm), theory('equality')], [c_2087, c_2735])).
% 3.98/1.68  tff(c_2842, plain, (![A_291, C_292]: (k5_xboole_0(A_291, k5_xboole_0(A_291, C_292))=C_292)), inference(demodulation, [status(thm), theory('equality')], [c_2193, c_2826])).
% 3.98/1.68  tff(c_2884, plain, (k5_xboole_0('#skF_5', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2552, c_2842])).
% 3.98/1.68  tff(c_2916, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2086, c_2884])).
% 3.98/1.68  tff(c_2918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2083, c_2916])).
% 3.98/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.68  
% 3.98/1.68  Inference rules
% 3.98/1.68  ----------------------
% 3.98/1.68  #Ref     : 0
% 3.98/1.68  #Sup     : 660
% 3.98/1.68  #Fact    : 1
% 3.98/1.68  #Define  : 0
% 3.98/1.68  #Split   : 7
% 3.98/1.68  #Chain   : 0
% 3.98/1.68  #Close   : 0
% 3.98/1.68  
% 3.98/1.68  Ordering : KBO
% 3.98/1.68  
% 3.98/1.68  Simplification rules
% 3.98/1.68  ----------------------
% 3.98/1.68  #Subsume      : 54
% 3.98/1.68  #Demod        : 281
% 3.98/1.68  #Tautology    : 388
% 3.98/1.68  #SimpNegUnit  : 26
% 3.98/1.68  #BackRed      : 5
% 3.98/1.68  
% 3.98/1.68  #Partial instantiations: 0
% 3.98/1.68  #Strategies tried      : 1
% 3.98/1.68  
% 3.98/1.68  Timing (in seconds)
% 3.98/1.68  ----------------------
% 3.98/1.69  Preprocessing        : 0.34
% 3.98/1.69  Parsing              : 0.18
% 3.98/1.69  CNF conversion       : 0.02
% 3.98/1.69  Main loop            : 0.57
% 3.98/1.69  Inferencing          : 0.20
% 3.98/1.69  Reduction            : 0.20
% 3.98/1.69  Demodulation         : 0.15
% 3.98/1.69  BG Simplification    : 0.03
% 3.98/1.69  Subsumption          : 0.09
% 3.98/1.69  Abstraction          : 0.03
% 3.98/1.69  MUC search           : 0.00
% 3.98/1.69  Cooper               : 0.00
% 3.98/1.69  Total                : 0.94
% 3.98/1.69  Index Insertion      : 0.00
% 3.98/1.69  Index Deletion       : 0.00
% 3.98/1.69  Index Matching       : 0.00
% 3.98/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------

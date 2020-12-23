%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:56 EST 2020

% Result     : Theorem 8.85s
% Output     : CNFRefutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 248 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 395 expanded)
%              Number of equality atoms :   37 ( 152 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_54,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_145,plain,(
    ! [B_12] : k3_xboole_0(B_12,B_12) = B_12 ),
    inference(resolution,[status(thm)],[c_26,c_133])).

tff(c_373,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_388,plain,(
    ! [B_12] : k5_xboole_0(B_12,B_12) = k4_xboole_0(B_12,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_373])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_945,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden(A_133,B_134)
      | r2_hidden(A_133,C_135)
      | ~ r2_hidden(A_133,k5_xboole_0(B_134,C_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_964,plain,(
    ! [B_134,C_135,B_4] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_134,C_135),B_4),B_134)
      | r2_hidden('#skF_1'(k5_xboole_0(B_134,C_135),B_4),C_135)
      | r1_tarski(k5_xboole_0(B_134,C_135),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_945])).

tff(c_2984,plain,(
    ! [C_135,B_4] :
      ( r1_tarski(k5_xboole_0(C_135,C_135),B_4)
      | r2_hidden('#skF_1'(k5_xboole_0(C_135,C_135),B_4),C_135) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_964])).

tff(c_2994,plain,(
    ! [C_135,B_4] :
      ( r1_tarski(k4_xboole_0(C_135,C_135),B_4)
      | r2_hidden('#skF_1'(k4_xboole_0(C_135,C_135),B_4),C_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_388,c_2984])).

tff(c_875,plain,(
    ! [A_125,C_126,B_127] :
      ( ~ r2_hidden(A_125,C_126)
      | ~ r2_hidden(A_125,B_127)
      | ~ r2_hidden(A_125,k5_xboole_0(B_127,C_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1161,plain,(
    ! [A_160,B_161] :
      ( ~ r2_hidden(A_160,B_161)
      | ~ r2_hidden(A_160,B_161)
      | ~ r2_hidden(A_160,k4_xboole_0(B_161,B_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_875])).

tff(c_4479,plain,(
    ! [B_372,B_373] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(B_372,B_372),B_373),B_372)
      | r1_tarski(k4_xboole_0(B_372,B_372),B_373) ) ),
    inference(resolution,[status(thm)],[c_8,c_1161])).

tff(c_4525,plain,(
    ! [C_135,B_4] : r1_tarski(k4_xboole_0(C_135,C_135),B_4) ),
    inference(resolution,[status(thm)],[c_2994,c_4479])).

tff(c_4582,plain,(
    ! [C_376,B_377] : r1_tarski(k4_xboole_0(C_376,C_376),B_377) ),
    inference(resolution,[status(thm)],[c_2994,c_4479])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4768,plain,(
    ! [C_384,B_385] :
      ( k4_xboole_0(C_384,C_384) = B_385
      | ~ r1_tarski(B_385,k4_xboole_0(C_384,C_384)) ) ),
    inference(resolution,[status(thm)],[c_4582,c_22])).

tff(c_4794,plain,(
    ! [C_387,C_386] : k4_xboole_0(C_387,C_387) = k4_xboole_0(C_386,C_386) ),
    inference(resolution,[status(thm)],[c_4525,c_4768])).

tff(c_30,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_144,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = A_19 ),
    inference(resolution,[status(thm)],[c_34,c_133])).

tff(c_385,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k5_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_373])).

tff(c_417,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k2_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_385])).

tff(c_36,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_423,plain,(
    ! [A_82,B_83] : k5_xboole_0(k2_xboole_0(A_82,B_83),k4_xboole_0(A_82,A_82)) = k2_xboole_0(k2_xboole_0(A_82,B_83),A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_36])).

tff(c_4049,plain,(
    ! [A_361,B_362] : k5_xboole_0(k2_xboole_0(A_361,B_362),k4_xboole_0(A_361,A_361)) = k2_xboole_0(A_361,k2_xboole_0(A_361,B_362)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_423])).

tff(c_4123,plain,(
    ! [B_363,A_364] : k5_xboole_0(k2_xboole_0(B_363,A_364),k4_xboole_0(A_364,A_364)) = k2_xboole_0(A_364,k2_xboole_0(A_364,B_363)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4049])).

tff(c_4187,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(k3_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16))) = k2_xboole_0(k3_xboole_0(A_15,B_16),k2_xboole_0(k3_xboole_0(A_15,B_16),A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4123])).

tff(c_4206,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(k3_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16))) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2,c_30,c_2,c_4187])).

tff(c_4826,plain,(
    ! [A_15,C_387] : k5_xboole_0(A_15,k4_xboole_0(C_387,C_387)) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_4794,c_4206])).

tff(c_343,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_tarski(A_69),B_70)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_572,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(k1_tarski(A_97),B_98) = k1_tarski(A_97)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_343,c_32])).

tff(c_28,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_581,plain,(
    ! [A_97,B_98] :
      ( k5_xboole_0(k1_tarski(A_97),k1_tarski(A_97)) = k4_xboole_0(k1_tarski(A_97),B_98)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_28])).

tff(c_617,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(k1_tarski(A_97),k1_tarski(A_97)) = k4_xboole_0(k1_tarski(A_97),B_98)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_581])).

tff(c_12859,plain,(
    ! [A_510,B_511,B_512] :
      ( r1_tarski(k4_xboole_0(k1_tarski(A_510),B_511),B_512)
      | ~ r2_hidden(A_510,B_511) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_4582])).

tff(c_4611,plain,(
    ! [C_376,B_377] :
      ( k4_xboole_0(C_376,C_376) = B_377
      | ~ r1_tarski(B_377,k4_xboole_0(C_376,C_376)) ) ),
    inference(resolution,[status(thm)],[c_4582,c_22])).

tff(c_14281,plain,(
    ! [A_571,B_572,C_573] :
      ( k4_xboole_0(k1_tarski(A_571),B_572) = k4_xboole_0(C_573,C_573)
      | ~ r2_hidden(A_571,B_572) ) ),
    inference(resolution,[status(thm)],[c_12859,c_4611])).

tff(c_14801,plain,(
    ! [B_572,C_573,A_571] :
      ( k5_xboole_0(B_572,k4_xboole_0(C_573,C_573)) = k2_xboole_0(B_572,k1_tarski(A_571))
      | ~ r2_hidden(A_571,B_572) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14281,c_36])).

tff(c_14995,plain,(
    ! [B_574,A_575] :
      ( k2_xboole_0(B_574,k1_tarski(A_575)) = B_574
      | ~ r2_hidden(A_575,B_574) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4826,c_14801])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_15314,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14995,c_56])).

tff(c_15397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_15314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:59:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.85/3.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.90/3.22  
% 8.90/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.22  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 8.91/3.22  
% 8.91/3.22  %Foreground sorts:
% 8.91/3.22  
% 8.91/3.22  
% 8.91/3.22  %Background operators:
% 8.91/3.22  
% 8.91/3.22  
% 8.91/3.22  %Foreground operators:
% 8.91/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.91/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.91/3.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.91/3.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.91/3.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.91/3.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.91/3.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.91/3.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.91/3.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.91/3.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.91/3.22  tff('#skF_2', type, '#skF_2': $i).
% 8.91/3.22  tff('#skF_3', type, '#skF_3': $i).
% 8.91/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.91/3.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.91/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.91/3.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.91/3.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.91/3.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.91/3.22  
% 8.91/3.24  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 8.91/3.24  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.91/3.24  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.91/3.24  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.91/3.24  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.91/3.24  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.91/3.24  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.91/3.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.91/3.24  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.91/3.24  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.91/3.24  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.91/3.24  tff(c_54, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.91/3.24  tff(c_26, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.91/3.24  tff(c_133, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.91/3.24  tff(c_145, plain, (![B_12]: (k3_xboole_0(B_12, B_12)=B_12)), inference(resolution, [status(thm)], [c_26, c_133])).
% 8.91/3.24  tff(c_373, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.91/3.24  tff(c_388, plain, (![B_12]: (k5_xboole_0(B_12, B_12)=k4_xboole_0(B_12, B_12))), inference(superposition, [status(thm), theory('equality')], [c_145, c_373])).
% 8.91/3.24  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.91/3.24  tff(c_945, plain, (![A_133, B_134, C_135]: (r2_hidden(A_133, B_134) | r2_hidden(A_133, C_135) | ~r2_hidden(A_133, k5_xboole_0(B_134, C_135)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.91/3.24  tff(c_964, plain, (![B_134, C_135, B_4]: (r2_hidden('#skF_1'(k5_xboole_0(B_134, C_135), B_4), B_134) | r2_hidden('#skF_1'(k5_xboole_0(B_134, C_135), B_4), C_135) | r1_tarski(k5_xboole_0(B_134, C_135), B_4))), inference(resolution, [status(thm)], [c_8, c_945])).
% 8.91/3.24  tff(c_2984, plain, (![C_135, B_4]: (r1_tarski(k5_xboole_0(C_135, C_135), B_4) | r2_hidden('#skF_1'(k5_xboole_0(C_135, C_135), B_4), C_135))), inference(factorization, [status(thm), theory('equality')], [c_964])).
% 8.91/3.24  tff(c_2994, plain, (![C_135, B_4]: (r1_tarski(k4_xboole_0(C_135, C_135), B_4) | r2_hidden('#skF_1'(k4_xboole_0(C_135, C_135), B_4), C_135))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_388, c_2984])).
% 8.91/3.24  tff(c_875, plain, (![A_125, C_126, B_127]: (~r2_hidden(A_125, C_126) | ~r2_hidden(A_125, B_127) | ~r2_hidden(A_125, k5_xboole_0(B_127, C_126)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.91/3.24  tff(c_1161, plain, (![A_160, B_161]: (~r2_hidden(A_160, B_161) | ~r2_hidden(A_160, B_161) | ~r2_hidden(A_160, k4_xboole_0(B_161, B_161)))), inference(superposition, [status(thm), theory('equality')], [c_388, c_875])).
% 8.91/3.24  tff(c_4479, plain, (![B_372, B_373]: (~r2_hidden('#skF_1'(k4_xboole_0(B_372, B_372), B_373), B_372) | r1_tarski(k4_xboole_0(B_372, B_372), B_373))), inference(resolution, [status(thm)], [c_8, c_1161])).
% 8.91/3.24  tff(c_4525, plain, (![C_135, B_4]: (r1_tarski(k4_xboole_0(C_135, C_135), B_4))), inference(resolution, [status(thm)], [c_2994, c_4479])).
% 8.91/3.24  tff(c_4582, plain, (![C_376, B_377]: (r1_tarski(k4_xboole_0(C_376, C_376), B_377))), inference(resolution, [status(thm)], [c_2994, c_4479])).
% 8.91/3.24  tff(c_22, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.91/3.24  tff(c_4768, plain, (![C_384, B_385]: (k4_xboole_0(C_384, C_384)=B_385 | ~r1_tarski(B_385, k4_xboole_0(C_384, C_384)))), inference(resolution, [status(thm)], [c_4582, c_22])).
% 8.91/3.24  tff(c_4794, plain, (![C_387, C_386]: (k4_xboole_0(C_387, C_387)=k4_xboole_0(C_386, C_386))), inference(resolution, [status(thm)], [c_4525, c_4768])).
% 8.91/3.24  tff(c_30, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k3_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.91/3.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.91/3.24  tff(c_34, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.91/3.24  tff(c_144, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k2_xboole_0(A_19, B_20))=A_19)), inference(resolution, [status(thm)], [c_34, c_133])).
% 8.91/3.24  tff(c_385, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k5_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_144, c_373])).
% 8.91/3.24  tff(c_417, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k2_xboole_0(A_82, B_83))=k4_xboole_0(A_82, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_385])).
% 8.91/3.24  tff(c_36, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.91/3.24  tff(c_423, plain, (![A_82, B_83]: (k5_xboole_0(k2_xboole_0(A_82, B_83), k4_xboole_0(A_82, A_82))=k2_xboole_0(k2_xboole_0(A_82, B_83), A_82))), inference(superposition, [status(thm), theory('equality')], [c_417, c_36])).
% 8.91/3.24  tff(c_4049, plain, (![A_361, B_362]: (k5_xboole_0(k2_xboole_0(A_361, B_362), k4_xboole_0(A_361, A_361))=k2_xboole_0(A_361, k2_xboole_0(A_361, B_362)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_423])).
% 8.91/3.24  tff(c_4123, plain, (![B_363, A_364]: (k5_xboole_0(k2_xboole_0(B_363, A_364), k4_xboole_0(A_364, A_364))=k2_xboole_0(A_364, k2_xboole_0(A_364, B_363)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4049])).
% 8.91/3.24  tff(c_4187, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(k3_xboole_0(A_15, B_16), k3_xboole_0(A_15, B_16)))=k2_xboole_0(k3_xboole_0(A_15, B_16), k2_xboole_0(k3_xboole_0(A_15, B_16), A_15)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_4123])).
% 8.91/3.24  tff(c_4206, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(k3_xboole_0(A_15, B_16), k3_xboole_0(A_15, B_16)))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2, c_30, c_2, c_4187])).
% 8.91/3.24  tff(c_4826, plain, (![A_15, C_387]: (k5_xboole_0(A_15, k4_xboole_0(C_387, C_387))=A_15)), inference(superposition, [status(thm), theory('equality')], [c_4794, c_4206])).
% 8.91/3.24  tff(c_343, plain, (![A_69, B_70]: (r1_tarski(k1_tarski(A_69), B_70) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.91/3.24  tff(c_32, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.91/3.24  tff(c_572, plain, (![A_97, B_98]: (k3_xboole_0(k1_tarski(A_97), B_98)=k1_tarski(A_97) | ~r2_hidden(A_97, B_98))), inference(resolution, [status(thm)], [c_343, c_32])).
% 8.91/3.24  tff(c_28, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.91/3.24  tff(c_581, plain, (![A_97, B_98]: (k5_xboole_0(k1_tarski(A_97), k1_tarski(A_97))=k4_xboole_0(k1_tarski(A_97), B_98) | ~r2_hidden(A_97, B_98))), inference(superposition, [status(thm), theory('equality')], [c_572, c_28])).
% 8.91/3.24  tff(c_617, plain, (![A_97, B_98]: (k4_xboole_0(k1_tarski(A_97), k1_tarski(A_97))=k4_xboole_0(k1_tarski(A_97), B_98) | ~r2_hidden(A_97, B_98))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_581])).
% 8.91/3.24  tff(c_12859, plain, (![A_510, B_511, B_512]: (r1_tarski(k4_xboole_0(k1_tarski(A_510), B_511), B_512) | ~r2_hidden(A_510, B_511))), inference(superposition, [status(thm), theory('equality')], [c_617, c_4582])).
% 8.91/3.24  tff(c_4611, plain, (![C_376, B_377]: (k4_xboole_0(C_376, C_376)=B_377 | ~r1_tarski(B_377, k4_xboole_0(C_376, C_376)))), inference(resolution, [status(thm)], [c_4582, c_22])).
% 8.91/3.24  tff(c_14281, plain, (![A_571, B_572, C_573]: (k4_xboole_0(k1_tarski(A_571), B_572)=k4_xboole_0(C_573, C_573) | ~r2_hidden(A_571, B_572))), inference(resolution, [status(thm)], [c_12859, c_4611])).
% 8.91/3.24  tff(c_14801, plain, (![B_572, C_573, A_571]: (k5_xboole_0(B_572, k4_xboole_0(C_573, C_573))=k2_xboole_0(B_572, k1_tarski(A_571)) | ~r2_hidden(A_571, B_572))), inference(superposition, [status(thm), theory('equality')], [c_14281, c_36])).
% 8.91/3.24  tff(c_14995, plain, (![B_574, A_575]: (k2_xboole_0(B_574, k1_tarski(A_575))=B_574 | ~r2_hidden(A_575, B_574))), inference(demodulation, [status(thm), theory('equality')], [c_4826, c_14801])).
% 8.91/3.24  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.91/3.24  tff(c_56, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 8.91/3.24  tff(c_15314, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14995, c_56])).
% 8.91/3.24  tff(c_15397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_15314])).
% 8.91/3.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.24  
% 8.91/3.24  Inference rules
% 8.91/3.24  ----------------------
% 8.91/3.24  #Ref     : 0
% 8.91/3.24  #Sup     : 3811
% 8.91/3.24  #Fact    : 2
% 8.91/3.24  #Define  : 0
% 8.91/3.24  #Split   : 1
% 8.91/3.24  #Chain   : 0
% 8.91/3.24  #Close   : 0
% 8.91/3.24  
% 8.91/3.24  Ordering : KBO
% 8.91/3.24  
% 8.91/3.24  Simplification rules
% 8.91/3.24  ----------------------
% 8.91/3.24  #Subsume      : 1332
% 8.91/3.24  #Demod        : 2005
% 8.91/3.24  #Tautology    : 1324
% 8.91/3.24  #SimpNegUnit  : 30
% 8.91/3.24  #BackRed      : 4
% 8.91/3.24  
% 8.91/3.24  #Partial instantiations: 0
% 8.91/3.24  #Strategies tried      : 1
% 8.91/3.24  
% 8.91/3.24  Timing (in seconds)
% 8.91/3.24  ----------------------
% 8.91/3.24  Preprocessing        : 0.33
% 8.91/3.24  Parsing              : 0.18
% 8.91/3.24  CNF conversion       : 0.02
% 8.91/3.24  Main loop            : 2.10
% 8.91/3.24  Inferencing          : 0.54
% 8.91/3.24  Reduction            : 0.92
% 8.91/3.24  Demodulation         : 0.75
% 8.91/3.24  BG Simplification    : 0.06
% 8.91/3.24  Subsumption          : 0.47
% 8.91/3.24  Abstraction          : 0.08
% 8.91/3.24  MUC search           : 0.00
% 8.91/3.24  Cooper               : 0.00
% 8.91/3.24  Total                : 2.47
% 8.91/3.25  Index Insertion      : 0.00
% 8.91/3.25  Index Deletion       : 0.00
% 8.91/3.25  Index Matching       : 0.00
% 8.91/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

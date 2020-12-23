%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:56 EST 2020

% Result     : Theorem 9.58s
% Output     : CNFRefutation 9.78s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 166 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 258 expanded)
%              Number of equality atoms :   61 ( 105 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_67,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_86,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_96,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_150,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_11490,plain,(
    ! [A_5258,B_5259,C_5260] :
      ( r2_hidden('#skF_4'(A_5258,B_5259,C_5260),A_5258)
      | r2_hidden('#skF_5'(A_5258,B_5259,C_5260),C_5260)
      | k4_xboole_0(A_5258,B_5259) = C_5260 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [A_14,B_15,C_16] :
      ( ~ r2_hidden('#skF_4'(A_14,B_15,C_16),C_16)
      | r2_hidden('#skF_5'(A_14,B_15,C_16),C_16)
      | k4_xboole_0(A_14,B_15) = C_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11570,plain,(
    ! [A_5258,B_5259] :
      ( r2_hidden('#skF_5'(A_5258,B_5259,A_5258),A_5258)
      | k4_xboole_0(A_5258,B_5259) = A_5258 ) ),
    inference(resolution,[status(thm)],[c_11490,c_40])).

tff(c_38,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden('#skF_4'(A_14,B_15,C_16),A_14)
      | r2_hidden('#skF_5'(A_14,B_15,C_16),B_15)
      | ~ r2_hidden('#skF_5'(A_14,B_15,C_16),A_14)
      | k4_xboole_0(A_14,B_15) = C_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12622,plain,(
    ! [A_5318,B_5319,C_5320] :
      ( ~ r2_hidden('#skF_4'(A_5318,B_5319,C_5320),C_5320)
      | r2_hidden('#skF_5'(A_5318,B_5319,C_5320),B_5319)
      | ~ r2_hidden('#skF_5'(A_5318,B_5319,C_5320),A_5318)
      | k4_xboole_0(A_5318,B_5319) = C_5320 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16485,plain,(
    ! [A_5445,B_5446] :
      ( r2_hidden('#skF_5'(A_5445,B_5446,A_5445),B_5446)
      | ~ r2_hidden('#skF_5'(A_5445,B_5446,A_5445),A_5445)
      | k4_xboole_0(A_5445,B_5446) = A_5445 ) ),
    inference(resolution,[status(thm)],[c_38,c_12622])).

tff(c_17095,plain,(
    ! [A_5460,B_5461] :
      ( r2_hidden('#skF_5'(A_5460,B_5461,A_5460),B_5461)
      | k4_xboole_0(A_5460,B_5461) = A_5460 ) ),
    inference(resolution,[status(thm)],[c_11570,c_16485])).

tff(c_58,plain,(
    ! [A_27,B_28] : r1_tarski(k4_xboole_0(A_27,B_28),A_27) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,(
    ! [A_26] : r1_tarski(k1_xboole_0,A_26) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_282,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_295,plain,(
    ! [A_76] :
      ( k1_xboole_0 = A_76
      | ~ r1_tarski(A_76,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_56,c_282])).

tff(c_313,plain,(
    ! [B_77] : k4_xboole_0(k1_xboole_0,B_77) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_295])).

tff(c_90,plain,(
    ! [B_43,A_42] :
      ( ~ r2_hidden(B_43,A_42)
      | k4_xboole_0(A_42,k1_tarski(B_43)) != A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_326,plain,(
    ! [B_43] : ~ r2_hidden(B_43,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_90])).

tff(c_17150,plain,(
    ! [A_5460] : k4_xboole_0(A_5460,k1_xboole_0) = A_5460 ),
    inference(resolution,[status(thm)],[c_17095,c_326])).

tff(c_175,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_197,plain,(
    ! [A_68] : k3_xboole_0(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_175])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_206,plain,(
    ! [A_68] : k3_xboole_0(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_2])).

tff(c_386,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_395,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = k4_xboole_0(A_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_386])).

tff(c_17153,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17150,c_395])).

tff(c_92,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,k1_tarski(B_43)) = A_42
      | r2_hidden(B_43,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ! [A_14,B_15,C_16] :
      ( ~ r2_hidden('#skF_4'(A_14,B_15,C_16),B_15)
      | r2_hidden('#skF_5'(A_14,B_15,C_16),C_16)
      | k4_xboole_0(A_14,B_15) = C_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11941,plain,(
    ! [A_5287,C_5288] :
      ( r2_hidden('#skF_5'(A_5287,A_5287,C_5288),C_5288)
      | k4_xboole_0(A_5287,A_5287) = C_5288 ) ),
    inference(resolution,[status(thm)],[c_11490,c_42])).

tff(c_11992,plain,(
    ! [A_5287] : k4_xboole_0(A_5287,A_5287) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11941,c_326])).

tff(c_50,plain,(
    ! [B_21] : r1_tarski(B_21,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_186,plain,(
    ! [B_21] : k3_xboole_0(B_21,B_21) = B_21 ),
    inference(resolution,[status(thm)],[c_50,c_175])).

tff(c_401,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k4_xboole_0(B_21,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_386])).

tff(c_11995,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11992,c_401])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_481,plain,(
    ! [D_95,A_96,B_97] :
      ( r2_hidden(D_95,A_96)
      | ~ r2_hidden(D_95,k3_xboole_0(A_96,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13486,plain,(
    ! [A_5389,B_5390,B_5391] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_5389,B_5390),B_5391),A_5389)
      | r1_tarski(k3_xboole_0(A_5389,B_5390),B_5391) ) ),
    inference(resolution,[status(thm)],[c_8,c_481])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_13573,plain,(
    ! [A_5392,B_5393] : r1_tarski(k3_xboole_0(A_5392,B_5393),A_5392) ),
    inference(resolution,[status(thm)],[c_13486,c_6])).

tff(c_54,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13720,plain,(
    ! [A_5396,B_5397] : k3_xboole_0(k3_xboole_0(A_5396,B_5397),A_5396) = k3_xboole_0(A_5396,B_5397) ),
    inference(resolution,[status(thm)],[c_13573,c_54])).

tff(c_52,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_13754,plain,(
    ! [A_5396,B_5397] : k5_xboole_0(k3_xboole_0(A_5396,B_5397),k3_xboole_0(A_5396,B_5397)) = k4_xboole_0(k3_xboole_0(A_5396,B_5397),A_5396) ),
    inference(superposition,[status(thm),theory(equality)],[c_13720,c_52])).

tff(c_13831,plain,(
    ! [A_5398,B_5399] : k4_xboole_0(k3_xboole_0(A_5398,B_5399),A_5398) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11995,c_13754])).

tff(c_19916,plain,(
    ! [B_5509,B_5510] :
      ( k3_xboole_0(k1_tarski(B_5509),B_5510) = k1_xboole_0
      | r2_hidden(B_5509,k3_xboole_0(k1_tarski(B_5509),B_5510)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_13831])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_19989,plain,(
    ! [B_5511,B_5512] :
      ( r2_hidden(B_5511,B_5512)
      | k3_xboole_0(k1_tarski(B_5511),B_5512) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_19916,c_12])).

tff(c_20156,plain,(
    ! [B_5511,B_5512] :
      ( k5_xboole_0(k1_tarski(B_5511),k1_xboole_0) = k4_xboole_0(k1_tarski(B_5511),B_5512)
      | r2_hidden(B_5511,B_5512) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19989,c_52])).

tff(c_20957,plain,(
    ! [B_5524,B_5525] :
      ( k4_xboole_0(k1_tarski(B_5524),B_5525) = k1_tarski(B_5524)
      | r2_hidden(B_5524,B_5525) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17153,c_20156])).

tff(c_94,plain,
    ( k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_8')
    | r2_hidden('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_271,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_21036,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_20957,c_271])).

tff(c_21085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_21036])).

tff(c_21086,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_84,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_152,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_62,plain,(
    ! [E_35,A_29,B_30] : r2_hidden(E_35,k1_enumset1(A_29,B_30,E_35)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_170,plain,(
    ! [B_62,A_63] : r2_hidden(B_62,k2_tarski(A_63,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_62])).

tff(c_173,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_170])).

tff(c_21087,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_98,plain,
    ( k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_8')
    | k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_tarski('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_21088,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_21107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21087,c_21088])).

tff(c_21108,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_tarski('#skF_10') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_21275,plain,(
    ! [D_5551,B_5552,A_5553] :
      ( ~ r2_hidden(D_5551,B_5552)
      | ~ r2_hidden(D_5551,k4_xboole_0(A_5553,B_5552)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_21332,plain,(
    ! [D_5556] :
      ( ~ r2_hidden(D_5556,'#skF_11')
      | ~ r2_hidden(D_5556,k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21108,c_21275])).

tff(c_21336,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_173,c_21332])).

tff(c_21340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21086,c_21336])).

tff(c_21341,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_21443,plain,(
    ! [A_5562,B_5563] : k1_enumset1(A_5562,A_5562,B_5563) = k2_tarski(A_5562,B_5563) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_21461,plain,(
    ! [B_5564,A_5565] : r2_hidden(B_5564,k2_tarski(A_5565,B_5564)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21443,c_62])).

tff(c_21464,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_21461])).

tff(c_21342,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_100,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_tarski('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_21474,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21342,c_100])).

tff(c_21715,plain,(
    ! [D_5595,B_5596,A_5597] :
      ( ~ r2_hidden(D_5595,B_5596)
      | ~ r2_hidden(D_5595,k4_xboole_0(A_5597,B_5596)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_21730,plain,(
    ! [D_5598] :
      ( ~ r2_hidden(D_5598,'#skF_11')
      | ~ r2_hidden(D_5598,k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21474,c_21715])).

tff(c_21738,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_21464,c_21730])).

tff(c_21743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21341,c_21738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.58/3.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.58/3.41  
% 9.58/3.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.58/3.41  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 9.58/3.41  
% 9.58/3.41  %Foreground sorts:
% 9.58/3.41  
% 9.58/3.41  
% 9.58/3.41  %Background operators:
% 9.58/3.41  
% 9.58/3.41  
% 9.58/3.41  %Foreground operators:
% 9.58/3.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.58/3.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.58/3.41  tff('#skF_11', type, '#skF_11': $i).
% 9.58/3.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.58/3.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.58/3.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.58/3.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.58/3.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.58/3.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.58/3.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.58/3.41  tff('#skF_10', type, '#skF_10': $i).
% 9.58/3.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.58/3.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.58/3.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.58/3.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.58/3.41  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 9.58/3.41  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 9.58/3.41  tff('#skF_9', type, '#skF_9': $i).
% 9.58/3.41  tff('#skF_8', type, '#skF_8': $i).
% 9.58/3.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.58/3.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.58/3.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.58/3.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.58/3.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.58/3.41  
% 9.78/3.43  tff(f_101, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 9.78/3.43  tff(f_53, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.78/3.43  tff(f_69, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.78/3.43  tff(f_67, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.78/3.43  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.78/3.43  tff(f_95, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 9.78/3.43  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.78/3.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.78/3.43  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.78/3.43  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.78/3.43  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.78/3.43  tff(f_86, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.78/3.43  tff(f_88, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.78/3.43  tff(f_84, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 9.78/3.43  tff(c_96, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.78/3.43  tff(c_150, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_96])).
% 9.78/3.43  tff(c_11490, plain, (![A_5258, B_5259, C_5260]: (r2_hidden('#skF_4'(A_5258, B_5259, C_5260), A_5258) | r2_hidden('#skF_5'(A_5258, B_5259, C_5260), C_5260) | k4_xboole_0(A_5258, B_5259)=C_5260)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.78/3.43  tff(c_40, plain, (![A_14, B_15, C_16]: (~r2_hidden('#skF_4'(A_14, B_15, C_16), C_16) | r2_hidden('#skF_5'(A_14, B_15, C_16), C_16) | k4_xboole_0(A_14, B_15)=C_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.78/3.43  tff(c_11570, plain, (![A_5258, B_5259]: (r2_hidden('#skF_5'(A_5258, B_5259, A_5258), A_5258) | k4_xboole_0(A_5258, B_5259)=A_5258)), inference(resolution, [status(thm)], [c_11490, c_40])).
% 9.78/3.43  tff(c_38, plain, (![A_14, B_15, C_16]: (r2_hidden('#skF_4'(A_14, B_15, C_16), A_14) | r2_hidden('#skF_5'(A_14, B_15, C_16), B_15) | ~r2_hidden('#skF_5'(A_14, B_15, C_16), A_14) | k4_xboole_0(A_14, B_15)=C_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.78/3.43  tff(c_12622, plain, (![A_5318, B_5319, C_5320]: (~r2_hidden('#skF_4'(A_5318, B_5319, C_5320), C_5320) | r2_hidden('#skF_5'(A_5318, B_5319, C_5320), B_5319) | ~r2_hidden('#skF_5'(A_5318, B_5319, C_5320), A_5318) | k4_xboole_0(A_5318, B_5319)=C_5320)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.78/3.43  tff(c_16485, plain, (![A_5445, B_5446]: (r2_hidden('#skF_5'(A_5445, B_5446, A_5445), B_5446) | ~r2_hidden('#skF_5'(A_5445, B_5446, A_5445), A_5445) | k4_xboole_0(A_5445, B_5446)=A_5445)), inference(resolution, [status(thm)], [c_38, c_12622])).
% 9.78/3.43  tff(c_17095, plain, (![A_5460, B_5461]: (r2_hidden('#skF_5'(A_5460, B_5461, A_5460), B_5461) | k4_xboole_0(A_5460, B_5461)=A_5460)), inference(resolution, [status(thm)], [c_11570, c_16485])).
% 9.78/3.43  tff(c_58, plain, (![A_27, B_28]: (r1_tarski(k4_xboole_0(A_27, B_28), A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.78/3.43  tff(c_56, plain, (![A_26]: (r1_tarski(k1_xboole_0, A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.78/3.43  tff(c_282, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.78/3.43  tff(c_295, plain, (![A_76]: (k1_xboole_0=A_76 | ~r1_tarski(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_282])).
% 9.78/3.43  tff(c_313, plain, (![B_77]: (k4_xboole_0(k1_xboole_0, B_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_295])).
% 9.78/3.43  tff(c_90, plain, (![B_43, A_42]: (~r2_hidden(B_43, A_42) | k4_xboole_0(A_42, k1_tarski(B_43))!=A_42)), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.78/3.43  tff(c_326, plain, (![B_43]: (~r2_hidden(B_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_313, c_90])).
% 9.78/3.43  tff(c_17150, plain, (![A_5460]: (k4_xboole_0(A_5460, k1_xboole_0)=A_5460)), inference(resolution, [status(thm)], [c_17095, c_326])).
% 9.78/3.43  tff(c_175, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.78/3.43  tff(c_197, plain, (![A_68]: (k3_xboole_0(k1_xboole_0, A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_175])).
% 9.78/3.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.78/3.43  tff(c_206, plain, (![A_68]: (k3_xboole_0(A_68, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_197, c_2])).
% 9.78/3.43  tff(c_386, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.78/3.43  tff(c_395, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=k4_xboole_0(A_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_206, c_386])).
% 9.78/3.43  tff(c_17153, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_17150, c_395])).
% 9.78/3.43  tff(c_92, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k1_tarski(B_43))=A_42 | r2_hidden(B_43, A_42))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.78/3.43  tff(c_42, plain, (![A_14, B_15, C_16]: (~r2_hidden('#skF_4'(A_14, B_15, C_16), B_15) | r2_hidden('#skF_5'(A_14, B_15, C_16), C_16) | k4_xboole_0(A_14, B_15)=C_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.78/3.43  tff(c_11941, plain, (![A_5287, C_5288]: (r2_hidden('#skF_5'(A_5287, A_5287, C_5288), C_5288) | k4_xboole_0(A_5287, A_5287)=C_5288)), inference(resolution, [status(thm)], [c_11490, c_42])).
% 9.78/3.43  tff(c_11992, plain, (![A_5287]: (k4_xboole_0(A_5287, A_5287)=k1_xboole_0)), inference(resolution, [status(thm)], [c_11941, c_326])).
% 9.78/3.43  tff(c_50, plain, (![B_21]: (r1_tarski(B_21, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.78/3.43  tff(c_186, plain, (![B_21]: (k3_xboole_0(B_21, B_21)=B_21)), inference(resolution, [status(thm)], [c_50, c_175])).
% 9.78/3.43  tff(c_401, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k4_xboole_0(B_21, B_21))), inference(superposition, [status(thm), theory('equality')], [c_186, c_386])).
% 9.78/3.43  tff(c_11995, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11992, c_401])).
% 9.78/3.43  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.78/3.43  tff(c_481, plain, (![D_95, A_96, B_97]: (r2_hidden(D_95, A_96) | ~r2_hidden(D_95, k3_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.78/3.43  tff(c_13486, plain, (![A_5389, B_5390, B_5391]: (r2_hidden('#skF_1'(k3_xboole_0(A_5389, B_5390), B_5391), A_5389) | r1_tarski(k3_xboole_0(A_5389, B_5390), B_5391))), inference(resolution, [status(thm)], [c_8, c_481])).
% 9.78/3.43  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.78/3.43  tff(c_13573, plain, (![A_5392, B_5393]: (r1_tarski(k3_xboole_0(A_5392, B_5393), A_5392))), inference(resolution, [status(thm)], [c_13486, c_6])).
% 9.78/3.43  tff(c_54, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.78/3.43  tff(c_13720, plain, (![A_5396, B_5397]: (k3_xboole_0(k3_xboole_0(A_5396, B_5397), A_5396)=k3_xboole_0(A_5396, B_5397))), inference(resolution, [status(thm)], [c_13573, c_54])).
% 9.78/3.43  tff(c_52, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.78/3.43  tff(c_13754, plain, (![A_5396, B_5397]: (k5_xboole_0(k3_xboole_0(A_5396, B_5397), k3_xboole_0(A_5396, B_5397))=k4_xboole_0(k3_xboole_0(A_5396, B_5397), A_5396))), inference(superposition, [status(thm), theory('equality')], [c_13720, c_52])).
% 9.78/3.43  tff(c_13831, plain, (![A_5398, B_5399]: (k4_xboole_0(k3_xboole_0(A_5398, B_5399), A_5398)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11995, c_13754])).
% 9.78/3.43  tff(c_19916, plain, (![B_5509, B_5510]: (k3_xboole_0(k1_tarski(B_5509), B_5510)=k1_xboole_0 | r2_hidden(B_5509, k3_xboole_0(k1_tarski(B_5509), B_5510)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_13831])).
% 9.78/3.43  tff(c_12, plain, (![D_13, B_9, A_8]: (r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.78/3.43  tff(c_19989, plain, (![B_5511, B_5512]: (r2_hidden(B_5511, B_5512) | k3_xboole_0(k1_tarski(B_5511), B_5512)=k1_xboole_0)), inference(resolution, [status(thm)], [c_19916, c_12])).
% 9.78/3.43  tff(c_20156, plain, (![B_5511, B_5512]: (k5_xboole_0(k1_tarski(B_5511), k1_xboole_0)=k4_xboole_0(k1_tarski(B_5511), B_5512) | r2_hidden(B_5511, B_5512))), inference(superposition, [status(thm), theory('equality')], [c_19989, c_52])).
% 9.78/3.43  tff(c_20957, plain, (![B_5524, B_5525]: (k4_xboole_0(k1_tarski(B_5524), B_5525)=k1_tarski(B_5524) | r2_hidden(B_5524, B_5525))), inference(demodulation, [status(thm), theory('equality')], [c_17153, c_20156])).
% 9.78/3.43  tff(c_94, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_tarski('#skF_8') | r2_hidden('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.78/3.43  tff(c_271, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_tarski('#skF_8')), inference(splitLeft, [status(thm)], [c_94])).
% 9.78/3.43  tff(c_21036, plain, (r2_hidden('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_20957, c_271])).
% 9.78/3.43  tff(c_21085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_21036])).
% 9.78/3.43  tff(c_21086, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_94])).
% 9.78/3.43  tff(c_84, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.78/3.43  tff(c_152, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.78/3.43  tff(c_62, plain, (![E_35, A_29, B_30]: (r2_hidden(E_35, k1_enumset1(A_29, B_30, E_35)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.78/3.43  tff(c_170, plain, (![B_62, A_63]: (r2_hidden(B_62, k2_tarski(A_63, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_62])).
% 9.78/3.43  tff(c_173, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_170])).
% 9.78/3.43  tff(c_21087, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_94])).
% 9.78/3.43  tff(c_98, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_tarski('#skF_8') | k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_tarski('#skF_10')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.78/3.43  tff(c_21088, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_tarski('#skF_8')), inference(splitLeft, [status(thm)], [c_98])).
% 9.78/3.43  tff(c_21107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21087, c_21088])).
% 9.78/3.43  tff(c_21108, plain, (k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_tarski('#skF_10')), inference(splitRight, [status(thm)], [c_98])).
% 9.78/3.43  tff(c_21275, plain, (![D_5551, B_5552, A_5553]: (~r2_hidden(D_5551, B_5552) | ~r2_hidden(D_5551, k4_xboole_0(A_5553, B_5552)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.78/3.43  tff(c_21332, plain, (![D_5556]: (~r2_hidden(D_5556, '#skF_11') | ~r2_hidden(D_5556, k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_21108, c_21275])).
% 9.78/3.43  tff(c_21336, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_173, c_21332])).
% 9.78/3.43  tff(c_21340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21086, c_21336])).
% 9.78/3.43  tff(c_21341, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_96])).
% 9.78/3.43  tff(c_21443, plain, (![A_5562, B_5563]: (k1_enumset1(A_5562, A_5562, B_5563)=k2_tarski(A_5562, B_5563))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.78/3.43  tff(c_21461, plain, (![B_5564, A_5565]: (r2_hidden(B_5564, k2_tarski(A_5565, B_5564)))), inference(superposition, [status(thm), theory('equality')], [c_21443, c_62])).
% 9.78/3.43  tff(c_21464, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_21461])).
% 9.78/3.43  tff(c_21342, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_96])).
% 9.78/3.43  tff(c_100, plain, (~r2_hidden('#skF_8', '#skF_9') | k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_tarski('#skF_10')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.78/3.43  tff(c_21474, plain, (k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_21342, c_100])).
% 9.78/3.43  tff(c_21715, plain, (![D_5595, B_5596, A_5597]: (~r2_hidden(D_5595, B_5596) | ~r2_hidden(D_5595, k4_xboole_0(A_5597, B_5596)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.78/3.43  tff(c_21730, plain, (![D_5598]: (~r2_hidden(D_5598, '#skF_11') | ~r2_hidden(D_5598, k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_21474, c_21715])).
% 9.78/3.43  tff(c_21738, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_21464, c_21730])).
% 9.78/3.43  tff(c_21743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21341, c_21738])).
% 9.78/3.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.78/3.43  
% 9.78/3.43  Inference rules
% 9.78/3.43  ----------------------
% 9.78/3.43  #Ref     : 0
% 9.78/3.43  #Sup     : 4392
% 9.78/3.43  #Fact    : 2
% 9.78/3.43  #Define  : 0
% 9.78/3.43  #Split   : 4
% 9.78/3.43  #Chain   : 0
% 9.78/3.43  #Close   : 0
% 9.78/3.43  
% 9.78/3.43  Ordering : KBO
% 9.78/3.43  
% 9.78/3.43  Simplification rules
% 9.78/3.43  ----------------------
% 9.78/3.43  #Subsume      : 1298
% 9.78/3.43  #Demod        : 2567
% 9.78/3.43  #Tautology    : 1298
% 9.78/3.43  #SimpNegUnit  : 148
% 9.78/3.43  #BackRed      : 8
% 9.78/3.43  
% 9.78/3.43  #Partial instantiations: 2508
% 9.78/3.43  #Strategies tried      : 1
% 9.78/3.43  
% 9.78/3.43  Timing (in seconds)
% 9.78/3.43  ----------------------
% 9.78/3.44  Preprocessing        : 0.32
% 9.78/3.44  Parsing              : 0.15
% 9.78/3.44  CNF conversion       : 0.03
% 9.78/3.44  Main loop            : 2.29
% 9.78/3.44  Inferencing          : 0.70
% 9.78/3.44  Reduction            : 0.84
% 9.78/3.44  Demodulation         : 0.66
% 9.78/3.44  BG Simplification    : 0.08
% 9.78/3.44  Subsumption          : 0.49
% 9.78/3.44  Abstraction          : 0.14
% 9.78/3.44  MUC search           : 0.00
% 9.78/3.44  Cooper               : 0.00
% 9.78/3.44  Total                : 2.65
% 9.78/3.44  Index Insertion      : 0.00
% 9.78/3.44  Index Deletion       : 0.00
% 9.78/3.44  Index Matching       : 0.00
% 9.78/3.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

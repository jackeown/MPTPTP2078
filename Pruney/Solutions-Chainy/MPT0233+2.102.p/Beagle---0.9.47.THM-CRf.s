%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:34 EST 2020

% Result     : Theorem 9.17s
% Output     : CNFRefutation 9.17s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 138 expanded)
%              Number of leaves         :   41 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :   94 ( 153 expanded)
%              Number of equality atoms :   71 ( 109 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_72,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(c_68,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_66,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_62,B_63] : r1_tarski(k1_tarski(A_62),k2_tarski(A_62,B_63)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_197,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_210,plain,(
    ! [A_62,B_63] : k3_xboole_0(k1_tarski(A_62),k2_tarski(A_62,B_63)) = k1_tarski(A_62) ),
    inference(resolution,[status(thm)],[c_64,c_197])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
    ! [B_83,A_84] : k3_xboole_0(B_83,A_84) = k3_xboole_0(A_84,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_284,plain,(
    ! [B_89,A_90] : r1_tarski(k3_xboole_0(B_89,A_90),A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_8])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1724,plain,(
    ! [B_168,A_169] : k3_xboole_0(k3_xboole_0(B_168,A_169),A_169) = k3_xboole_0(B_168,A_169) ),
    inference(resolution,[status(thm)],[c_284,c_12])).

tff(c_2841,plain,(
    ! [A_191,B_192] : k3_xboole_0(k3_xboole_0(A_191,B_192),A_191) = k3_xboole_0(B_192,A_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1724])).

tff(c_2996,plain,(
    ! [A_62,B_63] : k3_xboole_0(k2_tarski(A_62,B_63),k1_tarski(A_62)) = k3_xboole_0(k1_tarski(A_62),k1_tarski(A_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_2841])).

tff(c_3065,plain,(
    ! [A_62,B_63] : k3_xboole_0(k2_tarski(A_62,B_63),k1_tarski(A_62)) = k1_tarski(A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2996])).

tff(c_70,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_211,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_197])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [A_70] :
      ( k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    ! [B_8] : k3_xboole_0(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_160,plain,(
    ! [B_83] : k3_xboole_0(B_83,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_114])).

tff(c_499,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_511,plain,(
    ! [B_83] : k5_xboole_0(B_83,k1_xboole_0) = k4_xboole_0(B_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_499])).

tff(c_553,plain,(
    ! [B_110] : k4_xboole_0(B_110,k1_xboole_0) = B_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_511])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_563,plain,(
    ! [B_110] : k4_xboole_0(B_110,B_110) = k3_xboole_0(B_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_16])).

tff(c_576,plain,(
    ! [B_110] : k4_xboole_0(B_110,B_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_563])).

tff(c_712,plain,(
    ! [A_116,B_117,C_118] :
      ( r1_tarski(A_116,B_117)
      | ~ r1_tarski(A_116,k3_xboole_0(B_117,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_774,plain,(
    ! [B_121,C_122,B_123] : r1_tarski(k3_xboole_0(k3_xboole_0(B_121,C_122),B_123),B_121) ),
    inference(resolution,[status(thm)],[c_8,c_712])).

tff(c_14889,plain,(
    ! [B_479,C_480,B_481] : k3_xboole_0(k3_xboole_0(k3_xboole_0(B_479,C_480),B_481),B_479) = k3_xboole_0(k3_xboole_0(B_479,C_480),B_481) ),
    inference(resolution,[status(thm)],[c_774,c_12])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1263,plain,(
    ! [A_150,B_151] : k3_xboole_0(k3_xboole_0(A_150,B_151),A_150) = k3_xboole_0(A_150,B_151) ),
    inference(resolution,[status(thm)],[c_8,c_197])).

tff(c_517,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_499])).

tff(c_1272,plain,(
    ! [A_150,B_151] : k5_xboole_0(A_150,k3_xboole_0(A_150,B_151)) = k4_xboole_0(A_150,k3_xboole_0(A_150,B_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1263,c_517])).

tff(c_1365,plain,(
    ! [A_150,B_151] : k4_xboole_0(A_150,k3_xboole_0(A_150,B_151)) = k4_xboole_0(A_150,B_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1272])).

tff(c_15201,plain,(
    ! [B_479,C_480,B_481] : k4_xboole_0(k3_xboole_0(k3_xboole_0(B_479,C_480),B_481),k3_xboole_0(k3_xboole_0(B_479,C_480),B_481)) = k4_xboole_0(k3_xboole_0(k3_xboole_0(B_479,C_480),B_481),B_479) ),
    inference(superposition,[status(thm),theory(equality)],[c_14889,c_1365])).

tff(c_15535,plain,(
    ! [B_482,C_483,B_484] : k4_xboole_0(k3_xboole_0(k3_xboole_0(B_482,C_483),B_484),B_482) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_15201])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_15661,plain,(
    ! [B_482,C_483,B_484] : k2_xboole_0(B_482,k3_xboole_0(k3_xboole_0(B_482,C_483),B_484)) = k5_xboole_0(B_482,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15535,c_20])).

tff(c_15869,plain,(
    ! [B_485,C_486,B_487] : k2_xboole_0(B_485,k3_xboole_0(k3_xboole_0(B_485,C_486),B_487)) = B_485 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_15661])).

tff(c_19829,plain,(
    ! [A_529,B_530,B_531] : k2_xboole_0(A_529,k3_xboole_0(k3_xboole_0(B_530,A_529),B_531)) = A_529 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15869])).

tff(c_20025,plain,(
    ! [B_532] : k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k3_xboole_0(k2_tarski('#skF_3','#skF_4'),B_532)) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_19829])).

tff(c_20049,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_3')) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3065,c_20025])).

tff(c_52,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2325,plain,(
    ! [A_176,B_177,C_178,D_179] : k2_xboole_0(k1_enumset1(A_176,B_177,C_178),k1_tarski(D_179)) = k2_enumset1(A_176,B_177,C_178,D_179) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2343,plain,(
    ! [A_32,B_33,D_179] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(D_179)) = k2_enumset1(A_32,A_32,B_33,D_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2325])).

tff(c_2346,plain,(
    ! [A_32,B_33,D_179] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(D_179)) = k1_enumset1(A_32,B_33,D_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2343])).

tff(c_20109,plain,(
    k1_enumset1('#skF_5','#skF_6','#skF_3') = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_20049,c_2346])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20148,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20109,c_24])).

tff(c_338,plain,(
    ! [A_93,C_94,B_95] : k1_enumset1(A_93,C_94,B_95) = k1_enumset1(A_93,B_95,C_94) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_391,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,B_33,A_32) = k2_tarski(A_32,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_338])).

tff(c_1633,plain,(
    ! [E_161,C_162,B_163,A_164] :
      ( E_161 = C_162
      | E_161 = B_163
      | E_161 = A_164
      | ~ r2_hidden(E_161,k1_enumset1(A_164,B_163,C_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1636,plain,(
    ! [E_161,A_32,B_33] :
      ( E_161 = A_32
      | E_161 = B_33
      | E_161 = A_32
      | ~ r2_hidden(E_161,k2_tarski(A_32,B_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_1633])).

tff(c_20173,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20148,c_1636])).

tff(c_20180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_66,c_68,c_20173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n017.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:34:46 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.17/3.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.17/3.55  
% 9.17/3.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.17/3.55  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 9.17/3.55  
% 9.17/3.55  %Foreground sorts:
% 9.17/3.55  
% 9.17/3.55  
% 9.17/3.55  %Background operators:
% 9.17/3.55  
% 9.17/3.55  
% 9.17/3.55  %Foreground operators:
% 9.17/3.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.17/3.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.17/3.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.17/3.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.17/3.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.17/3.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.17/3.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.17/3.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.17/3.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.17/3.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.17/3.55  tff('#skF_5', type, '#skF_5': $i).
% 9.17/3.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.17/3.55  tff('#skF_6', type, '#skF_6': $i).
% 9.17/3.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.17/3.55  tff('#skF_3', type, '#skF_3': $i).
% 9.17/3.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.17/3.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.17/3.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.17/3.55  tff('#skF_4', type, '#skF_4': $i).
% 9.17/3.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.17/3.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.17/3.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.17/3.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.17/3.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.17/3.55  
% 9.17/3.57  tff(f_96, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 9.17/3.57  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.17/3.57  tff(f_86, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 9.17/3.57  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.17/3.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.17/3.57  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.17/3.57  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 9.17/3.57  tff(f_45, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.17/3.57  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.17/3.57  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.17/3.57  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 9.17/3.57  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.17/3.57  tff(f_74, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 9.17/3.57  tff(f_72, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.17/3.57  tff(f_68, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 9.17/3.57  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.17/3.57  tff(f_84, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 9.17/3.57  tff(c_68, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.17/3.57  tff(c_66, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.17/3.57  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.17/3.57  tff(c_64, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), k2_tarski(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.17/3.57  tff(c_197, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.17/3.57  tff(c_210, plain, (![A_62, B_63]: (k3_xboole_0(k1_tarski(A_62), k2_tarski(A_62, B_63))=k1_tarski(A_62))), inference(resolution, [status(thm)], [c_64, c_197])).
% 9.17/3.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.17/3.57  tff(c_144, plain, (![B_83, A_84]: (k3_xboole_0(B_83, A_84)=k3_xboole_0(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.17/3.57  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.17/3.57  tff(c_284, plain, (![B_89, A_90]: (r1_tarski(k3_xboole_0(B_89, A_90), A_90))), inference(superposition, [status(thm), theory('equality')], [c_144, c_8])).
% 9.17/3.57  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.17/3.57  tff(c_1724, plain, (![B_168, A_169]: (k3_xboole_0(k3_xboole_0(B_168, A_169), A_169)=k3_xboole_0(B_168, A_169))), inference(resolution, [status(thm)], [c_284, c_12])).
% 9.17/3.57  tff(c_2841, plain, (![A_191, B_192]: (k3_xboole_0(k3_xboole_0(A_191, B_192), A_191)=k3_xboole_0(B_192, A_191))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1724])).
% 9.17/3.57  tff(c_2996, plain, (![A_62, B_63]: (k3_xboole_0(k2_tarski(A_62, B_63), k1_tarski(A_62))=k3_xboole_0(k1_tarski(A_62), k1_tarski(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_2841])).
% 9.17/3.57  tff(c_3065, plain, (![A_62, B_63]: (k3_xboole_0(k2_tarski(A_62, B_63), k1_tarski(A_62))=k1_tarski(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2996])).
% 9.17/3.57  tff(c_70, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.17/3.57  tff(c_211, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_197])).
% 9.17/3.57  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.17/3.57  tff(c_103, plain, (![A_70]: (k1_xboole_0=A_70 | ~r1_tarski(A_70, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.17/3.57  tff(c_114, plain, (![B_8]: (k3_xboole_0(k1_xboole_0, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_103])).
% 9.17/3.57  tff(c_160, plain, (![B_83]: (k3_xboole_0(B_83, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_144, c_114])).
% 9.17/3.57  tff(c_499, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.17/3.57  tff(c_511, plain, (![B_83]: (k5_xboole_0(B_83, k1_xboole_0)=k4_xboole_0(B_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_160, c_499])).
% 9.17/3.57  tff(c_553, plain, (![B_110]: (k4_xboole_0(B_110, k1_xboole_0)=B_110)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_511])).
% 9.17/3.57  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.17/3.57  tff(c_563, plain, (![B_110]: (k4_xboole_0(B_110, B_110)=k3_xboole_0(B_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_553, c_16])).
% 9.17/3.57  tff(c_576, plain, (![B_110]: (k4_xboole_0(B_110, B_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_563])).
% 9.17/3.57  tff(c_712, plain, (![A_116, B_117, C_118]: (r1_tarski(A_116, B_117) | ~r1_tarski(A_116, k3_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.17/3.57  tff(c_774, plain, (![B_121, C_122, B_123]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_121, C_122), B_123), B_121))), inference(resolution, [status(thm)], [c_8, c_712])).
% 9.17/3.57  tff(c_14889, plain, (![B_479, C_480, B_481]: (k3_xboole_0(k3_xboole_0(k3_xboole_0(B_479, C_480), B_481), B_479)=k3_xboole_0(k3_xboole_0(B_479, C_480), B_481))), inference(resolution, [status(thm)], [c_774, c_12])).
% 9.17/3.57  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.17/3.57  tff(c_1263, plain, (![A_150, B_151]: (k3_xboole_0(k3_xboole_0(A_150, B_151), A_150)=k3_xboole_0(A_150, B_151))), inference(resolution, [status(thm)], [c_8, c_197])).
% 9.17/3.57  tff(c_517, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_499])).
% 9.17/3.57  tff(c_1272, plain, (![A_150, B_151]: (k5_xboole_0(A_150, k3_xboole_0(A_150, B_151))=k4_xboole_0(A_150, k3_xboole_0(A_150, B_151)))), inference(superposition, [status(thm), theory('equality')], [c_1263, c_517])).
% 9.17/3.57  tff(c_1365, plain, (![A_150, B_151]: (k4_xboole_0(A_150, k3_xboole_0(A_150, B_151))=k4_xboole_0(A_150, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1272])).
% 9.17/3.57  tff(c_15201, plain, (![B_479, C_480, B_481]: (k4_xboole_0(k3_xboole_0(k3_xboole_0(B_479, C_480), B_481), k3_xboole_0(k3_xboole_0(B_479, C_480), B_481))=k4_xboole_0(k3_xboole_0(k3_xboole_0(B_479, C_480), B_481), B_479))), inference(superposition, [status(thm), theory('equality')], [c_14889, c_1365])).
% 9.17/3.57  tff(c_15535, plain, (![B_482, C_483, B_484]: (k4_xboole_0(k3_xboole_0(k3_xboole_0(B_482, C_483), B_484), B_482)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_576, c_15201])).
% 9.17/3.57  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.17/3.57  tff(c_15661, plain, (![B_482, C_483, B_484]: (k2_xboole_0(B_482, k3_xboole_0(k3_xboole_0(B_482, C_483), B_484))=k5_xboole_0(B_482, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15535, c_20])).
% 9.17/3.57  tff(c_15869, plain, (![B_485, C_486, B_487]: (k2_xboole_0(B_485, k3_xboole_0(k3_xboole_0(B_485, C_486), B_487))=B_485)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_15661])).
% 9.17/3.57  tff(c_19829, plain, (![A_529, B_530, B_531]: (k2_xboole_0(A_529, k3_xboole_0(k3_xboole_0(B_530, A_529), B_531))=A_529)), inference(superposition, [status(thm), theory('equality')], [c_2, c_15869])).
% 9.17/3.57  tff(c_20025, plain, (![B_532]: (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), B_532))=k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_19829])).
% 9.17/3.57  tff(c_20049, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_3'))=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3065, c_20025])).
% 9.17/3.57  tff(c_52, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.17/3.57  tff(c_50, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.17/3.57  tff(c_2325, plain, (![A_176, B_177, C_178, D_179]: (k2_xboole_0(k1_enumset1(A_176, B_177, C_178), k1_tarski(D_179))=k2_enumset1(A_176, B_177, C_178, D_179))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.17/3.57  tff(c_2343, plain, (![A_32, B_33, D_179]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(D_179))=k2_enumset1(A_32, A_32, B_33, D_179))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2325])).
% 9.17/3.57  tff(c_2346, plain, (![A_32, B_33, D_179]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(D_179))=k1_enumset1(A_32, B_33, D_179))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2343])).
% 9.17/3.57  tff(c_20109, plain, (k1_enumset1('#skF_5', '#skF_6', '#skF_3')=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_20049, c_2346])).
% 9.17/3.57  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.17/3.57  tff(c_20148, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20109, c_24])).
% 9.17/3.57  tff(c_338, plain, (![A_93, C_94, B_95]: (k1_enumset1(A_93, C_94, B_95)=k1_enumset1(A_93, B_95, C_94))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.17/3.57  tff(c_391, plain, (![A_32, B_33]: (k1_enumset1(A_32, B_33, A_32)=k2_tarski(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_50, c_338])).
% 9.17/3.57  tff(c_1633, plain, (![E_161, C_162, B_163, A_164]: (E_161=C_162 | E_161=B_163 | E_161=A_164 | ~r2_hidden(E_161, k1_enumset1(A_164, B_163, C_162)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.17/3.57  tff(c_1636, plain, (![E_161, A_32, B_33]: (E_161=A_32 | E_161=B_33 | E_161=A_32 | ~r2_hidden(E_161, k2_tarski(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_391, c_1633])).
% 9.17/3.57  tff(c_20173, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_20148, c_1636])).
% 9.17/3.57  tff(c_20180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_66, c_68, c_20173])).
% 9.17/3.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.17/3.57  
% 9.17/3.57  Inference rules
% 9.17/3.57  ----------------------
% 9.17/3.57  #Ref     : 0
% 9.17/3.57  #Sup     : 4790
% 9.17/3.57  #Fact    : 6
% 9.17/3.57  #Define  : 0
% 9.17/3.57  #Split   : 0
% 9.17/3.57  #Chain   : 0
% 9.17/3.57  #Close   : 0
% 9.17/3.57  
% 9.17/3.57  Ordering : KBO
% 9.17/3.57  
% 9.17/3.57  Simplification rules
% 9.17/3.57  ----------------------
% 9.17/3.57  #Subsume      : 91
% 9.17/3.57  #Demod        : 5643
% 9.17/3.57  #Tautology    : 3753
% 9.17/3.57  #SimpNegUnit  : 1
% 9.17/3.57  #BackRed      : 1
% 9.17/3.57  
% 9.17/3.57  #Partial instantiations: 0
% 9.17/3.58  #Strategies tried      : 1
% 9.17/3.58  
% 9.17/3.58  Timing (in seconds)
% 9.17/3.58  ----------------------
% 9.17/3.58  Preprocessing        : 0.34
% 9.17/3.58  Parsing              : 0.18
% 9.17/3.58  CNF conversion       : 0.02
% 9.17/3.58  Main loop            : 2.47
% 9.17/3.58  Inferencing          : 0.52
% 9.17/3.58  Reduction            : 1.36
% 9.17/3.58  Demodulation         : 1.19
% 9.17/3.58  BG Simplification    : 0.06
% 9.17/3.58  Subsumption          : 0.41
% 9.17/3.58  Abstraction          : 0.10
% 9.17/3.58  MUC search           : 0.00
% 9.17/3.58  Cooper               : 0.00
% 9.17/3.58  Total                : 2.85
% 9.17/3.58  Index Insertion      : 0.00
% 9.17/3.58  Index Deletion       : 0.00
% 9.17/3.58  Index Matching       : 0.00
% 9.17/3.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------

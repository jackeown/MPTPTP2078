%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:29 EST 2020

% Result     : Theorem 9.57s
% Output     : CNFRefutation 9.57s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 244 expanded)
%              Number of leaves         :   53 ( 105 expanded)
%              Depth                    :   16
%              Number of atoms          :  187 ( 414 expanded)
%              Number of equality atoms :   33 (  83 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_153,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_135,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_68,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_97,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_95,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_131,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_80,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_112,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_142,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_92,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_90,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_88,plain,(
    r1_tarski('#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_82,plain,(
    ! [A_76,B_78] :
      ( r1_tarski(k2_relat_1(A_76),k2_relat_1(B_78))
      | ~ r1_tarski(A_76,B_78)
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_583,plain,(
    ! [A_158] :
      ( k2_xboole_0(k1_relat_1(A_158),k2_relat_1(A_158)) = k3_relat_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_22,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,k2_xboole_0(C_13,B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_592,plain,(
    ! [A_11,A_158] :
      ( r1_tarski(A_11,k3_relat_1(A_158))
      | ~ r1_tarski(A_11,k2_relat_1(A_158))
      | ~ v1_relat_1(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_22])).

tff(c_78,plain,(
    ! [A_72] :
      ( k2_xboole_0(k1_relat_1(A_72),k2_relat_1(A_72)) = k3_relat_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1079,plain,(
    ! [A_212,C_213,B_214] :
      ( r1_tarski(k2_xboole_0(A_212,C_213),B_214)
      | ~ r1_tarski(C_213,B_214)
      | ~ r1_tarski(A_212,B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7130,plain,(
    ! [A_460,B_461] :
      ( r1_tarski(k3_relat_1(A_460),B_461)
      | ~ r1_tarski(k2_relat_1(A_460),B_461)
      | ~ r1_tarski(k1_relat_1(A_460),B_461)
      | ~ v1_relat_1(A_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1079])).

tff(c_86,plain,(
    ~ r1_tarski(k3_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_7208,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_7130,c_86])).

tff(c_7237,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_7208])).

tff(c_8552,plain,(
    ~ r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_7237])).

tff(c_26,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ! [A_27,C_29,B_28] :
      ( r1_tarski(k2_xboole_0(A_27,C_29),B_28)
      | ~ r1_tarski(C_29,B_28)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_707,plain,(
    ! [A_179,B_180,C_181] :
      ( r1_tarski(A_179,k2_xboole_0(B_180,C_181))
      | ~ r1_tarski(k4_xboole_0(A_179,B_180),C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_748,plain,(
    ! [A_182,B_183] : r1_tarski(A_182,k2_xboole_0(B_183,A_182)) ),
    inference(resolution,[status(thm)],[c_28,c_707])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5386,plain,(
    ! [B_451,A_452] :
      ( k2_xboole_0(B_451,A_452) = A_452
      | ~ r1_tarski(k2_xboole_0(B_451,A_452),A_452) ) ),
    inference(resolution,[status(thm)],[c_748,c_16])).

tff(c_5421,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(B_28,B_28)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_36,c_5386])).

tff(c_5452,plain,(
    ! [A_453,B_454] :
      ( k2_xboole_0(A_453,B_454) = B_454
      | ~ r1_tarski(A_453,B_454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5421])).

tff(c_5688,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_26,c_5452])).

tff(c_38,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_148,plain,(
    ! [A_92,B_93] : k3_tarski(k2_tarski(A_92,B_93)) = k2_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_175,plain,(
    ! [B_100,A_101] : k3_tarski(k2_tarski(B_100,A_101)) = k2_xboole_0(A_101,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_148])).

tff(c_52,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_181,plain,(
    ! [B_100,A_101] : k2_xboole_0(B_100,A_101) = k2_xboole_0(A_101,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_52])).

tff(c_1817,plain,(
    ! [A_261,B_262] :
      ( r2_hidden('#skF_1'(A_261,B_262),B_262)
      | r2_hidden('#skF_2'(A_261,B_262),A_261)
      | B_262 = A_261 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [C_36] : r2_hidden(C_36,k1_tarski(C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_355,plain,(
    ! [C_124,A_125,D_126] :
      ( r2_hidden(C_124,k1_relat_1(A_125))
      | ~ r2_hidden(k4_tarski(C_124,D_126),A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_360,plain,(
    ! [C_124,D_126] : r2_hidden(C_124,k1_relat_1(k1_tarski(k4_tarski(C_124,D_126)))) ),
    inference(resolution,[status(thm)],[c_42,c_355])).

tff(c_56,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_6'(A_39,B_40),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_34,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_491,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r1_xboole_0(A_143,B_144)
      | ~ r2_hidden(C_145,B_144)
      | ~ r2_hidden(C_145,A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_495,plain,(
    ! [C_146,A_147] :
      ( ~ r2_hidden(C_146,k1_xboole_0)
      | ~ r2_hidden(C_146,A_147) ) ),
    inference(resolution,[status(thm)],[c_34,c_491])).

tff(c_547,plain,(
    ! [A_154,A_155] :
      ( ~ r2_hidden('#skF_6'(A_154,k1_xboole_0),A_155)
      | ~ r2_hidden(A_154,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_56,c_495])).

tff(c_558,plain,(
    ! [A_154] : ~ r2_hidden(A_154,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_360,c_547])).

tff(c_1863,plain,(
    ! [B_262] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_262),B_262)
      | k1_xboole_0 = B_262 ) ),
    inference(resolution,[status(thm)],[c_1817,c_558])).

tff(c_3631,plain,(
    ! [C_358,A_359] :
      ( r2_hidden(k4_tarski(C_358,'#skF_10'(A_359,k1_relat_1(A_359),C_358)),A_359)
      | ~ r2_hidden(C_358,k1_relat_1(A_359)) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3661,plain,(
    ! [C_360] : ~ r2_hidden(C_360,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3631,c_558])).

tff(c_3701,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1863,c_3661])).

tff(c_6322,plain,(
    ! [A_458] : k2_xboole_0(k1_xboole_0,A_458) = A_458 ),
    inference(resolution,[status(thm)],[c_26,c_5452])).

tff(c_6582,plain,(
    ! [A_101] : k2_xboole_0(A_101,k1_xboole_0) = A_101 ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_6322])).

tff(c_881,plain,(
    ! [A_195,B_196,C_197] :
      ( r1_tarski(k4_xboole_0(A_195,B_196),C_197)
      | ~ r1_tarski(A_195,k2_xboole_0(B_196,C_197)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9796,plain,(
    ! [A_498,B_499,C_500] :
      ( k4_xboole_0(A_498,B_499) = C_500
      | ~ r1_tarski(C_500,k4_xboole_0(A_498,B_499))
      | ~ r1_tarski(A_498,k2_xboole_0(B_499,C_500)) ) ),
    inference(resolution,[status(thm)],[c_881,c_16])).

tff(c_9827,plain,(
    ! [A_498,B_499] :
      ( k4_xboole_0(A_498,B_499) = k1_xboole_0
      | ~ r1_tarski(A_498,k2_xboole_0(B_499,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_26,c_9796])).

tff(c_9844,plain,(
    ! [A_501,B_502] :
      ( k4_xboole_0(A_501,B_502) = k1_xboole_0
      | ~ r1_tarski(A_501,B_502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6582,c_9827])).

tff(c_10062,plain,(
    k4_xboole_0('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_9844])).

tff(c_58,plain,(
    ! [A_46,B_47] : k6_subset_1(A_46,B_47) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_80,plain,(
    ! [A_73,B_75] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_73),k1_relat_1(B_75)),k1_relat_1(k6_subset_1(A_73,B_75)))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4106,plain,(
    ! [A_377,B_378] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_377),k1_relat_1(B_378)),k1_relat_1(k4_xboole_0(A_377,B_378)))
      | ~ v1_relat_1(B_378)
      | ~ v1_relat_1(A_377) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_80])).

tff(c_32,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,k2_xboole_0(B_24,C_25))
      | ~ r1_tarski(k4_xboole_0(A_23,B_24),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4126,plain,(
    ! [A_377,B_378] :
      ( r1_tarski(k1_relat_1(A_377),k2_xboole_0(k1_relat_1(B_378),k1_relat_1(k4_xboole_0(A_377,B_378))))
      | ~ v1_relat_1(B_378)
      | ~ v1_relat_1(A_377) ) ),
    inference(resolution,[status(thm)],[c_4106,c_32])).

tff(c_10075,plain,
    ( r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),k1_relat_1(k1_xboole_0)))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_10062,c_4126])).

tff(c_10187,plain,(
    r1_tarski(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_5688,c_181,c_3701,c_10075])).

tff(c_5449,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5421])).

tff(c_10820,plain,(
    k2_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')) = k1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_10187,c_5449])).

tff(c_367,plain,(
    ! [A_129,C_130,B_131] :
      ( r1_tarski(A_129,C_130)
      | ~ r1_tarski(B_131,C_130)
      | ~ r1_tarski(A_129,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_434,plain,(
    ! [A_137,A_138,B_139] :
      ( r1_tarski(A_137,A_138)
      | ~ r1_tarski(A_137,k4_xboole_0(A_138,B_139)) ) ),
    inference(resolution,[status(thm)],[c_28,c_367])).

tff(c_450,plain,(
    ! [A_138,B_139,B_19] : r1_tarski(k4_xboole_0(k4_xboole_0(A_138,B_139),B_19),A_138) ),
    inference(resolution,[status(thm)],[c_28,c_434])).

tff(c_983,plain,(
    ! [A_203,B_204,B_205] : r1_tarski(k4_xboole_0(A_203,B_204),k2_xboole_0(B_205,A_203)) ),
    inference(resolution,[status(thm)],[c_450,c_707])).

tff(c_1046,plain,(
    ! [A_209,B_210,B_211] : r1_tarski(A_209,k2_xboole_0(B_210,k2_xboole_0(B_211,A_209))) ),
    inference(resolution,[status(thm)],[c_983,c_32])).

tff(c_1159,plain,(
    ! [A_218,B_219,B_220] : r1_tarski(A_218,k2_xboole_0(k2_xboole_0(B_219,A_218),B_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1046])).

tff(c_1176,plain,(
    ! [B_100,A_101,B_220] : r1_tarski(B_100,k2_xboole_0(k2_xboole_0(B_100,A_101),B_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1159])).

tff(c_14051,plain,(
    ! [B_546] : r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),B_546)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10820,c_1176])).

tff(c_14105,plain,
    ( r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_14051])).

tff(c_14134,plain,(
    r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_14105])).

tff(c_14136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8552,c_14134])).

tff(c_14137,plain,(
    ~ r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_7237])).

tff(c_14141,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_11'),k2_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_592,c_14137])).

tff(c_14144,plain,(
    ~ r1_tarski(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_14141])).

tff(c_14394,plain,
    ( ~ r1_tarski('#skF_11','#skF_12')
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_14144])).

tff(c_14398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_14394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:28:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.57/3.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.57/3.72  
% 9.57/3.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.57/3.72  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10
% 9.57/3.72  
% 9.57/3.72  %Foreground sorts:
% 9.57/3.72  
% 9.57/3.72  
% 9.57/3.72  %Background operators:
% 9.57/3.72  
% 9.57/3.72  
% 9.57/3.72  %Foreground operators:
% 9.57/3.72  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.57/3.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.57/3.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.57/3.72  tff('#skF_11', type, '#skF_11': $i).
% 9.57/3.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.57/3.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.57/3.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.57/3.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.57/3.72  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 9.57/3.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.57/3.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.57/3.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.57/3.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.57/3.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.57/3.72  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.57/3.72  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 9.57/3.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.57/3.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.57/3.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.57/3.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.57/3.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.57/3.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.57/3.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.57/3.72  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 9.57/3.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.57/3.72  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 9.57/3.72  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.57/3.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.57/3.72  tff('#skF_12', type, '#skF_12': $i).
% 9.57/3.72  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.57/3.72  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 9.57/3.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.57/3.72  
% 9.57/3.74  tff(f_163, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 9.57/3.74  tff(f_153, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 9.57/3.74  tff(f_135, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 9.57/3.74  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 9.57/3.74  tff(f_86, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 9.57/3.74  tff(f_68, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.57/3.74  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.57/3.74  tff(f_70, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.57/3.74  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.57/3.74  tff(f_88, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.57/3.74  tff(f_97, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.57/3.74  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 9.57/3.74  tff(f_95, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.57/3.74  tff(f_131, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 9.57/3.74  tff(f_110, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 9.57/3.74  tff(f_80, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.57/3.74  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.57/3.74  tff(f_74, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 9.57/3.74  tff(f_112, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.57/3.74  tff(f_142, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 9.57/3.74  tff(f_66, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.57/3.74  tff(c_92, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.57/3.74  tff(c_90, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.57/3.74  tff(c_88, plain, (r1_tarski('#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.57/3.74  tff(c_82, plain, (![A_76, B_78]: (r1_tarski(k2_relat_1(A_76), k2_relat_1(B_78)) | ~r1_tarski(A_76, B_78) | ~v1_relat_1(B_78) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.57/3.74  tff(c_583, plain, (![A_158]: (k2_xboole_0(k1_relat_1(A_158), k2_relat_1(A_158))=k3_relat_1(A_158) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.57/3.74  tff(c_22, plain, (![A_11, C_13, B_12]: (r1_tarski(A_11, k2_xboole_0(C_13, B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.57/3.74  tff(c_592, plain, (![A_11, A_158]: (r1_tarski(A_11, k3_relat_1(A_158)) | ~r1_tarski(A_11, k2_relat_1(A_158)) | ~v1_relat_1(A_158))), inference(superposition, [status(thm), theory('equality')], [c_583, c_22])).
% 9.57/3.74  tff(c_78, plain, (![A_72]: (k2_xboole_0(k1_relat_1(A_72), k2_relat_1(A_72))=k3_relat_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.57/3.74  tff(c_1079, plain, (![A_212, C_213, B_214]: (r1_tarski(k2_xboole_0(A_212, C_213), B_214) | ~r1_tarski(C_213, B_214) | ~r1_tarski(A_212, B_214))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.57/3.74  tff(c_7130, plain, (![A_460, B_461]: (r1_tarski(k3_relat_1(A_460), B_461) | ~r1_tarski(k2_relat_1(A_460), B_461) | ~r1_tarski(k1_relat_1(A_460), B_461) | ~v1_relat_1(A_460))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1079])).
% 9.57/3.74  tff(c_86, plain, (~r1_tarski(k3_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.57/3.74  tff(c_7208, plain, (~r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_7130, c_86])).
% 9.57/3.74  tff(c_7237, plain, (~r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_7208])).
% 9.57/3.74  tff(c_8552, plain, (~r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_7237])).
% 9.57/3.74  tff(c_26, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.57/3.74  tff(c_20, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.57/3.74  tff(c_36, plain, (![A_27, C_29, B_28]: (r1_tarski(k2_xboole_0(A_27, C_29), B_28) | ~r1_tarski(C_29, B_28) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.57/3.74  tff(c_28, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.57/3.74  tff(c_707, plain, (![A_179, B_180, C_181]: (r1_tarski(A_179, k2_xboole_0(B_180, C_181)) | ~r1_tarski(k4_xboole_0(A_179, B_180), C_181))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.57/3.74  tff(c_748, plain, (![A_182, B_183]: (r1_tarski(A_182, k2_xboole_0(B_183, A_182)))), inference(resolution, [status(thm)], [c_28, c_707])).
% 9.57/3.74  tff(c_16, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.57/3.74  tff(c_5386, plain, (![B_451, A_452]: (k2_xboole_0(B_451, A_452)=A_452 | ~r1_tarski(k2_xboole_0(B_451, A_452), A_452))), inference(resolution, [status(thm)], [c_748, c_16])).
% 9.57/3.74  tff(c_5421, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(B_28, B_28) | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_36, c_5386])).
% 9.57/3.74  tff(c_5452, plain, (![A_453, B_454]: (k2_xboole_0(A_453, B_454)=B_454 | ~r1_tarski(A_453, B_454))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5421])).
% 9.57/3.74  tff(c_5688, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(resolution, [status(thm)], [c_26, c_5452])).
% 9.57/3.74  tff(c_38, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.57/3.74  tff(c_148, plain, (![A_92, B_93]: (k3_tarski(k2_tarski(A_92, B_93))=k2_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.57/3.74  tff(c_175, plain, (![B_100, A_101]: (k3_tarski(k2_tarski(B_100, A_101))=k2_xboole_0(A_101, B_100))), inference(superposition, [status(thm), theory('equality')], [c_38, c_148])).
% 9.57/3.74  tff(c_52, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.57/3.74  tff(c_181, plain, (![B_100, A_101]: (k2_xboole_0(B_100, A_101)=k2_xboole_0(A_101, B_100))), inference(superposition, [status(thm), theory('equality')], [c_175, c_52])).
% 9.57/3.74  tff(c_1817, plain, (![A_261, B_262]: (r2_hidden('#skF_1'(A_261, B_262), B_262) | r2_hidden('#skF_2'(A_261, B_262), A_261) | B_262=A_261)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.57/3.74  tff(c_42, plain, (![C_36]: (r2_hidden(C_36, k1_tarski(C_36)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.57/3.74  tff(c_355, plain, (![C_124, A_125, D_126]: (r2_hidden(C_124, k1_relat_1(A_125)) | ~r2_hidden(k4_tarski(C_124, D_126), A_125))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.57/3.74  tff(c_360, plain, (![C_124, D_126]: (r2_hidden(C_124, k1_relat_1(k1_tarski(k4_tarski(C_124, D_126)))))), inference(resolution, [status(thm)], [c_42, c_355])).
% 9.57/3.74  tff(c_56, plain, (![A_39, B_40]: (r2_hidden('#skF_6'(A_39, B_40), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.57/3.74  tff(c_34, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.57/3.74  tff(c_491, plain, (![A_143, B_144, C_145]: (~r1_xboole_0(A_143, B_144) | ~r2_hidden(C_145, B_144) | ~r2_hidden(C_145, A_143))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.57/3.74  tff(c_495, plain, (![C_146, A_147]: (~r2_hidden(C_146, k1_xboole_0) | ~r2_hidden(C_146, A_147))), inference(resolution, [status(thm)], [c_34, c_491])).
% 9.57/3.74  tff(c_547, plain, (![A_154, A_155]: (~r2_hidden('#skF_6'(A_154, k1_xboole_0), A_155) | ~r2_hidden(A_154, k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_495])).
% 9.57/3.74  tff(c_558, plain, (![A_154]: (~r2_hidden(A_154, k1_xboole_0))), inference(resolution, [status(thm)], [c_360, c_547])).
% 9.57/3.74  tff(c_1863, plain, (![B_262]: (r2_hidden('#skF_1'(k1_xboole_0, B_262), B_262) | k1_xboole_0=B_262)), inference(resolution, [status(thm)], [c_1817, c_558])).
% 9.57/3.74  tff(c_3631, plain, (![C_358, A_359]: (r2_hidden(k4_tarski(C_358, '#skF_10'(A_359, k1_relat_1(A_359), C_358)), A_359) | ~r2_hidden(C_358, k1_relat_1(A_359)))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.57/3.74  tff(c_3661, plain, (![C_360]: (~r2_hidden(C_360, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_3631, c_558])).
% 9.57/3.74  tff(c_3701, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1863, c_3661])).
% 9.57/3.74  tff(c_6322, plain, (![A_458]: (k2_xboole_0(k1_xboole_0, A_458)=A_458)), inference(resolution, [status(thm)], [c_26, c_5452])).
% 9.57/3.74  tff(c_6582, plain, (![A_101]: (k2_xboole_0(A_101, k1_xboole_0)=A_101)), inference(superposition, [status(thm), theory('equality')], [c_181, c_6322])).
% 9.57/3.74  tff(c_881, plain, (![A_195, B_196, C_197]: (r1_tarski(k4_xboole_0(A_195, B_196), C_197) | ~r1_tarski(A_195, k2_xboole_0(B_196, C_197)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.57/3.74  tff(c_9796, plain, (![A_498, B_499, C_500]: (k4_xboole_0(A_498, B_499)=C_500 | ~r1_tarski(C_500, k4_xboole_0(A_498, B_499)) | ~r1_tarski(A_498, k2_xboole_0(B_499, C_500)))), inference(resolution, [status(thm)], [c_881, c_16])).
% 9.57/3.74  tff(c_9827, plain, (![A_498, B_499]: (k4_xboole_0(A_498, B_499)=k1_xboole_0 | ~r1_tarski(A_498, k2_xboole_0(B_499, k1_xboole_0)))), inference(resolution, [status(thm)], [c_26, c_9796])).
% 9.57/3.74  tff(c_9844, plain, (![A_501, B_502]: (k4_xboole_0(A_501, B_502)=k1_xboole_0 | ~r1_tarski(A_501, B_502))), inference(demodulation, [status(thm), theory('equality')], [c_6582, c_9827])).
% 9.57/3.74  tff(c_10062, plain, (k4_xboole_0('#skF_11', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_9844])).
% 9.57/3.74  tff(c_58, plain, (![A_46, B_47]: (k6_subset_1(A_46, B_47)=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.57/3.74  tff(c_80, plain, (![A_73, B_75]: (r1_tarski(k6_subset_1(k1_relat_1(A_73), k1_relat_1(B_75)), k1_relat_1(k6_subset_1(A_73, B_75))) | ~v1_relat_1(B_75) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.57/3.74  tff(c_4106, plain, (![A_377, B_378]: (r1_tarski(k4_xboole_0(k1_relat_1(A_377), k1_relat_1(B_378)), k1_relat_1(k4_xboole_0(A_377, B_378))) | ~v1_relat_1(B_378) | ~v1_relat_1(A_377))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_80])).
% 9.57/3.74  tff(c_32, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, k2_xboole_0(B_24, C_25)) | ~r1_tarski(k4_xboole_0(A_23, B_24), C_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.57/3.74  tff(c_4126, plain, (![A_377, B_378]: (r1_tarski(k1_relat_1(A_377), k2_xboole_0(k1_relat_1(B_378), k1_relat_1(k4_xboole_0(A_377, B_378)))) | ~v1_relat_1(B_378) | ~v1_relat_1(A_377))), inference(resolution, [status(thm)], [c_4106, c_32])).
% 9.57/3.74  tff(c_10075, plain, (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), k1_relat_1(k1_xboole_0))) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_10062, c_4126])).
% 9.57/3.74  tff(c_10187, plain, (r1_tarski(k1_relat_1('#skF_11'), k1_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_5688, c_181, c_3701, c_10075])).
% 9.57/3.74  tff(c_5449, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5421])).
% 9.57/3.74  tff(c_10820, plain, (k2_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12'))=k1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_10187, c_5449])).
% 9.57/3.74  tff(c_367, plain, (![A_129, C_130, B_131]: (r1_tarski(A_129, C_130) | ~r1_tarski(B_131, C_130) | ~r1_tarski(A_129, B_131))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.57/3.74  tff(c_434, plain, (![A_137, A_138, B_139]: (r1_tarski(A_137, A_138) | ~r1_tarski(A_137, k4_xboole_0(A_138, B_139)))), inference(resolution, [status(thm)], [c_28, c_367])).
% 9.57/3.74  tff(c_450, plain, (![A_138, B_139, B_19]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_138, B_139), B_19), A_138))), inference(resolution, [status(thm)], [c_28, c_434])).
% 9.57/3.74  tff(c_983, plain, (![A_203, B_204, B_205]: (r1_tarski(k4_xboole_0(A_203, B_204), k2_xboole_0(B_205, A_203)))), inference(resolution, [status(thm)], [c_450, c_707])).
% 9.57/3.74  tff(c_1046, plain, (![A_209, B_210, B_211]: (r1_tarski(A_209, k2_xboole_0(B_210, k2_xboole_0(B_211, A_209))))), inference(resolution, [status(thm)], [c_983, c_32])).
% 9.57/3.74  tff(c_1159, plain, (![A_218, B_219, B_220]: (r1_tarski(A_218, k2_xboole_0(k2_xboole_0(B_219, A_218), B_220)))), inference(superposition, [status(thm), theory('equality')], [c_181, c_1046])).
% 9.57/3.74  tff(c_1176, plain, (![B_100, A_101, B_220]: (r1_tarski(B_100, k2_xboole_0(k2_xboole_0(B_100, A_101), B_220)))), inference(superposition, [status(thm), theory('equality')], [c_181, c_1159])).
% 9.57/3.74  tff(c_14051, plain, (![B_546]: (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), B_546)))), inference(superposition, [status(thm), theory('equality')], [c_10820, c_1176])).
% 9.57/3.74  tff(c_14105, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_78, c_14051])).
% 9.57/3.74  tff(c_14134, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_14105])).
% 9.57/3.74  tff(c_14136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8552, c_14134])).
% 9.57/3.74  tff(c_14137, plain, (~r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(splitRight, [status(thm)], [c_7237])).
% 9.57/3.74  tff(c_14141, plain, (~r1_tarski(k2_relat_1('#skF_11'), k2_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_592, c_14137])).
% 9.57/3.74  tff(c_14144, plain, (~r1_tarski(k2_relat_1('#skF_11'), k2_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_14141])).
% 9.57/3.74  tff(c_14394, plain, (~r1_tarski('#skF_11', '#skF_12') | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_82, c_14144])).
% 9.57/3.74  tff(c_14398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_14394])).
% 9.57/3.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.57/3.74  
% 9.57/3.74  Inference rules
% 9.57/3.74  ----------------------
% 9.57/3.74  #Ref     : 0
% 9.57/3.74  #Sup     : 3443
% 9.57/3.74  #Fact    : 0
% 9.57/3.74  #Define  : 0
% 9.57/3.74  #Split   : 11
% 9.57/3.74  #Chain   : 0
% 9.57/3.74  #Close   : 0
% 9.57/3.74  
% 9.57/3.74  Ordering : KBO
% 9.57/3.74  
% 9.57/3.74  Simplification rules
% 9.57/3.74  ----------------------
% 9.57/3.74  #Subsume      : 828
% 9.57/3.74  #Demod        : 2210
% 9.57/3.74  #Tautology    : 1397
% 9.57/3.74  #SimpNegUnit  : 27
% 9.57/3.74  #BackRed      : 25
% 9.57/3.74  
% 9.57/3.74  #Partial instantiations: 0
% 9.57/3.74  #Strategies tried      : 1
% 9.57/3.74  
% 9.57/3.74  Timing (in seconds)
% 9.57/3.74  ----------------------
% 9.57/3.74  Preprocessing        : 0.47
% 9.57/3.74  Parsing              : 0.18
% 9.57/3.74  CNF conversion       : 0.06
% 9.57/3.74  Main loop            : 2.42
% 9.57/3.74  Inferencing          : 0.55
% 9.57/3.74  Reduction            : 1.07
% 9.57/3.74  Demodulation         : 0.86
% 9.57/3.74  BG Simplification    : 0.07
% 9.57/3.74  Subsumption          : 0.57
% 9.57/3.74  Abstraction          : 0.09
% 9.57/3.74  MUC search           : 0.00
% 9.57/3.74  Cooper               : 0.00
% 9.57/3.74  Total                : 2.94
% 9.57/3.74  Index Insertion      : 0.00
% 9.57/3.74  Index Deletion       : 0.00
% 9.57/3.74  Index Matching       : 0.00
% 9.57/3.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------

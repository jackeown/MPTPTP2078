%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:04 EST 2020

% Result     : Theorem 12.04s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 249 expanded)
%              Number of leaves         :   34 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  147 ( 451 expanded)
%              Number of equality atoms :   38 ( 123 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_62,plain,(
    ! [A_31] : k1_subset_1(A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_70,plain,
    ( k1_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_78,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_70])).

tff(c_114,plain,(
    ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_324,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_77,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_76])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_96,plain,(
    ! [A_39,B_40] : r1_tarski(k4_xboole_0(A_39,B_40),A_39) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_101,plain,(
    ! [B_40] : k4_xboole_0(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_40])).

tff(c_116,plain,(
    ! [B_40] : k4_xboole_0('#skF_7',B_40) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_115,c_101])).

tff(c_208,plain,(
    ! [D_59,B_60,A_61] :
      ( ~ r2_hidden(D_59,B_60)
      | ~ r2_hidden(D_59,k4_xboole_0(A_61,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_211,plain,(
    ! [D_59,B_40] :
      ( ~ r2_hidden(D_59,B_40)
      | ~ r2_hidden(D_59,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_208])).

tff(c_382,plain,(
    ! [A_87,B_88] :
      ( ~ r2_hidden('#skF_1'(A_87,B_88),'#skF_7')
      | r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_324,c_211])).

tff(c_390,plain,(
    ! [B_2] : r1_tarski('#skF_7',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_382])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_114])).

tff(c_406,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_406])).

tff(c_410,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_823,plain,(
    ! [C_146,B_147,A_148] :
      ( r2_hidden(C_146,B_147)
      | ~ r2_hidden(C_146,A_148)
      | ~ r1_tarski(A_148,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_11869,plain,(
    ! [A_503,B_504,B_505] :
      ( r2_hidden('#skF_1'(A_503,B_504),B_505)
      | ~ r1_tarski(A_503,B_505)
      | r1_tarski(A_503,B_504) ) ),
    inference(resolution,[status(thm)],[c_6,c_823])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8020,plain,(
    ! [A_372,B_373] :
      ( k4_xboole_0(A_372,B_373) = k3_subset_1(A_372,B_373)
      | ~ m1_subset_1(B_373,k1_zfmisc_1(A_372)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8033,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_8020])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8049,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_7')
      | ~ r2_hidden(D_11,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8033,c_10])).

tff(c_30027,plain,(
    ! [A_822,B_823] :
      ( ~ r2_hidden('#skF_1'(A_822,B_823),'#skF_7')
      | ~ r1_tarski(A_822,k3_subset_1('#skF_6','#skF_7'))
      | r1_tarski(A_822,B_823) ) ),
    inference(resolution,[status(thm)],[c_11869,c_8049])).

tff(c_30054,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
      | r1_tarski('#skF_7',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_30027])).

tff(c_30063,plain,(
    ! [B_2] : r1_tarski('#skF_7',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_30054])).

tff(c_409,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    ! [A_34] : ~ v1_xboole_0(k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ! [C_28,A_24] :
      ( r2_hidden(C_28,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_477,plain,(
    ! [B_108,A_109] :
      ( m1_subset_1(B_108,A_109)
      | ~ r2_hidden(B_108,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_480,plain,(
    ! [C_28,A_24] :
      ( m1_subset_1(C_28,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(resolution,[status(thm)],[c_44,c_477])).

tff(c_483,plain,(
    ! [C_28,A_24] :
      ( m1_subset_1(C_28,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_480])).

tff(c_8244,plain,(
    ! [A_384,C_385] :
      ( k4_xboole_0(A_384,C_385) = k3_subset_1(A_384,C_385)
      | ~ r1_tarski(C_385,A_384) ) ),
    inference(resolution,[status(thm)],[c_483,c_8020])).

tff(c_8289,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = k3_subset_1(B_13,B_13) ),
    inference(resolution,[status(thm)],[c_30,c_8244])).

tff(c_489,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_1'(A_112,B_113),A_112)
      | r1_tarski(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_508,plain,(
    ! [A_6,B_7,B_113] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_113),A_6)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_113) ) ),
    inference(resolution,[status(thm)],[c_489,c_12])).

tff(c_608,plain,(
    ! [D_121,B_122,A_123] :
      ( ~ r2_hidden(D_121,B_122)
      | ~ r2_hidden(D_121,k4_xboole_0(A_123,B_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13337,plain,(
    ! [A_538,B_539,B_540] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_538,B_539),B_540),B_539)
      | r1_tarski(k4_xboole_0(A_538,B_539),B_540) ) ),
    inference(resolution,[status(thm)],[c_6,c_608])).

tff(c_13341,plain,(
    ! [A_6,B_113] : r1_tarski(k4_xboole_0(A_6,A_6),B_113) ),
    inference(resolution,[status(thm)],[c_508,c_13337])).

tff(c_13410,plain,(
    ! [A_541,B_542] : r1_tarski(k3_subset_1(A_541,A_541),B_542) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8289,c_13341])).

tff(c_13508,plain,(
    ! [A_541] : k3_subset_1(A_541,A_541) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13410,c_40])).

tff(c_417,plain,(
    ! [A_96,B_97] :
      ( k3_xboole_0(A_96,B_97) = A_96
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_429,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_417])).

tff(c_558,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_573,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k4_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_558])).

tff(c_8291,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k3_subset_1(B_13,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8289,c_573])).

tff(c_511,plain,(
    ! [B_114,A_115] :
      ( r2_hidden(B_114,A_115)
      | ~ m1_subset_1(B_114,A_115)
      | v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [C_28,A_24] :
      ( r1_tarski(C_28,A_24)
      | ~ r2_hidden(C_28,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_526,plain,(
    ! [B_114,A_24] :
      ( r1_tarski(B_114,A_24)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_511,c_42])).

tff(c_533,plain,(
    ! [B_116,A_117] :
      ( r1_tarski(B_116,A_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_117)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_526])).

tff(c_546,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_533])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_553,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_546,c_36])).

tff(c_567,plain,(
    k5_xboole_0('#skF_7','#skF_7') = k4_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_558])).

tff(c_8440,plain,(
    k4_xboole_0('#skF_7','#skF_6') = k3_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8291,c_567])).

tff(c_13533,plain,(
    k4_xboole_0('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13508,c_8440])).

tff(c_38,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_454,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_462,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,k4_xboole_0(A_21,B_22)) ) ),
    inference(resolution,[status(thm)],[c_38,c_454])).

tff(c_13677,plain,
    ( k4_xboole_0('#skF_7','#skF_6') = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13533,c_462])).

tff(c_13721,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13533,c_13677])).

tff(c_13722,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_13721])).

tff(c_30069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30063,c_13722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:49:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.04/5.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/5.04  
% 12.04/5.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/5.04  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 12.04/5.04  
% 12.04/5.04  %Foreground sorts:
% 12.04/5.04  
% 12.04/5.04  
% 12.04/5.04  %Background operators:
% 12.04/5.04  
% 12.04/5.04  
% 12.04/5.04  %Foreground operators:
% 12.04/5.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.04/5.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.04/5.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.04/5.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.04/5.04  tff('#skF_7', type, '#skF_7': $i).
% 12.04/5.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.04/5.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.04/5.04  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.04/5.04  tff('#skF_6', type, '#skF_6': $i).
% 12.04/5.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.04/5.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.04/5.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.04/5.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.04/5.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.04/5.04  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 12.04/5.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.04/5.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.04/5.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.04/5.04  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.04/5.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.04/5.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.04/5.04  
% 12.04/5.06  tff(f_88, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 12.04/5.06  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 12.04/5.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.04/5.06  tff(f_62, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.04/5.06  tff(f_66, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 12.04/5.06  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.04/5.06  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 12.04/5.06  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.04/5.06  tff(f_95, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.04/5.06  tff(f_73, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.04/5.06  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 12.04/5.06  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.04/5.06  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.04/5.06  tff(c_62, plain, (![A_31]: (k1_subset_1(A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.04/5.06  tff(c_70, plain, (k1_subset_1('#skF_6')!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.04/5.06  tff(c_78, plain, (k1_xboole_0!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_70])).
% 12.04/5.06  tff(c_114, plain, (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_78])).
% 12.04/5.06  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.04/5.06  tff(c_324, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.04/5.06  tff(c_76, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.04/5.06  tff(c_77, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_76])).
% 12.04/5.06  tff(c_115, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_77])).
% 12.04/5.06  tff(c_96, plain, (![A_39, B_40]: (r1_tarski(k4_xboole_0(A_39, B_40), A_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.04/5.06  tff(c_40, plain, (![A_23]: (k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.04/5.06  tff(c_101, plain, (![B_40]: (k4_xboole_0(k1_xboole_0, B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_96, c_40])).
% 12.04/5.06  tff(c_116, plain, (![B_40]: (k4_xboole_0('#skF_7', B_40)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_115, c_101])).
% 12.04/5.06  tff(c_208, plain, (![D_59, B_60, A_61]: (~r2_hidden(D_59, B_60) | ~r2_hidden(D_59, k4_xboole_0(A_61, B_60)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.04/5.06  tff(c_211, plain, (![D_59, B_40]: (~r2_hidden(D_59, B_40) | ~r2_hidden(D_59, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_208])).
% 12.04/5.06  tff(c_382, plain, (![A_87, B_88]: (~r2_hidden('#skF_1'(A_87, B_88), '#skF_7') | r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_324, c_211])).
% 12.04/5.06  tff(c_390, plain, (![B_2]: (r1_tarski('#skF_7', B_2))), inference(resolution, [status(thm)], [c_6, c_382])).
% 12.04/5.06  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_390, c_114])).
% 12.04/5.06  tff(c_406, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_77])).
% 12.04/5.06  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_406])).
% 12.04/5.06  tff(c_410, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_78])).
% 12.04/5.06  tff(c_823, plain, (![C_146, B_147, A_148]: (r2_hidden(C_146, B_147) | ~r2_hidden(C_146, A_148) | ~r1_tarski(A_148, B_147))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.04/5.06  tff(c_11869, plain, (![A_503, B_504, B_505]: (r2_hidden('#skF_1'(A_503, B_504), B_505) | ~r1_tarski(A_503, B_505) | r1_tarski(A_503, B_504))), inference(resolution, [status(thm)], [c_6, c_823])).
% 12.04/5.06  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.04/5.06  tff(c_8020, plain, (![A_372, B_373]: (k4_xboole_0(A_372, B_373)=k3_subset_1(A_372, B_373) | ~m1_subset_1(B_373, k1_zfmisc_1(A_372)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.04/5.06  tff(c_8033, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_8020])).
% 12.04/5.06  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.04/5.06  tff(c_8049, plain, (![D_11]: (~r2_hidden(D_11, '#skF_7') | ~r2_hidden(D_11, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_8033, c_10])).
% 12.04/5.06  tff(c_30027, plain, (![A_822, B_823]: (~r2_hidden('#skF_1'(A_822, B_823), '#skF_7') | ~r1_tarski(A_822, k3_subset_1('#skF_6', '#skF_7')) | r1_tarski(A_822, B_823))), inference(resolution, [status(thm)], [c_11869, c_8049])).
% 12.04/5.06  tff(c_30054, plain, (![B_2]: (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | r1_tarski('#skF_7', B_2))), inference(resolution, [status(thm)], [c_6, c_30027])).
% 12.04/5.06  tff(c_30063, plain, (![B_2]: (r1_tarski('#skF_7', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_410, c_30054])).
% 12.04/5.06  tff(c_409, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_78])).
% 12.04/5.06  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.04/5.06  tff(c_66, plain, (![A_34]: (~v1_xboole_0(k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.04/5.06  tff(c_44, plain, (![C_28, A_24]: (r2_hidden(C_28, k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.04/5.06  tff(c_477, plain, (![B_108, A_109]: (m1_subset_1(B_108, A_109) | ~r2_hidden(B_108, A_109) | v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.04/5.06  tff(c_480, plain, (![C_28, A_24]: (m1_subset_1(C_28, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(resolution, [status(thm)], [c_44, c_477])).
% 12.04/5.06  tff(c_483, plain, (![C_28, A_24]: (m1_subset_1(C_28, k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(negUnitSimplification, [status(thm)], [c_66, c_480])).
% 12.04/5.06  tff(c_8244, plain, (![A_384, C_385]: (k4_xboole_0(A_384, C_385)=k3_subset_1(A_384, C_385) | ~r1_tarski(C_385, A_384))), inference(resolution, [status(thm)], [c_483, c_8020])).
% 12.04/5.06  tff(c_8289, plain, (![B_13]: (k4_xboole_0(B_13, B_13)=k3_subset_1(B_13, B_13))), inference(resolution, [status(thm)], [c_30, c_8244])).
% 12.04/5.06  tff(c_489, plain, (![A_112, B_113]: (r2_hidden('#skF_1'(A_112, B_113), A_112) | r1_tarski(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.04/5.06  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.04/5.06  tff(c_508, plain, (![A_6, B_7, B_113]: (r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_113), A_6) | r1_tarski(k4_xboole_0(A_6, B_7), B_113))), inference(resolution, [status(thm)], [c_489, c_12])).
% 12.04/5.06  tff(c_608, plain, (![D_121, B_122, A_123]: (~r2_hidden(D_121, B_122) | ~r2_hidden(D_121, k4_xboole_0(A_123, B_122)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.04/5.06  tff(c_13337, plain, (![A_538, B_539, B_540]: (~r2_hidden('#skF_1'(k4_xboole_0(A_538, B_539), B_540), B_539) | r1_tarski(k4_xboole_0(A_538, B_539), B_540))), inference(resolution, [status(thm)], [c_6, c_608])).
% 12.04/5.06  tff(c_13341, plain, (![A_6, B_113]: (r1_tarski(k4_xboole_0(A_6, A_6), B_113))), inference(resolution, [status(thm)], [c_508, c_13337])).
% 12.04/5.06  tff(c_13410, plain, (![A_541, B_542]: (r1_tarski(k3_subset_1(A_541, A_541), B_542))), inference(demodulation, [status(thm), theory('equality')], [c_8289, c_13341])).
% 12.04/5.06  tff(c_13508, plain, (![A_541]: (k3_subset_1(A_541, A_541)=k1_xboole_0)), inference(resolution, [status(thm)], [c_13410, c_40])).
% 12.04/5.06  tff(c_417, plain, (![A_96, B_97]: (k3_xboole_0(A_96, B_97)=A_96 | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.04/5.06  tff(c_429, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_417])).
% 12.04/5.06  tff(c_558, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.04/5.06  tff(c_573, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k4_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_429, c_558])).
% 12.04/5.06  tff(c_8291, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k3_subset_1(B_13, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_8289, c_573])).
% 12.04/5.06  tff(c_511, plain, (![B_114, A_115]: (r2_hidden(B_114, A_115) | ~m1_subset_1(B_114, A_115) | v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.04/5.06  tff(c_42, plain, (![C_28, A_24]: (r1_tarski(C_28, A_24) | ~r2_hidden(C_28, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.04/5.06  tff(c_526, plain, (![B_114, A_24]: (r1_tarski(B_114, A_24) | ~m1_subset_1(B_114, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_511, c_42])).
% 12.04/5.06  tff(c_533, plain, (![B_116, A_117]: (r1_tarski(B_116, A_117) | ~m1_subset_1(B_116, k1_zfmisc_1(A_117)))), inference(negUnitSimplification, [status(thm)], [c_66, c_526])).
% 12.04/5.06  tff(c_546, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_533])).
% 12.04/5.06  tff(c_36, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.04/5.06  tff(c_553, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_546, c_36])).
% 12.04/5.06  tff(c_567, plain, (k5_xboole_0('#skF_7', '#skF_7')=k4_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_553, c_558])).
% 12.04/5.06  tff(c_8440, plain, (k4_xboole_0('#skF_7', '#skF_6')=k3_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8291, c_567])).
% 12.04/5.06  tff(c_13533, plain, (k4_xboole_0('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13508, c_8440])).
% 12.04/5.06  tff(c_38, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.04/5.06  tff(c_454, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.04/5.06  tff(c_462, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_38, c_454])).
% 12.04/5.06  tff(c_13677, plain, (k4_xboole_0('#skF_7', '#skF_6')='#skF_7' | ~r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13533, c_462])).
% 12.04/5.06  tff(c_13721, plain, (k1_xboole_0='#skF_7' | ~r1_tarski('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13533, c_13677])).
% 12.04/5.06  tff(c_13722, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_409, c_13721])).
% 12.04/5.06  tff(c_30069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30063, c_13722])).
% 12.04/5.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/5.06  
% 12.04/5.06  Inference rules
% 12.04/5.06  ----------------------
% 12.04/5.06  #Ref     : 0
% 12.04/5.06  #Sup     : 6967
% 12.04/5.06  #Fact    : 0
% 12.04/5.06  #Define  : 0
% 12.04/5.06  #Split   : 38
% 12.04/5.06  #Chain   : 0
% 12.04/5.06  #Close   : 0
% 12.04/5.06  
% 12.04/5.06  Ordering : KBO
% 12.04/5.06  
% 12.04/5.06  Simplification rules
% 12.04/5.06  ----------------------
% 12.04/5.06  #Subsume      : 622
% 12.04/5.06  #Demod        : 5675
% 12.04/5.06  #Tautology    : 2705
% 12.04/5.06  #SimpNegUnit  : 180
% 12.04/5.06  #BackRed      : 203
% 12.04/5.06  
% 12.04/5.06  #Partial instantiations: 0
% 12.04/5.06  #Strategies tried      : 1
% 12.04/5.06  
% 12.04/5.06  Timing (in seconds)
% 12.04/5.06  ----------------------
% 12.04/5.06  Preprocessing        : 0.32
% 12.04/5.06  Parsing              : 0.16
% 12.04/5.06  CNF conversion       : 0.02
% 12.04/5.06  Main loop            : 3.98
% 12.04/5.06  Inferencing          : 0.84
% 12.04/5.06  Reduction            : 1.65
% 12.04/5.06  Demodulation         : 1.30
% 12.04/5.06  BG Simplification    : 0.11
% 12.04/5.06  Subsumption          : 1.08
% 12.04/5.06  Abstraction          : 0.13
% 12.04/5.06  MUC search           : 0.00
% 12.04/5.06  Cooper               : 0.00
% 12.04/5.06  Total                : 4.34
% 12.04/5.06  Index Insertion      : 0.00
% 12.04/5.06  Index Deletion       : 0.00
% 12.04/5.06  Index Matching       : 0.00
% 12.04/5.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------

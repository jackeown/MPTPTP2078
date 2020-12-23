%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:00 EST 2020

% Result     : Theorem 4.95s
% Output     : CNFRefutation 5.25s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 157 expanded)
%              Number of leaves         :   38 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 244 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_50,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    ! [B_49,A_50] : k3_tarski(k2_tarski(B_49,A_50)) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_10])).

tff(c_14,plain,(
    ! [C_14,A_12,B_13] : k2_xboole_0(k2_zfmisc_1(C_14,A_12),k2_zfmisc_1(C_14,B_13)) = k2_zfmisc_1(C_14,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_zfmisc_1(A_15),k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_370,plain,(
    ! [A_98,C_99,B_100] :
      ( m1_subset_1(A_98,C_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(C_99))
      | ~ r2_hidden(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_378,plain,(
    ! [A_102,B_103,A_104] :
      ( m1_subset_1(A_102,B_103)
      | ~ r2_hidden(A_102,A_104)
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(resolution,[status(thm)],[c_24,c_370])).

tff(c_411,plain,(
    ! [A_120,B_121,B_122] :
      ( m1_subset_1(A_120,B_121)
      | ~ r1_tarski(B_122,B_121)
      | v1_xboole_0(B_122)
      | ~ m1_subset_1(A_120,B_122) ) ),
    inference(resolution,[status(thm)],[c_20,c_378])).

tff(c_423,plain,(
    ! [A_120,B_16,A_15] :
      ( m1_subset_1(A_120,k1_zfmisc_1(B_16))
      | v1_xboole_0(k1_zfmisc_1(A_15))
      | ~ m1_subset_1(A_120,k1_zfmisc_1(A_15))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_411])).

tff(c_3454,plain,(
    ! [A_406,B_407,A_408] :
      ( m1_subset_1(A_406,k1_zfmisc_1(B_407))
      | ~ m1_subset_1(A_406,k1_zfmisc_1(A_408))
      | ~ r1_tarski(A_408,B_407) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_423])).

tff(c_3461,plain,(
    ! [B_409] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(B_409))
      | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),B_409) ) ),
    inference(resolution,[status(thm)],[c_46,c_3454])).

tff(c_3731,plain,(
    ! [B_418] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),B_418))) ),
    inference(resolution,[status(thm)],[c_2,c_3461])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3758,plain,(
    ! [B_419] : r1_tarski('#skF_3',k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),B_419)) ),
    inference(resolution,[status(thm)],[c_3731,c_22])).

tff(c_3782,plain,(
    ! [B_420] : r1_tarski('#skF_3',k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_2',B_420))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3758])).

tff(c_236,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_244,plain,(
    ! [A_20,B_72,A_73] :
      ( v5_relat_1(A_20,B_72)
      | ~ r1_tarski(A_20,k2_zfmisc_1(A_73,B_72)) ) ),
    inference(resolution,[status(thm)],[c_24,c_236])).

tff(c_3821,plain,(
    ! [B_421] : v5_relat_1('#skF_3',k2_xboole_0('#skF_2',B_421)) ),
    inference(resolution,[status(thm)],[c_3782,c_244])).

tff(c_3825,plain,(
    ! [B_49] : v5_relat_1('#skF_3',k2_xboole_0(B_49,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_3821])).

tff(c_191,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_200,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_191])).

tff(c_34,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k2_relat_1(B_28),A_27)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_539,plain,(
    ! [A_142,C_143,B_144] : k2_xboole_0(k2_zfmisc_1(A_142,C_143),k2_zfmisc_1(B_144,C_143)) = k2_zfmisc_1(k2_xboole_0(A_142,B_144),C_143) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_586,plain,(
    ! [A_145,C_146,B_147] : r1_tarski(k2_zfmisc_1(A_145,C_146),k2_zfmisc_1(k2_xboole_0(A_145,B_147),C_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_2])).

tff(c_612,plain,(
    ! [B_49,C_146,A_50] : r1_tarski(k2_zfmisc_1(B_49,C_146),k2_zfmisc_1(k2_xboole_0(A_50,B_49),C_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_586])).

tff(c_2695,plain,(
    ! [A_333,B_334,A_335] :
      ( m1_subset_1(A_333,k1_zfmisc_1(B_334))
      | ~ m1_subset_1(A_333,k1_zfmisc_1(A_335))
      | ~ r1_tarski(A_335,B_334) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_423])).

tff(c_2702,plain,(
    ! [B_336] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(B_336))
      | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),B_336) ) ),
    inference(resolution,[status(thm)],[c_46,c_2695])).

tff(c_2733,plain,(
    ! [A_337] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(A_337,'#skF_1'),'#skF_2'))) ),
    inference(resolution,[status(thm)],[c_612,c_2702])).

tff(c_42,plain,(
    ! [C_35,A_33,B_34] :
      ( v4_relat_1(C_35,A_33)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2776,plain,(
    ! [A_338] : v4_relat_1('#skF_3',k2_xboole_0(A_338,'#skF_1')) ),
    inference(resolution,[status(thm)],[c_2733,c_42])).

tff(c_2780,plain,(
    ! [A_50] : v4_relat_1('#skF_3',k2_xboole_0('#skF_1',A_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_2776])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_relat_1(B_26),A_25)
      | ~ v4_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [A_29] :
      ( k2_xboole_0(k1_relat_1(A_29),k2_relat_1(A_29)) = k3_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_382,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_tarski(k2_xboole_0(A_105,C_106),B_107)
      | ~ r1_tarski(C_106,B_107)
      | ~ r1_tarski(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1271,plain,(
    ! [A_197,B_198] :
      ( r1_tarski(k3_relat_1(A_197),B_198)
      | ~ r1_tarski(k2_relat_1(A_197),B_198)
      | ~ r1_tarski(k1_relat_1(A_197),B_198)
      | ~ v1_relat_1(A_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_382])).

tff(c_44,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1288,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1271,c_44])).

tff(c_1295,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_1288])).

tff(c_1417,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1295])).

tff(c_1420,plain,
    ( ~ v4_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1417])).

tff(c_1423,plain,(
    ~ v4_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_1420])).

tff(c_2787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2780,c_1423])).

tff(c_2788,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1295])).

tff(c_2792,plain,
    ( ~ v5_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2788])).

tff(c_2795,plain,(
    ~ v5_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_2792])).

tff(c_3832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_2795])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:49:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.95/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.97  
% 4.95/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.98  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.95/1.98  
% 4.95/1.98  %Foreground sorts:
% 4.95/1.98  
% 4.95/1.98  
% 4.95/1.98  %Background operators:
% 4.95/1.98  
% 4.95/1.98  
% 4.95/1.98  %Foreground operators:
% 4.95/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.95/1.98  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.95/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.95/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.95/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.95/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.95/1.98  tff('#skF_2', type, '#skF_2': $i).
% 4.95/1.98  tff('#skF_3', type, '#skF_3': $i).
% 4.95/1.98  tff('#skF_1', type, '#skF_1': $i).
% 4.95/1.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.95/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.95/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/1.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.95/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.95/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.95/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/1.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.95/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.95/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.95/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.95/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.95/1.98  
% 5.25/1.99  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.25/1.99  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.25/1.99  tff(f_43, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 5.25/1.99  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.25/1.99  tff(f_97, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 5.25/1.99  tff(f_50, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.25/1.99  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 5.25/1.99  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.25/1.99  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.25/1.99  tff(f_66, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.25/1.99  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.25/1.99  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.25/1.99  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.25/1.99  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.25/1.99  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 5.25/1.99  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.25/1.99  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.25/1.99  tff(c_82, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.25/1.99  tff(c_116, plain, (![B_49, A_50]: (k3_tarski(k2_tarski(B_49, A_50))=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_6, c_82])).
% 5.25/1.99  tff(c_10, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.25/1.99  tff(c_122, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_116, c_10])).
% 5.25/1.99  tff(c_14, plain, (![C_14, A_12, B_13]: (k2_xboole_0(k2_zfmisc_1(C_14, A_12), k2_zfmisc_1(C_14, B_13))=k2_zfmisc_1(C_14, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.25/1.99  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.25/1.99  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.25/1.99  tff(c_18, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.25/1.99  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(k1_zfmisc_1(A_15), k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.25/1.99  tff(c_20, plain, (![A_18, B_19]: (r2_hidden(A_18, B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.25/1.99  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.25/1.99  tff(c_370, plain, (![A_98, C_99, B_100]: (m1_subset_1(A_98, C_99) | ~m1_subset_1(B_100, k1_zfmisc_1(C_99)) | ~r2_hidden(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.25/1.99  tff(c_378, plain, (![A_102, B_103, A_104]: (m1_subset_1(A_102, B_103) | ~r2_hidden(A_102, A_104) | ~r1_tarski(A_104, B_103))), inference(resolution, [status(thm)], [c_24, c_370])).
% 5.25/1.99  tff(c_411, plain, (![A_120, B_121, B_122]: (m1_subset_1(A_120, B_121) | ~r1_tarski(B_122, B_121) | v1_xboole_0(B_122) | ~m1_subset_1(A_120, B_122))), inference(resolution, [status(thm)], [c_20, c_378])).
% 5.25/1.99  tff(c_423, plain, (![A_120, B_16, A_15]: (m1_subset_1(A_120, k1_zfmisc_1(B_16)) | v1_xboole_0(k1_zfmisc_1(A_15)) | ~m1_subset_1(A_120, k1_zfmisc_1(A_15)) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_16, c_411])).
% 5.25/1.99  tff(c_3454, plain, (![A_406, B_407, A_408]: (m1_subset_1(A_406, k1_zfmisc_1(B_407)) | ~m1_subset_1(A_406, k1_zfmisc_1(A_408)) | ~r1_tarski(A_408, B_407))), inference(negUnitSimplification, [status(thm)], [c_18, c_423])).
% 5.25/1.99  tff(c_3461, plain, (![B_409]: (m1_subset_1('#skF_3', k1_zfmisc_1(B_409)) | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), B_409))), inference(resolution, [status(thm)], [c_46, c_3454])).
% 5.25/1.99  tff(c_3731, plain, (![B_418]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), B_418))))), inference(resolution, [status(thm)], [c_2, c_3461])).
% 5.25/1.99  tff(c_22, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.25/1.99  tff(c_3758, plain, (![B_419]: (r1_tarski('#skF_3', k2_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), B_419)))), inference(resolution, [status(thm)], [c_3731, c_22])).
% 5.25/1.99  tff(c_3782, plain, (![B_420]: (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_2', B_420))))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3758])).
% 5.25/1.99  tff(c_236, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.25/1.99  tff(c_244, plain, (![A_20, B_72, A_73]: (v5_relat_1(A_20, B_72) | ~r1_tarski(A_20, k2_zfmisc_1(A_73, B_72)))), inference(resolution, [status(thm)], [c_24, c_236])).
% 5.25/1.99  tff(c_3821, plain, (![B_421]: (v5_relat_1('#skF_3', k2_xboole_0('#skF_2', B_421)))), inference(resolution, [status(thm)], [c_3782, c_244])).
% 5.25/1.99  tff(c_3825, plain, (![B_49]: (v5_relat_1('#skF_3', k2_xboole_0(B_49, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_122, c_3821])).
% 5.25/1.99  tff(c_191, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.25/1.99  tff(c_200, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_191])).
% 5.25/1.99  tff(c_34, plain, (![B_28, A_27]: (r1_tarski(k2_relat_1(B_28), A_27) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.25/1.99  tff(c_539, plain, (![A_142, C_143, B_144]: (k2_xboole_0(k2_zfmisc_1(A_142, C_143), k2_zfmisc_1(B_144, C_143))=k2_zfmisc_1(k2_xboole_0(A_142, B_144), C_143))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.25/1.99  tff(c_586, plain, (![A_145, C_146, B_147]: (r1_tarski(k2_zfmisc_1(A_145, C_146), k2_zfmisc_1(k2_xboole_0(A_145, B_147), C_146)))), inference(superposition, [status(thm), theory('equality')], [c_539, c_2])).
% 5.25/1.99  tff(c_612, plain, (![B_49, C_146, A_50]: (r1_tarski(k2_zfmisc_1(B_49, C_146), k2_zfmisc_1(k2_xboole_0(A_50, B_49), C_146)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_586])).
% 5.25/1.99  tff(c_2695, plain, (![A_333, B_334, A_335]: (m1_subset_1(A_333, k1_zfmisc_1(B_334)) | ~m1_subset_1(A_333, k1_zfmisc_1(A_335)) | ~r1_tarski(A_335, B_334))), inference(negUnitSimplification, [status(thm)], [c_18, c_423])).
% 5.25/1.99  tff(c_2702, plain, (![B_336]: (m1_subset_1('#skF_3', k1_zfmisc_1(B_336)) | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), B_336))), inference(resolution, [status(thm)], [c_46, c_2695])).
% 5.25/1.99  tff(c_2733, plain, (![A_337]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(A_337, '#skF_1'), '#skF_2'))))), inference(resolution, [status(thm)], [c_612, c_2702])).
% 5.25/1.99  tff(c_42, plain, (![C_35, A_33, B_34]: (v4_relat_1(C_35, A_33) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.25/1.99  tff(c_2776, plain, (![A_338]: (v4_relat_1('#skF_3', k2_xboole_0(A_338, '#skF_1')))), inference(resolution, [status(thm)], [c_2733, c_42])).
% 5.25/1.99  tff(c_2780, plain, (![A_50]: (v4_relat_1('#skF_3', k2_xboole_0('#skF_1', A_50)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_2776])).
% 5.25/1.99  tff(c_30, plain, (![B_26, A_25]: (r1_tarski(k1_relat_1(B_26), A_25) | ~v4_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.25/1.99  tff(c_36, plain, (![A_29]: (k2_xboole_0(k1_relat_1(A_29), k2_relat_1(A_29))=k3_relat_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.25/1.99  tff(c_382, plain, (![A_105, C_106, B_107]: (r1_tarski(k2_xboole_0(A_105, C_106), B_107) | ~r1_tarski(C_106, B_107) | ~r1_tarski(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.25/1.99  tff(c_1271, plain, (![A_197, B_198]: (r1_tarski(k3_relat_1(A_197), B_198) | ~r1_tarski(k2_relat_1(A_197), B_198) | ~r1_tarski(k1_relat_1(A_197), B_198) | ~v1_relat_1(A_197))), inference(superposition, [status(thm), theory('equality')], [c_36, c_382])).
% 5.25/1.99  tff(c_44, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.25/1.99  tff(c_1288, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1271, c_44])).
% 5.25/1.99  tff(c_1295, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_1288])).
% 5.25/1.99  tff(c_1417, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1295])).
% 5.25/1.99  tff(c_1420, plain, (~v4_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1417])).
% 5.25/1.99  tff(c_1423, plain, (~v4_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_1420])).
% 5.25/1.99  tff(c_2787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2780, c_1423])).
% 5.25/1.99  tff(c_2788, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1295])).
% 5.25/1.99  tff(c_2792, plain, (~v5_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2788])).
% 5.25/1.99  tff(c_2795, plain, (~v5_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_2792])).
% 5.25/1.99  tff(c_3832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3825, c_2795])).
% 5.25/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/1.99  
% 5.25/1.99  Inference rules
% 5.25/1.99  ----------------------
% 5.25/1.99  #Ref     : 0
% 5.25/1.99  #Sup     : 897
% 5.25/1.99  #Fact    : 0
% 5.25/1.99  #Define  : 0
% 5.25/1.99  #Split   : 3
% 5.25/1.99  #Chain   : 0
% 5.25/1.99  #Close   : 0
% 5.25/1.99  
% 5.25/1.99  Ordering : KBO
% 5.25/1.99  
% 5.25/1.99  Simplification rules
% 5.25/1.99  ----------------------
% 5.25/1.99  #Subsume      : 58
% 5.25/1.99  #Demod        : 419
% 5.25/1.99  #Tautology    : 259
% 5.25/1.99  #SimpNegUnit  : 1
% 5.25/1.99  #BackRed      : 2
% 5.25/1.99  
% 5.25/1.99  #Partial instantiations: 0
% 5.25/1.99  #Strategies tried      : 1
% 5.25/1.99  
% 5.25/1.99  Timing (in seconds)
% 5.25/1.99  ----------------------
% 5.25/2.00  Preprocessing        : 0.32
% 5.25/2.00  Parsing              : 0.18
% 5.25/2.00  CNF conversion       : 0.02
% 5.25/2.00  Main loop            : 0.87
% 5.25/2.00  Inferencing          : 0.28
% 5.25/2.00  Reduction            : 0.35
% 5.25/2.00  Demodulation         : 0.28
% 5.25/2.00  BG Simplification    : 0.03
% 5.25/2.00  Subsumption          : 0.15
% 5.25/2.00  Abstraction          : 0.03
% 5.25/2.00  MUC search           : 0.00
% 5.25/2.00  Cooper               : 0.00
% 5.25/2.00  Total                : 1.23
% 5.25/2.00  Index Insertion      : 0.00
% 5.25/2.00  Index Deletion       : 0.00
% 5.25/2.00  Index Matching       : 0.00
% 5.25/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------

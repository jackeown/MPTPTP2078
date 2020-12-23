%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:40 EST 2020

% Result     : Theorem 25.03s
% Output     : CNFRefutation 25.09s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 166 expanded)
%              Number of leaves         :   35 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 ( 285 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_132,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_141,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_132])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_13,B_14)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k8_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_15,B_16)),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_238,plain,(
    ! [C_78,B_79,A_80] :
      ( v5_relat_1(C_78,B_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_247,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_238])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_454,plain,(
    ! [A_111,B_112] :
      ( k8_relat_1(A_111,B_112) = B_112
      | ~ r1_tarski(k2_relat_1(B_112),A_111)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_606,plain,(
    ! [A_121,B_122] :
      ( k8_relat_1(A_121,B_122) = B_122
      | ~ v5_relat_1(B_122,A_121)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_16,c_454])).

tff(c_624,plain,
    ( k8_relat_1('#skF_1','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_247,c_606])).

tff(c_641,plain,(
    k8_relat_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_624])).

tff(c_649,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_22])).

tff(c_658,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_649])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_697,plain,(
    ! [A_125] :
      ( r1_tarski(A_125,'#skF_1')
      | ~ r1_tarski(A_125,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_658,c_8])).

tff(c_709,plain,(
    ! [A_15] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_15,'#skF_4')),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_697])).

tff(c_722,plain,(
    ! [A_15] : r1_tarski(k2_relat_1(k8_relat_1(A_15,'#skF_4')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_709])).

tff(c_32,plain,(
    ! [A_23] :
      ( k8_relat_1(k2_relat_1(A_23),A_23) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1374,plain,(
    ! [A_159,B_160,C_161] :
      ( k8_relat_1(A_159,k8_relat_1(B_160,C_161)) = k8_relat_1(A_159,C_161)
      | ~ r1_tarski(A_159,B_160)
      | ~ v1_relat_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_15332,plain,(
    ! [B_525,C_526] :
      ( k8_relat_1(k2_relat_1(k8_relat_1(B_525,C_526)),C_526) = k8_relat_1(B_525,C_526)
      | ~ r1_tarski(k2_relat_1(k8_relat_1(B_525,C_526)),B_525)
      | ~ v1_relat_1(C_526)
      | ~ v1_relat_1(k8_relat_1(B_525,C_526)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1374])).

tff(c_78931,plain,(
    ! [A_1431,B_1432] :
      ( k8_relat_1(k2_relat_1(k8_relat_1(A_1431,B_1432)),B_1432) = k8_relat_1(A_1431,B_1432)
      | ~ v1_relat_1(k8_relat_1(A_1431,B_1432))
      | ~ v1_relat_1(B_1432) ) ),
    inference(resolution,[status(thm)],[c_22,c_15332])).

tff(c_1050,plain,(
    ! [A_147,C_148,B_149] :
      ( r1_tarski(k8_relat_1(A_147,C_148),k8_relat_1(B_149,C_148))
      | ~ r1_tarski(A_147,B_149)
      | ~ v1_relat_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1062,plain,(
    ! [A_147] :
      ( r1_tarski(k8_relat_1(A_147,'#skF_4'),'#skF_4')
      | ~ r1_tarski(A_147,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_1050])).

tff(c_1087,plain,(
    ! [A_147] :
      ( r1_tarski(k8_relat_1(A_147,'#skF_4'),'#skF_4')
      | ~ r1_tarski(A_147,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_1062])).

tff(c_79367,plain,(
    ! [A_1431] :
      ( r1_tarski(k8_relat_1(A_1431,'#skF_4'),'#skF_4')
      | ~ r1_tarski(k2_relat_1(k8_relat_1(A_1431,'#skF_4')),'#skF_1')
      | ~ v1_relat_1(k8_relat_1(A_1431,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78931,c_1087])).

tff(c_79704,plain,(
    ! [A_1433] :
      ( r1_tarski(k8_relat_1(A_1433,'#skF_4'),'#skF_4')
      | ~ v1_relat_1(k8_relat_1(A_1433,'#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_722,c_79367])).

tff(c_108,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_112,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_108])).

tff(c_172,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(A_69,C_70)
      | ~ r1_tarski(B_71,C_70)
      | ~ r1_tarski(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [A_69] :
      ( r1_tarski(A_69,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_69,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_112,c_172])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2075,plain,(
    ! [D_196,C_197,B_198,A_199] :
      ( m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(C_197,B_198)))
      | ~ r1_tarski(k2_relat_1(D_196),B_198)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(C_197,A_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_11613,plain,(
    ! [A_451,C_452,B_453,A_454] :
      ( m1_subset_1(A_451,k1_zfmisc_1(k2_zfmisc_1(C_452,B_453)))
      | ~ r1_tarski(k2_relat_1(A_451),B_453)
      | ~ r1_tarski(A_451,k2_zfmisc_1(C_452,A_454)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2075])).

tff(c_11957,plain,(
    ! [A_461,B_462] :
      ( m1_subset_1(A_461,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_462)))
      | ~ r1_tarski(k2_relat_1(A_461),B_462)
      | ~ r1_tarski(A_461,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_180,c_11613])).

tff(c_1876,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k6_relset_1(A_185,B_186,C_187,D_188) = k8_relat_1(C_187,D_188)
      | ~ m1_subset_1(D_188,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1883,plain,(
    ! [C_187] : k6_relset_1('#skF_3','#skF_1',C_187,'#skF_4') = k8_relat_1(C_187,'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1876])).

tff(c_52,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1979,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_52])).

tff(c_11978,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_11957,c_1979])).

tff(c_12874,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11978])).

tff(c_79766,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_79704,c_12874])).

tff(c_79791,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_79766])).

tff(c_79796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_79791])).

tff(c_79797,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_11978])).

tff(c_79834,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_79797])).

tff(c_79839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_79834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.03/15.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.09/15.47  
% 25.09/15.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.09/15.48  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 25.09/15.48  
% 25.09/15.48  %Foreground sorts:
% 25.09/15.48  
% 25.09/15.48  
% 25.09/15.48  %Background operators:
% 25.09/15.48  
% 25.09/15.48  
% 25.09/15.48  %Foreground operators:
% 25.09/15.48  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 25.09/15.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.09/15.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.09/15.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 25.09/15.48  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 25.09/15.48  tff('#skF_2', type, '#skF_2': $i).
% 25.09/15.48  tff('#skF_3', type, '#skF_3': $i).
% 25.09/15.48  tff('#skF_1', type, '#skF_1': $i).
% 25.09/15.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 25.09/15.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.09/15.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.09/15.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 25.09/15.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.09/15.48  tff('#skF_4', type, '#skF_4': $i).
% 25.09/15.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 25.09/15.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.09/15.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 25.09/15.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.09/15.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 25.09/15.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.09/15.48  
% 25.09/15.49  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 25.09/15.49  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 25.09/15.49  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 25.09/15.49  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 25.09/15.49  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_relat_1)).
% 25.09/15.49  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 25.09/15.49  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 25.09/15.49  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 25.09/15.49  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 25.09/15.49  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 25.09/15.49  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_relat_1)).
% 25.09/15.49  tff(f_93, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_relat_1)).
% 25.09/15.49  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 25.09/15.49  tff(f_117, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 25.09/15.49  tff(f_111, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 25.09/15.49  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 25.09/15.49  tff(c_132, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.09/15.49  tff(c_141, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_132])).
% 25.09/15.49  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(k2_relat_1(k8_relat_1(A_13, B_14)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 25.09/15.49  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k8_relat_1(A_11, B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 25.09/15.49  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(k2_relat_1(k8_relat_1(A_15, B_16)), k2_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 25.09/15.49  tff(c_238, plain, (![C_78, B_79, A_80]: (v5_relat_1(C_78, B_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 25.09/15.49  tff(c_247, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_238])).
% 25.09/15.49  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.09/15.49  tff(c_454, plain, (![A_111, B_112]: (k8_relat_1(A_111, B_112)=B_112 | ~r1_tarski(k2_relat_1(B_112), A_111) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_77])).
% 25.09/15.49  tff(c_606, plain, (![A_121, B_122]: (k8_relat_1(A_121, B_122)=B_122 | ~v5_relat_1(B_122, A_121) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_16, c_454])).
% 25.09/15.49  tff(c_624, plain, (k8_relat_1('#skF_1', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_247, c_606])).
% 25.09/15.49  tff(c_641, plain, (k8_relat_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_624])).
% 25.09/15.49  tff(c_649, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_641, c_22])).
% 25.09/15.49  tff(c_658, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_649])).
% 25.09/15.49  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.09/15.49  tff(c_697, plain, (![A_125]: (r1_tarski(A_125, '#skF_1') | ~r1_tarski(A_125, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_658, c_8])).
% 25.09/15.49  tff(c_709, plain, (![A_15]: (r1_tarski(k2_relat_1(k8_relat_1(A_15, '#skF_4')), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_697])).
% 25.09/15.49  tff(c_722, plain, (![A_15]: (r1_tarski(k2_relat_1(k8_relat_1(A_15, '#skF_4')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_709])).
% 25.09/15.49  tff(c_32, plain, (![A_23]: (k8_relat_1(k2_relat_1(A_23), A_23)=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 25.09/15.49  tff(c_1374, plain, (![A_159, B_160, C_161]: (k8_relat_1(A_159, k8_relat_1(B_160, C_161))=k8_relat_1(A_159, C_161) | ~r1_tarski(A_159, B_160) | ~v1_relat_1(C_161))), inference(cnfTransformation, [status(thm)], [f_87])).
% 25.09/15.49  tff(c_15332, plain, (![B_525, C_526]: (k8_relat_1(k2_relat_1(k8_relat_1(B_525, C_526)), C_526)=k8_relat_1(B_525, C_526) | ~r1_tarski(k2_relat_1(k8_relat_1(B_525, C_526)), B_525) | ~v1_relat_1(C_526) | ~v1_relat_1(k8_relat_1(B_525, C_526)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1374])).
% 25.09/15.49  tff(c_78931, plain, (![A_1431, B_1432]: (k8_relat_1(k2_relat_1(k8_relat_1(A_1431, B_1432)), B_1432)=k8_relat_1(A_1431, B_1432) | ~v1_relat_1(k8_relat_1(A_1431, B_1432)) | ~v1_relat_1(B_1432))), inference(resolution, [status(thm)], [c_22, c_15332])).
% 25.09/15.49  tff(c_1050, plain, (![A_147, C_148, B_149]: (r1_tarski(k8_relat_1(A_147, C_148), k8_relat_1(B_149, C_148)) | ~r1_tarski(A_147, B_149) | ~v1_relat_1(C_148))), inference(cnfTransformation, [status(thm)], [f_93])).
% 25.09/15.49  tff(c_1062, plain, (![A_147]: (r1_tarski(k8_relat_1(A_147, '#skF_4'), '#skF_4') | ~r1_tarski(A_147, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_641, c_1050])).
% 25.09/15.49  tff(c_1087, plain, (![A_147]: (r1_tarski(k8_relat_1(A_147, '#skF_4'), '#skF_4') | ~r1_tarski(A_147, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_1062])).
% 25.09/15.49  tff(c_79367, plain, (![A_1431]: (r1_tarski(k8_relat_1(A_1431, '#skF_4'), '#skF_4') | ~r1_tarski(k2_relat_1(k8_relat_1(A_1431, '#skF_4')), '#skF_1') | ~v1_relat_1(k8_relat_1(A_1431, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_78931, c_1087])).
% 25.09/15.49  tff(c_79704, plain, (![A_1433]: (r1_tarski(k8_relat_1(A_1433, '#skF_4'), '#skF_4') | ~v1_relat_1(k8_relat_1(A_1433, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_722, c_79367])).
% 25.09/15.49  tff(c_108, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.09/15.49  tff(c_112, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_108])).
% 25.09/15.49  tff(c_172, plain, (![A_69, C_70, B_71]: (r1_tarski(A_69, C_70) | ~r1_tarski(B_71, C_70) | ~r1_tarski(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.09/15.49  tff(c_180, plain, (![A_69]: (r1_tarski(A_69, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_69, '#skF_4'))), inference(resolution, [status(thm)], [c_112, c_172])).
% 25.09/15.49  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.09/15.49  tff(c_2075, plain, (![D_196, C_197, B_198, A_199]: (m1_subset_1(D_196, k1_zfmisc_1(k2_zfmisc_1(C_197, B_198))) | ~r1_tarski(k2_relat_1(D_196), B_198) | ~m1_subset_1(D_196, k1_zfmisc_1(k2_zfmisc_1(C_197, A_199))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 25.09/15.49  tff(c_11613, plain, (![A_451, C_452, B_453, A_454]: (m1_subset_1(A_451, k1_zfmisc_1(k2_zfmisc_1(C_452, B_453))) | ~r1_tarski(k2_relat_1(A_451), B_453) | ~r1_tarski(A_451, k2_zfmisc_1(C_452, A_454)))), inference(resolution, [status(thm)], [c_12, c_2075])).
% 25.09/15.49  tff(c_11957, plain, (![A_461, B_462]: (m1_subset_1(A_461, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_462))) | ~r1_tarski(k2_relat_1(A_461), B_462) | ~r1_tarski(A_461, '#skF_4'))), inference(resolution, [status(thm)], [c_180, c_11613])).
% 25.09/15.49  tff(c_1876, plain, (![A_185, B_186, C_187, D_188]: (k6_relset_1(A_185, B_186, C_187, D_188)=k8_relat_1(C_187, D_188) | ~m1_subset_1(D_188, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 25.09/15.49  tff(c_1883, plain, (![C_187]: (k6_relset_1('#skF_3', '#skF_1', C_187, '#skF_4')=k8_relat_1(C_187, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_1876])).
% 25.09/15.49  tff(c_52, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 25.09/15.49  tff(c_1979, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_52])).
% 25.09/15.49  tff(c_11978, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_11957, c_1979])).
% 25.09/15.49  tff(c_12874, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_11978])).
% 25.09/15.49  tff(c_79766, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_79704, c_12874])).
% 25.09/15.49  tff(c_79791, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_79766])).
% 25.09/15.49  tff(c_79796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_79791])).
% 25.09/15.49  tff(c_79797, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_11978])).
% 25.09/15.49  tff(c_79834, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_79797])).
% 25.09/15.49  tff(c_79839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_79834])).
% 25.09/15.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.09/15.49  
% 25.09/15.49  Inference rules
% 25.09/15.49  ----------------------
% 25.09/15.49  #Ref     : 0
% 25.09/15.49  #Sup     : 18687
% 25.09/15.49  #Fact    : 0
% 25.09/15.49  #Define  : 0
% 25.09/15.49  #Split   : 13
% 25.09/15.49  #Chain   : 0
% 25.09/15.49  #Close   : 0
% 25.09/15.49  
% 25.09/15.49  Ordering : KBO
% 25.09/15.49  
% 25.09/15.49  Simplification rules
% 25.09/15.49  ----------------------
% 25.09/15.49  #Subsume      : 4502
% 25.09/15.49  #Demod        : 11337
% 25.09/15.49  #Tautology    : 6362
% 25.09/15.49  #SimpNegUnit  : 181
% 25.09/15.49  #BackRed      : 5
% 25.09/15.49  
% 25.09/15.49  #Partial instantiations: 0
% 25.09/15.49  #Strategies tried      : 1
% 25.09/15.49  
% 25.09/15.49  Timing (in seconds)
% 25.09/15.49  ----------------------
% 25.09/15.50  Preprocessing        : 0.34
% 25.09/15.50  Parsing              : 0.18
% 25.09/15.50  CNF conversion       : 0.02
% 25.09/15.50  Main loop            : 14.36
% 25.09/15.50  Inferencing          : 1.89
% 25.09/15.50  Reduction            : 7.51
% 25.09/15.50  Demodulation         : 6.36
% 25.09/15.50  BG Simplification    : 0.18
% 25.09/15.50  Subsumption          : 4.16
% 25.09/15.50  Abstraction          : 0.28
% 25.09/15.50  MUC search           : 0.00
% 25.09/15.50  Cooper               : 0.00
% 25.09/15.50  Total                : 14.74
% 25.09/15.50  Index Insertion      : 0.00
% 25.09/15.50  Index Deletion       : 0.00
% 25.09/15.50  Index Matching       : 0.00
% 25.09/15.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

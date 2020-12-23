%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:37 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 8.24s
% Verified   : 
% Statistics : Number of formulae       :  253 (1435 expanded)
%              Number of leaves         :   45 ( 445 expanded)
%              Depth                    :   15
%              Number of atoms          :  405 (4265 expanded)
%              Number of equality atoms :  138 ( 782 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_68,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_129,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_142,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_129])).

tff(c_72,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6857,plain,(
    ! [A_655,B_656,C_657] :
      ( k1_relset_1(A_655,B_656,C_657) = k1_relat_1(C_657)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(k2_zfmisc_1(A_655,B_656))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6876,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_6857])).

tff(c_7760,plain,(
    ! [B_752,A_753,C_754] :
      ( k1_xboole_0 = B_752
      | k1_relset_1(A_753,B_752,C_754) = A_753
      | ~ v1_funct_2(C_754,A_753,B_752)
      | ~ m1_subset_1(C_754,k1_zfmisc_1(k2_zfmisc_1(A_753,B_752))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_7773,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_7760])).

tff(c_7786,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6876,c_7773])).

tff(c_7788,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7786])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k7_relat_1(B_17,A_16)) = A_16
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7811,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7788,c_32])).

tff(c_8089,plain,(
    ! [A_767] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_767)) = A_767
      | ~ r1_tarski(A_767,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_7811])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_7606,plain,(
    ! [A_740,B_741,C_742,D_743] :
      ( k2_partfun1(A_740,B_741,C_742,D_743) = k7_relat_1(C_742,D_743)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1(A_740,B_741)))
      | ~ v1_funct_1(C_742) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_7615,plain,(
    ! [D_743] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_743) = k7_relat_1('#skF_5',D_743)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_7606])).

tff(c_7627,plain,(
    ! [D_743] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_743) = k7_relat_1('#skF_5',D_743) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7615])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5229,plain,(
    ! [A_528,B_529,C_530,D_531] :
      ( k7_relset_1(A_528,B_529,C_530,D_531) = k9_relat_1(C_530,D_531)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_528,B_529))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5241,plain,(
    ! [D_532] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_532) = k9_relat_1('#skF_5',D_532) ),
    inference(resolution,[status(thm)],[c_70,c_5229])).

tff(c_3076,plain,(
    ! [A_339,B_340,C_341] :
      ( k1_relset_1(A_339,B_340,C_341) = k1_relat_1(C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3095,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_3076])).

tff(c_3846,plain,(
    ! [B_419,A_420,C_421] :
      ( k1_xboole_0 = B_419
      | k1_relset_1(A_420,B_419,C_421) = A_420
      | ~ v1_funct_2(C_421,A_420,B_419)
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(A_420,B_419))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3859,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3846])).

tff(c_3871,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3095,c_3859])).

tff(c_3873,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3871])).

tff(c_3890,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3873,c_32])).

tff(c_4174,plain,(
    ! [A_437] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_437)) = A_437
      | ~ r1_tarski(A_437,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_3890])).

tff(c_3744,plain,(
    ! [A_413,B_414,C_415,D_416] :
      ( k2_partfun1(A_413,B_414,C_415,D_416) = k7_relat_1(C_415,D_416)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414)))
      | ~ v1_funct_1(C_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3753,plain,(
    ! [D_416] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_416) = k7_relat_1('#skF_5',D_416)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_3744])).

tff(c_3765,plain,(
    ! [D_416] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_416) = k7_relat_1('#skF_5',D_416) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3753])).

tff(c_1674,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( k7_relset_1(A_218,B_219,C_220,D_221) = k9_relat_1(C_220,D_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1685,plain,(
    ! [D_221] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_221) = k9_relat_1('#skF_5',D_221) ),
    inference(resolution,[status(thm)],[c_70,c_1674])).

tff(c_66,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1687,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1685,c_66])).

tff(c_28,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2077,plain,(
    ! [A_268,B_269,C_270,D_271] :
      ( k2_partfun1(A_268,B_269,C_270,D_271) = k7_relat_1(C_270,D_271)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269)))
      | ~ v1_funct_1(C_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2084,plain,(
    ! [D_271] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_271) = k7_relat_1('#skF_5',D_271)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_2077])).

tff(c_2093,plain,(
    ! [D_271] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_271) = k7_relat_1('#skF_5',D_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2084])).

tff(c_1909,plain,(
    ! [C_252,A_253,B_254] :
      ( m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ r1_tarski(k2_relat_1(C_252),B_254)
      | ~ r1_tarski(k1_relat_1(C_252),A_253)
      | ~ v1_relat_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_908,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( v1_funct_1(k2_partfun1(A_141,B_142,C_143,D_144))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_913,plain,(
    ! [D_144] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_144))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_908])).

tff(c_921,plain,(
    ! [D_144] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_913])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_143,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_143])).

tff(c_925,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1067,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_925])).

tff(c_1941,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1909,c_1067])).

tff(c_2356,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_2093,c_2093,c_1941])).

tff(c_2357,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2356])).

tff(c_2360,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_2357])).

tff(c_2364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2360])).

tff(c_2366,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2356])).

tff(c_44,plain,(
    ! [C_33,A_31,B_32] :
      ( m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ r1_tarski(k2_relat_1(C_33),B_32)
      | ~ r1_tarski(k1_relat_1(C_33),A_31)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2096,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_1067])).

tff(c_2113,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_2096])).

tff(c_2464,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2366,c_2113])).

tff(c_2465,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2464])).

tff(c_2493,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_2465])).

tff(c_2500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2493])).

tff(c_2501,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2464])).

tff(c_2565,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2501])).

tff(c_2568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1687,c_2565])).

tff(c_2569,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_3776,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3765,c_2569])).

tff(c_2570,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_3093,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2570,c_3076])).

tff(c_3769,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3765,c_3765,c_3093])).

tff(c_3775,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3765,c_2570])).

tff(c_3974,plain,(
    ! [B_422,C_423,A_424] :
      ( k1_xboole_0 = B_422
      | v1_funct_2(C_423,A_424,B_422)
      | k1_relset_1(A_424,B_422,C_423) != A_424
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_424,B_422))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3977,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3775,c_3974])).

tff(c_3995,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3769,c_3977])).

tff(c_3996,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3776,c_3995])).

tff(c_4050,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3996])).

tff(c_4180,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4174,c_4050])).

tff(c_4264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4180])).

tff(c_4265,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3996])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4311,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_10])).

tff(c_3431,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( k7_relset_1(A_384,B_385,C_386,D_387) = k9_relat_1(C_386,D_387)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3445,plain,(
    ! [D_387] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_387) = k9_relat_1('#skF_5',D_387) ),
    inference(resolution,[status(thm)],[c_70,c_3431])).

tff(c_949,plain,(
    ! [B_147,A_148] :
      ( B_147 = A_148
      | ~ r1_tarski(B_147,A_148)
      | ~ r1_tarski(A_148,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_963,plain,
    ( k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_949])).

tff(c_973,plain,(
    ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_963])).

tff(c_3446,plain,(
    ~ r1_tarski('#skF_3',k9_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3445,c_973])).

tff(c_4403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4311,c_3446])).

tff(c_4404,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3871])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4447,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4404,c_2])).

tff(c_4449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4447])).

tff(c_4450,plain,(
    k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_5247,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5241,c_4450])).

tff(c_5497,plain,(
    ! [A_558,B_559,C_560,D_561] :
      ( k2_partfun1(A_558,B_559,C_560,D_561) = k7_relat_1(C_560,D_561)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(A_558,B_559)))
      | ~ v1_funct_1(C_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5504,plain,(
    ! [D_561] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_561) = k7_relat_1('#skF_5',D_561)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_5497])).

tff(c_5513,plain,(
    ! [D_561] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_561) = k7_relat_1('#skF_5',D_561) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5504])).

tff(c_5375,plain,(
    ! [C_544,A_545,B_546] :
      ( m1_subset_1(C_544,k1_zfmisc_1(k2_zfmisc_1(A_545,B_546)))
      | ~ r1_tarski(k2_relat_1(C_544),B_546)
      | ~ r1_tarski(k1_relat_1(C_544),A_545)
      | ~ v1_relat_1(C_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4529,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_925])).

tff(c_5407,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_5375,c_4529])).

tff(c_5746,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5513,c_5513,c_5513,c_5407])).

tff(c_5747,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5746])).

tff(c_5750,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_5747])).

tff(c_5754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_5750])).

tff(c_5756,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5746])).

tff(c_5516,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5513,c_4529])).

tff(c_5533,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_5516])).

tff(c_5949,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5756,c_5533])).

tff(c_5950,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5949])).

tff(c_6073,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_5950])).

tff(c_6080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_6073])).

tff(c_6081,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5949])).

tff(c_6292,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6081])).

tff(c_6295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_8,c_5247,c_6292])).

tff(c_6297,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_6874,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6297,c_6857])).

tff(c_7631,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7627,c_7627,c_6874])).

tff(c_6296,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_7638,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7627,c_6296])).

tff(c_7637,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7627,c_6297])).

tff(c_52,plain,(
    ! [B_35,C_36,A_34] :
      ( k1_xboole_0 = B_35
      | v1_funct_2(C_36,A_34,B_35)
      | k1_relset_1(A_34,B_35,C_36) != A_34
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_7695,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_7637,c_52])).

tff(c_7719,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_7638,c_7695])).

tff(c_7738,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7719])).

tff(c_7853,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7631,c_7738])).

tff(c_8095,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8089,c_7853])).

tff(c_8185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8095])).

tff(c_8186,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7786])).

tff(c_8232,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8186,c_2])).

tff(c_8234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_8232])).

tff(c_8235,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7719])).

tff(c_8278,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8235,c_10])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8277,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8235,c_8235,c_14])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6417,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6297,c_18])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6526,plain,
    ( k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6417,c_4])).

tff(c_6581,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6526])).

tff(c_7632,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7627,c_6581])).

tff(c_8556,plain,(
    ~ r1_tarski('#skF_3',k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8277,c_7632])).

tff(c_8560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8278,c_8556])).

tff(c_8561,plain,(
    k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_6526])).

tff(c_8645,plain,(
    ~ v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8561,c_6296])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8871,plain,(
    ! [A_794,B_795,C_796] :
      ( k1_relset_1(A_794,B_795,C_796) = k1_relat_1(C_796)
      | ~ m1_subset_1(C_796,k1_zfmisc_1(k2_zfmisc_1(A_794,B_795))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9255,plain,(
    ! [A_843,B_844,A_845] :
      ( k1_relset_1(A_843,B_844,A_845) = k1_relat_1(A_845)
      | ~ r1_tarski(A_845,k2_zfmisc_1(A_843,B_844)) ) ),
    inference(resolution,[status(thm)],[c_20,c_8871])).

tff(c_9287,plain,(
    ! [A_843,B_844] : k1_relset_1(A_843,B_844,k2_zfmisc_1(A_843,B_844)) = k1_relat_1(k2_zfmisc_1(A_843,B_844)) ),
    inference(resolution,[status(thm)],[c_8,c_9255])).

tff(c_8644,plain,(
    m1_subset_1(k2_zfmisc_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8561,c_6297])).

tff(c_9679,plain,(
    ! [B_873,C_874,A_875] :
      ( k1_xboole_0 = B_873
      | v1_funct_2(C_874,A_875,B_873)
      | k1_relset_1(A_875,B_873,C_874) != A_875
      | ~ m1_subset_1(C_874,k1_zfmisc_1(k2_zfmisc_1(A_875,B_873))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_9685,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_8644,c_9679])).

tff(c_9701,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9287,c_9685])).

tff(c_9702,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_8645,c_9701])).

tff(c_9739,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_9702])).

tff(c_9466,plain,(
    ! [A_863,B_864,C_865,D_866] :
      ( k2_partfun1(A_863,B_864,C_865,D_866) = k7_relat_1(C_865,D_866)
      | ~ m1_subset_1(C_865,k1_zfmisc_1(k2_zfmisc_1(A_863,B_864)))
      | ~ v1_funct_1(C_865) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_9475,plain,(
    ! [D_866] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_866) = k7_relat_1('#skF_5',D_866)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_9466])).

tff(c_9489,plain,(
    ! [D_867] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_867) = k7_relat_1('#skF_5',D_867) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9475])).

tff(c_9495,plain,(
    k7_relat_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9489,c_8561])).

tff(c_8890,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_8871])).

tff(c_9537,plain,(
    ! [B_869,A_870,C_871] :
      ( k1_xboole_0 = B_869
      | k1_relset_1(A_870,B_869,C_871) = A_870
      | ~ v1_funct_2(C_871,A_870,B_869)
      | ~ m1_subset_1(C_871,k1_zfmisc_1(k2_zfmisc_1(A_870,B_869))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_9550,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_9537])).

tff(c_9563,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8890,c_9550])).

tff(c_9565,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9563])).

tff(c_9579,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9565,c_32])).

tff(c_9740,plain,(
    ! [A_877] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_877)) = A_877
      | ~ r1_tarski(A_877,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_9579])).

tff(c_9814,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9495,c_9740])).

tff(c_9851,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_9814])).

tff(c_9853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9739,c_9851])).

tff(c_9854,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9702])).

tff(c_927,plain,(
    ! [C_145] :
      ( v1_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_129])).

tff(c_933,plain,(
    ! [A_146] :
      ( v1_relat_1(A_146)
      | ~ r1_tarski(A_146,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_927])).

tff(c_947,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_933])).

tff(c_6327,plain,(
    ! [C_612,A_613,B_614] :
      ( v4_relat_1(C_612,A_613)
      | ~ m1_subset_1(C_612,k1_zfmisc_1(k2_zfmisc_1(A_613,B_614))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6374,plain,(
    ! [A_623,A_624,B_625] :
      ( v4_relat_1(A_623,A_624)
      | ~ r1_tarski(A_623,k2_zfmisc_1(A_624,B_625)) ) ),
    inference(resolution,[status(thm)],[c_20,c_6327])).

tff(c_6418,plain,(
    ! [A_626] : v4_relat_1(k1_xboole_0,A_626) ),
    inference(resolution,[status(thm)],[c_10,c_6374])).

tff(c_4476,plain,(
    ! [B_446,A_447] :
      ( r1_tarski(k1_relat_1(B_446),A_447)
      | ~ v4_relat_1(B_446,A_447)
      | ~ v1_relat_1(B_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_966,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_949])).

tff(c_4487,plain,(
    ! [B_446] :
      ( k1_relat_1(B_446) = k1_xboole_0
      | ~ v4_relat_1(B_446,k1_xboole_0)
      | ~ v1_relat_1(B_446) ) ),
    inference(resolution,[status(thm)],[c_4476,c_966])).

tff(c_6422,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6418,c_4487])).

tff(c_6425,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_6422])).

tff(c_46,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_34,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_79,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_6553,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_6556,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_6553])).

tff(c_6560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6556])).

tff(c_6562,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8912,plain,(
    ! [B_798,C_799] :
      ( k1_relset_1(k1_xboole_0,B_798,C_799) = k1_relat_1(C_799)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8871])).

tff(c_8914,plain,(
    ! [B_798] : k1_relset_1(k1_xboole_0,B_798,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6562,c_8912])).

tff(c_8919,plain,(
    ! [B_798] : k1_relset_1(k1_xboole_0,B_798,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6425,c_8914])).

tff(c_50,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8928,plain,(
    ! [C_801,B_802] :
      ( v1_funct_2(C_801,k1_xboole_0,B_802)
      | k1_relset_1(k1_xboole_0,B_802,C_801) != k1_xboole_0
      | ~ m1_subset_1(C_801,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_8930,plain,(
    ! [B_802] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_802)
      | k1_relset_1(k1_xboole_0,B_802,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6562,c_8928])).

tff(c_8936,plain,(
    ! [B_802] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_802) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8919,c_8930])).

tff(c_9870,plain,(
    ! [B_802] : v1_funct_2('#skF_3','#skF_3',B_802) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9854,c_9854,c_8936])).

tff(c_9884,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9854,c_9854,c_6425])).

tff(c_9898,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9854,c_9854,c_14])).

tff(c_9855,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9702])).

tff(c_10391,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9884,c_9898,c_9855])).

tff(c_10190,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9898,c_8645])).

tff(c_10393,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10391,c_10190])).

tff(c_10400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9870,c_10393])).

tff(c_10401,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9563])).

tff(c_10443,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10401,c_2])).

tff(c_10445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_10443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/2.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.82  
% 7.97/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.97/2.82  
% 7.97/2.82  %Foreground sorts:
% 7.97/2.82  
% 7.97/2.82  
% 7.97/2.82  %Background operators:
% 7.97/2.82  
% 7.97/2.82  
% 7.97/2.82  %Foreground operators:
% 7.97/2.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.97/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/2.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.97/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.97/2.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.97/2.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.97/2.82  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.97/2.82  tff('#skF_5', type, '#skF_5': $i).
% 7.97/2.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.97/2.82  tff('#skF_2', type, '#skF_2': $i).
% 7.97/2.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.97/2.82  tff('#skF_3', type, '#skF_3': $i).
% 7.97/2.82  tff('#skF_1', type, '#skF_1': $i).
% 7.97/2.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.97/2.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.97/2.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.97/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/2.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.97/2.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.97/2.82  tff('#skF_4', type, '#skF_4': $i).
% 7.97/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/2.82  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.97/2.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.97/2.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.97/2.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.97/2.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.97/2.82  
% 8.24/2.85  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 8.24/2.85  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.24/2.85  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.24/2.85  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.24/2.85  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 8.24/2.85  tff(f_126, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.24/2.85  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.24/2.85  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.24/2.85  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 8.24/2.85  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 8.24/2.85  tff(f_54, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 8.24/2.85  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 8.24/2.85  tff(f_120, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 8.24/2.85  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.24/2.85  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.24/2.85  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.24/2.85  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.24/2.85  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.24/2.85  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.24/2.85  tff(c_76, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.24/2.85  tff(c_68, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.24/2.85  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.24/2.85  tff(c_129, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.24/2.85  tff(c_142, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_129])).
% 8.24/2.85  tff(c_72, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.24/2.85  tff(c_6857, plain, (![A_655, B_656, C_657]: (k1_relset_1(A_655, B_656, C_657)=k1_relat_1(C_657) | ~m1_subset_1(C_657, k1_zfmisc_1(k2_zfmisc_1(A_655, B_656))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.24/2.85  tff(c_6876, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_6857])).
% 8.24/2.85  tff(c_7760, plain, (![B_752, A_753, C_754]: (k1_xboole_0=B_752 | k1_relset_1(A_753, B_752, C_754)=A_753 | ~v1_funct_2(C_754, A_753, B_752) | ~m1_subset_1(C_754, k1_zfmisc_1(k2_zfmisc_1(A_753, B_752))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.24/2.85  tff(c_7773, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_7760])).
% 8.24/2.85  tff(c_7786, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6876, c_7773])).
% 8.24/2.85  tff(c_7788, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_7786])).
% 8.24/2.85  tff(c_32, plain, (![B_17, A_16]: (k1_relat_1(k7_relat_1(B_17, A_16))=A_16 | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.24/2.85  tff(c_7811, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_5', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7788, c_32])).
% 8.24/2.85  tff(c_8089, plain, (![A_767]: (k1_relat_1(k7_relat_1('#skF_5', A_767))=A_767 | ~r1_tarski(A_767, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_7811])).
% 8.24/2.85  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.24/2.85  tff(c_7606, plain, (![A_740, B_741, C_742, D_743]: (k2_partfun1(A_740, B_741, C_742, D_743)=k7_relat_1(C_742, D_743) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1(A_740, B_741))) | ~v1_funct_1(C_742))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.24/2.85  tff(c_7615, plain, (![D_743]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_743)=k7_relat_1('#skF_5', D_743) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_7606])).
% 8.24/2.85  tff(c_7627, plain, (![D_743]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_743)=k7_relat_1('#skF_5', D_743))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_7615])).
% 8.24/2.85  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.24/2.85  tff(c_5229, plain, (![A_528, B_529, C_530, D_531]: (k7_relset_1(A_528, B_529, C_530, D_531)=k9_relat_1(C_530, D_531) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_528, B_529))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.24/2.85  tff(c_5241, plain, (![D_532]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_532)=k9_relat_1('#skF_5', D_532))), inference(resolution, [status(thm)], [c_70, c_5229])).
% 8.24/2.85  tff(c_3076, plain, (![A_339, B_340, C_341]: (k1_relset_1(A_339, B_340, C_341)=k1_relat_1(C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.24/2.85  tff(c_3095, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_3076])).
% 8.24/2.85  tff(c_3846, plain, (![B_419, A_420, C_421]: (k1_xboole_0=B_419 | k1_relset_1(A_420, B_419, C_421)=A_420 | ~v1_funct_2(C_421, A_420, B_419) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(A_420, B_419))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.24/2.85  tff(c_3859, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_3846])).
% 8.24/2.85  tff(c_3871, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3095, c_3859])).
% 8.24/2.85  tff(c_3873, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_3871])).
% 8.24/2.85  tff(c_3890, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_5', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3873, c_32])).
% 8.24/2.85  tff(c_4174, plain, (![A_437]: (k1_relat_1(k7_relat_1('#skF_5', A_437))=A_437 | ~r1_tarski(A_437, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_3890])).
% 8.24/2.85  tff(c_3744, plain, (![A_413, B_414, C_415, D_416]: (k2_partfun1(A_413, B_414, C_415, D_416)=k7_relat_1(C_415, D_416) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))) | ~v1_funct_1(C_415))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.24/2.85  tff(c_3753, plain, (![D_416]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_416)=k7_relat_1('#skF_5', D_416) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_3744])).
% 8.24/2.85  tff(c_3765, plain, (![D_416]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_416)=k7_relat_1('#skF_5', D_416))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3753])).
% 8.24/2.85  tff(c_1674, plain, (![A_218, B_219, C_220, D_221]: (k7_relset_1(A_218, B_219, C_220, D_221)=k9_relat_1(C_220, D_221) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.24/2.85  tff(c_1685, plain, (![D_221]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_221)=k9_relat_1('#skF_5', D_221))), inference(resolution, [status(thm)], [c_70, c_1674])).
% 8.24/2.85  tff(c_66, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.24/2.85  tff(c_1687, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1685, c_66])).
% 8.24/2.85  tff(c_28, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.24/2.85  tff(c_30, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.24/2.85  tff(c_26, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.24/2.85  tff(c_2077, plain, (![A_268, B_269, C_270, D_271]: (k2_partfun1(A_268, B_269, C_270, D_271)=k7_relat_1(C_270, D_271) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))) | ~v1_funct_1(C_270))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.24/2.85  tff(c_2084, plain, (![D_271]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_271)=k7_relat_1('#skF_5', D_271) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_2077])).
% 8.24/2.85  tff(c_2093, plain, (![D_271]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_271)=k7_relat_1('#skF_5', D_271))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2084])).
% 8.24/2.85  tff(c_1909, plain, (![C_252, A_253, B_254]: (m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~r1_tarski(k2_relat_1(C_252), B_254) | ~r1_tarski(k1_relat_1(C_252), A_253) | ~v1_relat_1(C_252))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.24/2.85  tff(c_908, plain, (![A_141, B_142, C_143, D_144]: (v1_funct_1(k2_partfun1(A_141, B_142, C_143, D_144)) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(C_143))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.24/2.85  tff(c_913, plain, (![D_144]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_144)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_908])).
% 8.24/2.85  tff(c_921, plain, (![D_144]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_144)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_913])).
% 8.24/2.85  tff(c_64, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.24/2.85  tff(c_143, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_64])).
% 8.24/2.85  tff(c_924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_921, c_143])).
% 8.24/2.85  tff(c_925, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_64])).
% 8.24/2.85  tff(c_1067, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_925])).
% 8.24/2.85  tff(c_1941, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_1909, c_1067])).
% 8.24/2.85  tff(c_2356, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_2093, c_2093, c_1941])).
% 8.24/2.85  tff(c_2357, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2356])).
% 8.24/2.85  tff(c_2360, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_2357])).
% 8.24/2.85  tff(c_2364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_2360])).
% 8.24/2.85  tff(c_2366, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitRight, [status(thm)], [c_2356])).
% 8.24/2.85  tff(c_44, plain, (![C_33, A_31, B_32]: (m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~r1_tarski(k2_relat_1(C_33), B_32) | ~r1_tarski(k1_relat_1(C_33), A_31) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.24/2.85  tff(c_2096, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_1067])).
% 8.24/2.85  tff(c_2113, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_2096])).
% 8.24/2.85  tff(c_2464, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2366, c_2113])).
% 8.24/2.85  tff(c_2465, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_2464])).
% 8.24/2.85  tff(c_2493, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_2465])).
% 8.24/2.85  tff(c_2500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_2493])).
% 8.24/2.85  tff(c_2501, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_2464])).
% 8.24/2.85  tff(c_2565, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_2501])).
% 8.24/2.85  tff(c_2568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_1687, c_2565])).
% 8.24/2.85  tff(c_2569, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_925])).
% 8.24/2.85  tff(c_3776, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3765, c_2569])).
% 8.24/2.85  tff(c_2570, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_925])).
% 8.24/2.85  tff(c_3093, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_2570, c_3076])).
% 8.24/2.85  tff(c_3769, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3765, c_3765, c_3093])).
% 8.24/2.85  tff(c_3775, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3765, c_2570])).
% 8.24/2.85  tff(c_3974, plain, (![B_422, C_423, A_424]: (k1_xboole_0=B_422 | v1_funct_2(C_423, A_424, B_422) | k1_relset_1(A_424, B_422, C_423)!=A_424 | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_424, B_422))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.24/2.85  tff(c_3977, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_3775, c_3974])).
% 8.24/2.85  tff(c_3995, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3769, c_3977])).
% 8.24/2.85  tff(c_3996, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3776, c_3995])).
% 8.24/2.85  tff(c_4050, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_3996])).
% 8.24/2.85  tff(c_4180, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4174, c_4050])).
% 8.24/2.85  tff(c_4264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_4180])).
% 8.24/2.85  tff(c_4265, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3996])).
% 8.24/2.85  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.24/2.85  tff(c_4311, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_10])).
% 8.24/2.85  tff(c_3431, plain, (![A_384, B_385, C_386, D_387]: (k7_relset_1(A_384, B_385, C_386, D_387)=k9_relat_1(C_386, D_387) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.24/2.85  tff(c_3445, plain, (![D_387]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_387)=k9_relat_1('#skF_5', D_387))), inference(resolution, [status(thm)], [c_70, c_3431])).
% 8.24/2.85  tff(c_949, plain, (![B_147, A_148]: (B_147=A_148 | ~r1_tarski(B_147, A_148) | ~r1_tarski(A_148, B_147))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.24/2.85  tff(c_963, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_949])).
% 8.24/2.85  tff(c_973, plain, (~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_963])).
% 8.24/2.85  tff(c_3446, plain, (~r1_tarski('#skF_3', k9_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3445, c_973])).
% 8.24/2.85  tff(c_4403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4311, c_3446])).
% 8.24/2.85  tff(c_4404, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3871])).
% 8.24/2.85  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.24/2.85  tff(c_4447, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4404, c_2])).
% 8.24/2.85  tff(c_4449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_4447])).
% 8.24/2.85  tff(c_4450, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_963])).
% 8.24/2.85  tff(c_5247, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5241, c_4450])).
% 8.24/2.85  tff(c_5497, plain, (![A_558, B_559, C_560, D_561]: (k2_partfun1(A_558, B_559, C_560, D_561)=k7_relat_1(C_560, D_561) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(A_558, B_559))) | ~v1_funct_1(C_560))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.24/2.85  tff(c_5504, plain, (![D_561]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_561)=k7_relat_1('#skF_5', D_561) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_5497])).
% 8.24/2.85  tff(c_5513, plain, (![D_561]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_561)=k7_relat_1('#skF_5', D_561))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5504])).
% 8.24/2.85  tff(c_5375, plain, (![C_544, A_545, B_546]: (m1_subset_1(C_544, k1_zfmisc_1(k2_zfmisc_1(A_545, B_546))) | ~r1_tarski(k2_relat_1(C_544), B_546) | ~r1_tarski(k1_relat_1(C_544), A_545) | ~v1_relat_1(C_544))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.24/2.85  tff(c_4529, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_925])).
% 8.24/2.85  tff(c_5407, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_5375, c_4529])).
% 8.24/2.85  tff(c_5746, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5513, c_5513, c_5513, c_5407])).
% 8.24/2.85  tff(c_5747, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_5746])).
% 8.24/2.85  tff(c_5750, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_5747])).
% 8.24/2.85  tff(c_5754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_5750])).
% 8.24/2.85  tff(c_5756, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitRight, [status(thm)], [c_5746])).
% 8.24/2.85  tff(c_5516, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5513, c_4529])).
% 8.24/2.85  tff(c_5533, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_5516])).
% 8.24/2.85  tff(c_5949, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5756, c_5533])).
% 8.24/2.85  tff(c_5950, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_5949])).
% 8.24/2.85  tff(c_6073, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_5950])).
% 8.24/2.85  tff(c_6080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_6073])).
% 8.24/2.85  tff(c_6081, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_5949])).
% 8.24/2.85  tff(c_6292, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_6081])).
% 8.24/2.85  tff(c_6295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_8, c_5247, c_6292])).
% 8.24/2.85  tff(c_6297, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_925])).
% 8.24/2.85  tff(c_6874, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_6297, c_6857])).
% 8.24/2.85  tff(c_7631, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7627, c_7627, c_6874])).
% 8.24/2.85  tff(c_6296, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_925])).
% 8.24/2.85  tff(c_7638, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7627, c_6296])).
% 8.24/2.85  tff(c_7637, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_7627, c_6297])).
% 8.24/2.85  tff(c_52, plain, (![B_35, C_36, A_34]: (k1_xboole_0=B_35 | v1_funct_2(C_36, A_34, B_35) | k1_relset_1(A_34, B_35, C_36)!=A_34 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.24/2.85  tff(c_7695, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_7637, c_52])).
% 8.24/2.85  tff(c_7719, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_7638, c_7695])).
% 8.24/2.85  tff(c_7738, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_7719])).
% 8.24/2.85  tff(c_7853, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7631, c_7738])).
% 8.24/2.85  tff(c_8095, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8089, c_7853])).
% 8.24/2.85  tff(c_8185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_8095])).
% 8.24/2.85  tff(c_8186, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_7786])).
% 8.24/2.85  tff(c_8232, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8186, c_2])).
% 8.24/2.85  tff(c_8234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_8232])).
% 8.24/2.85  tff(c_8235, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_7719])).
% 8.24/2.85  tff(c_8278, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8235, c_10])).
% 8.24/2.85  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.24/2.85  tff(c_8277, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8235, c_8235, c_14])).
% 8.24/2.85  tff(c_18, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.24/2.85  tff(c_6417, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6297, c_18])).
% 8.24/2.85  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.24/2.85  tff(c_6526, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_6417, c_4])).
% 8.24/2.85  tff(c_6581, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_6526])).
% 8.24/2.85  tff(c_7632, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7627, c_6581])).
% 8.24/2.85  tff(c_8556, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8277, c_7632])).
% 8.24/2.85  tff(c_8560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8278, c_8556])).
% 8.24/2.85  tff(c_8561, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_6526])).
% 8.24/2.85  tff(c_8645, plain, (~v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8561, c_6296])).
% 8.24/2.85  tff(c_20, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.24/2.85  tff(c_8871, plain, (![A_794, B_795, C_796]: (k1_relset_1(A_794, B_795, C_796)=k1_relat_1(C_796) | ~m1_subset_1(C_796, k1_zfmisc_1(k2_zfmisc_1(A_794, B_795))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.24/2.85  tff(c_9255, plain, (![A_843, B_844, A_845]: (k1_relset_1(A_843, B_844, A_845)=k1_relat_1(A_845) | ~r1_tarski(A_845, k2_zfmisc_1(A_843, B_844)))), inference(resolution, [status(thm)], [c_20, c_8871])).
% 8.24/2.85  tff(c_9287, plain, (![A_843, B_844]: (k1_relset_1(A_843, B_844, k2_zfmisc_1(A_843, B_844))=k1_relat_1(k2_zfmisc_1(A_843, B_844)))), inference(resolution, [status(thm)], [c_8, c_9255])).
% 8.24/2.85  tff(c_8644, plain, (m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8561, c_6297])).
% 8.24/2.85  tff(c_9679, plain, (![B_873, C_874, A_875]: (k1_xboole_0=B_873 | v1_funct_2(C_874, A_875, B_873) | k1_relset_1(A_875, B_873, C_874)!=A_875 | ~m1_subset_1(C_874, k1_zfmisc_1(k2_zfmisc_1(A_875, B_873))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.24/2.85  tff(c_9685, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_8644, c_9679])).
% 8.24/2.85  tff(c_9701, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9287, c_9685])).
% 8.24/2.85  tff(c_9702, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_8645, c_9701])).
% 8.24/2.85  tff(c_9739, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_9702])).
% 8.24/2.85  tff(c_9466, plain, (![A_863, B_864, C_865, D_866]: (k2_partfun1(A_863, B_864, C_865, D_866)=k7_relat_1(C_865, D_866) | ~m1_subset_1(C_865, k1_zfmisc_1(k2_zfmisc_1(A_863, B_864))) | ~v1_funct_1(C_865))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.24/2.85  tff(c_9475, plain, (![D_866]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_866)=k7_relat_1('#skF_5', D_866) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_9466])).
% 8.24/2.85  tff(c_9489, plain, (![D_867]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_867)=k7_relat_1('#skF_5', D_867))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_9475])).
% 8.24/2.85  tff(c_9495, plain, (k7_relat_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9489, c_8561])).
% 8.24/2.85  tff(c_8890, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_8871])).
% 8.24/2.85  tff(c_9537, plain, (![B_869, A_870, C_871]: (k1_xboole_0=B_869 | k1_relset_1(A_870, B_869, C_871)=A_870 | ~v1_funct_2(C_871, A_870, B_869) | ~m1_subset_1(C_871, k1_zfmisc_1(k2_zfmisc_1(A_870, B_869))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.24/2.85  tff(c_9550, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_9537])).
% 8.24/2.85  tff(c_9563, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8890, c_9550])).
% 8.24/2.85  tff(c_9565, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_9563])).
% 8.24/2.85  tff(c_9579, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_5', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9565, c_32])).
% 8.24/2.85  tff(c_9740, plain, (![A_877]: (k1_relat_1(k7_relat_1('#skF_5', A_877))=A_877 | ~r1_tarski(A_877, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_9579])).
% 8.24/2.85  tff(c_9814, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9495, c_9740])).
% 8.24/2.85  tff(c_9851, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_9814])).
% 8.24/2.85  tff(c_9853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9739, c_9851])).
% 8.24/2.85  tff(c_9854, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_9702])).
% 8.24/2.85  tff(c_927, plain, (![C_145]: (v1_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_129])).
% 8.24/2.85  tff(c_933, plain, (![A_146]: (v1_relat_1(A_146) | ~r1_tarski(A_146, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_927])).
% 8.24/2.85  tff(c_947, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_933])).
% 8.24/2.85  tff(c_6327, plain, (![C_612, A_613, B_614]: (v4_relat_1(C_612, A_613) | ~m1_subset_1(C_612, k1_zfmisc_1(k2_zfmisc_1(A_613, B_614))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.24/2.85  tff(c_6374, plain, (![A_623, A_624, B_625]: (v4_relat_1(A_623, A_624) | ~r1_tarski(A_623, k2_zfmisc_1(A_624, B_625)))), inference(resolution, [status(thm)], [c_20, c_6327])).
% 8.24/2.85  tff(c_6418, plain, (![A_626]: (v4_relat_1(k1_xboole_0, A_626))), inference(resolution, [status(thm)], [c_10, c_6374])).
% 8.24/2.85  tff(c_4476, plain, (![B_446, A_447]: (r1_tarski(k1_relat_1(B_446), A_447) | ~v4_relat_1(B_446, A_447) | ~v1_relat_1(B_446))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.24/2.85  tff(c_966, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_949])).
% 8.24/2.85  tff(c_4487, plain, (![B_446]: (k1_relat_1(B_446)=k1_xboole_0 | ~v4_relat_1(B_446, k1_xboole_0) | ~v1_relat_1(B_446))), inference(resolution, [status(thm)], [c_4476, c_966])).
% 8.24/2.85  tff(c_6422, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6418, c_4487])).
% 8.24/2.85  tff(c_6425, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_947, c_6422])).
% 8.24/2.85  tff(c_46, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_34, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.24/2.85  tff(c_79, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 8.24/2.85  tff(c_6553, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_79])).
% 8.24/2.85  tff(c_6556, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_6553])).
% 8.24/2.85  tff(c_6560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_6556])).
% 8.24/2.85  tff(c_6562, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_79])).
% 8.24/2.85  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.24/2.85  tff(c_8912, plain, (![B_798, C_799]: (k1_relset_1(k1_xboole_0, B_798, C_799)=k1_relat_1(C_799) | ~m1_subset_1(C_799, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8871])).
% 8.24/2.85  tff(c_8914, plain, (![B_798]: (k1_relset_1(k1_xboole_0, B_798, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6562, c_8912])).
% 8.24/2.85  tff(c_8919, plain, (![B_798]: (k1_relset_1(k1_xboole_0, B_798, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6425, c_8914])).
% 8.24/2.85  tff(c_50, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.24/2.85  tff(c_8928, plain, (![C_801, B_802]: (v1_funct_2(C_801, k1_xboole_0, B_802) | k1_relset_1(k1_xboole_0, B_802, C_801)!=k1_xboole_0 | ~m1_subset_1(C_801, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 8.24/2.85  tff(c_8930, plain, (![B_802]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_802) | k1_relset_1(k1_xboole_0, B_802, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6562, c_8928])).
% 8.24/2.85  tff(c_8936, plain, (![B_802]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_802))), inference(demodulation, [status(thm), theory('equality')], [c_8919, c_8930])).
% 8.24/2.85  tff(c_9870, plain, (![B_802]: (v1_funct_2('#skF_3', '#skF_3', B_802))), inference(demodulation, [status(thm), theory('equality')], [c_9854, c_9854, c_8936])).
% 8.24/2.85  tff(c_9884, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9854, c_9854, c_6425])).
% 8.24/2.85  tff(c_9898, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9854, c_9854, c_14])).
% 8.24/2.85  tff(c_9855, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_9702])).
% 8.24/2.85  tff(c_10391, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9884, c_9898, c_9855])).
% 8.24/2.85  tff(c_10190, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9898, c_8645])).
% 8.24/2.85  tff(c_10393, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10391, c_10190])).
% 8.24/2.85  tff(c_10400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9870, c_10393])).
% 8.24/2.85  tff(c_10401, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_9563])).
% 8.24/2.85  tff(c_10443, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10401, c_2])).
% 8.24/2.85  tff(c_10445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_10443])).
% 8.24/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.85  
% 8.24/2.85  Inference rules
% 8.24/2.85  ----------------------
% 8.24/2.85  #Ref     : 0
% 8.24/2.85  #Sup     : 2274
% 8.24/2.85  #Fact    : 0
% 8.24/2.85  #Define  : 0
% 8.24/2.85  #Split   : 44
% 8.24/2.85  #Chain   : 0
% 8.24/2.85  #Close   : 0
% 8.24/2.85  
% 8.24/2.85  Ordering : KBO
% 8.24/2.85  
% 8.24/2.85  Simplification rules
% 8.24/2.85  ----------------------
% 8.24/2.85  #Subsume      : 215
% 8.24/2.85  #Demod        : 2146
% 8.24/2.85  #Tautology    : 937
% 8.24/2.85  #SimpNegUnit  : 8
% 8.24/2.85  #BackRed      : 331
% 8.24/2.85  
% 8.24/2.85  #Partial instantiations: 0
% 8.24/2.85  #Strategies tried      : 1
% 8.24/2.85  
% 8.24/2.85  Timing (in seconds)
% 8.24/2.85  ----------------------
% 8.24/2.85  Preprocessing        : 0.40
% 8.24/2.85  Parsing              : 0.22
% 8.24/2.85  CNF conversion       : 0.02
% 8.24/2.85  Main loop            : 1.54
% 8.24/2.85  Inferencing          : 0.52
% 8.24/2.85  Reduction            : 0.55
% 8.24/2.85  Demodulation         : 0.40
% 8.24/2.85  BG Simplification    : 0.06
% 8.24/2.85  Subsumption          : 0.27
% 8.24/2.85  Abstraction          : 0.06
% 8.24/2.85  MUC search           : 0.00
% 8.24/2.85  Cooper               : 0.00
% 8.24/2.85  Total                : 2.01
% 8.24/2.85  Index Insertion      : 0.00
% 8.24/2.85  Index Deletion       : 0.00
% 8.24/2.86  Index Matching       : 0.00
% 8.24/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------

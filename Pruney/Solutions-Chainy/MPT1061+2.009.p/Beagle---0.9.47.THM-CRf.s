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
% DateTime   : Thu Dec  3 10:17:37 EST 2020

% Result     : Theorem 9.17s
% Output     : CNFRefutation 9.39s
% Verified   : 
% Statistics : Number of formulae       :  342 (6397 expanded)
%              Number of leaves         :   50 (1886 expanded)
%              Depth                    :   24
%              Number of atoms          :  552 (16291 expanded)
%              Number of equality atoms :  186 (2660 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_132,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_146,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1433,plain,(
    ! [C_210,A_211,B_212] :
      ( v1_relat_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1446,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_1433])).

tff(c_12456,plain,(
    ! [A_1054,B_1055,C_1056,D_1057] :
      ( k7_relset_1(A_1054,B_1055,C_1056,D_1057) = k9_relat_1(C_1056,D_1057)
      | ~ m1_subset_1(C_1056,k1_zfmisc_1(k2_zfmisc_1(A_1054,B_1055))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12468,plain,(
    ! [D_1058] : k7_relset_1('#skF_2','#skF_5','#skF_6',D_1058) = k9_relat_1('#skF_6',D_1058) ),
    inference(resolution,[status(thm)],[c_82,c_12456])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3470,plain,(
    ! [C_404,B_405,A_406] :
      ( ~ v1_xboole_0(C_404)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(C_404))
      | ~ r2_hidden(A_406,B_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3483,plain,(
    ! [B_407,A_408,A_409] :
      ( ~ v1_xboole_0(B_407)
      | ~ r2_hidden(A_408,A_409)
      | ~ r1_tarski(A_409,B_407) ) ),
    inference(resolution,[status(thm)],[c_24,c_3470])).

tff(c_3487,plain,(
    ! [B_410,A_411,B_412] :
      ( ~ v1_xboole_0(B_410)
      | ~ r1_tarski(A_411,B_410)
      | r1_tarski(A_411,B_412) ) ),
    inference(resolution,[status(thm)],[c_6,c_3483])).

tff(c_3544,plain,(
    ! [B_415,B_416] :
      ( ~ v1_xboole_0(B_415)
      | r1_tarski(B_415,B_416) ) ),
    inference(resolution,[status(thm)],[c_14,c_3487])).

tff(c_78,plain,(
    r1_tarski(k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_145,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_154,plain,
    ( k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4',k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_145])).

tff(c_1453,plain,(
    ~ r1_tarski('#skF_4',k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_3588,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3544,c_1453])).

tff(c_80,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_3898,plain,(
    ! [A_439,B_440,C_441] :
      ( k1_relset_1(A_439,B_440,C_441) = k1_relat_1(C_441)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_439,B_440))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3917,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_3898])).

tff(c_4671,plain,(
    ! [B_497,A_498,C_499] :
      ( k1_xboole_0 = B_497
      | k1_relset_1(A_498,B_497,C_499) = A_498
      | ~ v1_funct_2(C_499,A_498,B_497)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k2_zfmisc_1(A_498,B_497))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4684,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_4671])).

tff(c_4692,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3917,c_4684])).

tff(c_4694,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4692])).

tff(c_44,plain,(
    ! [B_28,A_27] :
      ( k1_relat_1(k7_relat_1(B_28,A_27)) = A_27
      | ~ r1_tarski(A_27,k1_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4704,plain,(
    ! [A_27] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_27)) = A_27
      | ~ r1_tarski(A_27,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4694,c_44])).

tff(c_4724,plain,(
    ! [A_27] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_27)) = A_27
      | ~ r1_tarski(A_27,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_4704])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4628,plain,(
    ! [A_491,B_492,C_493,D_494] :
      ( k2_partfun1(A_491,B_492,C_493,D_494) = k7_relat_1(C_493,D_494)
      | ~ m1_subset_1(C_493,k1_zfmisc_1(k2_zfmisc_1(A_491,B_492)))
      | ~ v1_funct_1(C_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4639,plain,(
    ! [D_494] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_494) = k7_relat_1('#skF_6',D_494)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_4628])).

tff(c_4649,plain,(
    ! [D_494] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_494) = k7_relat_1('#skF_6',D_494) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4639])).

tff(c_2050,plain,(
    ! [A_299,B_300,C_301] :
      ( k1_relset_1(A_299,B_300,C_301) = k1_relat_1(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2065,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_2050])).

tff(c_2875,plain,(
    ! [B_359,A_360,C_361] :
      ( k1_xboole_0 = B_359
      | k1_relset_1(A_360,B_359,C_361) = A_360
      | ~ v1_funct_2(C_361,A_360,B_359)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_360,B_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2888,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_2875])).

tff(c_2896,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2065,c_2888])).

tff(c_2898,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2896])).

tff(c_2906,plain,(
    ! [A_27] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_27)) = A_27
      | ~ r1_tarski(A_27,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2898,c_44])).

tff(c_2926,plain,(
    ! [A_27] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_27)) = A_27
      | ~ r1_tarski(A_27,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_2906])).

tff(c_2221,plain,(
    ! [A_308,B_309,C_310,D_311] :
      ( k7_relset_1(A_308,B_309,C_310,D_311) = k9_relat_1(C_310,D_311)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2232,plain,(
    ! [D_311] : k7_relset_1('#skF_2','#skF_5','#skF_6',D_311) = k9_relat_1('#skF_6',D_311) ),
    inference(resolution,[status(thm)],[c_82,c_2221])).

tff(c_2241,plain,(
    r1_tarski(k9_relat_1('#skF_6','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2232,c_78])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( k2_relat_1(k7_relat_1(B_24,A_23)) = k9_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k7_relat_1(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2727,plain,(
    ! [C_345,A_346,B_347] :
      ( m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(A_346,B_347)))
      | ~ r1_tarski(k2_relat_1(C_345),B_347)
      | ~ r1_tarski(k1_relat_1(C_345),A_346)
      | ~ v1_relat_1(C_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2691,plain,(
    ! [A_339,B_340,C_341,D_342] :
      ( k2_partfun1(A_339,B_340,C_341,D_342) = k7_relat_1(C_341,D_342)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340)))
      | ~ v1_funct_1(C_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2698,plain,(
    ! [D_342] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_342) = k7_relat_1('#skF_6',D_342)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_2691])).

tff(c_2704,plain,(
    ! [D_342] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_342) = k7_relat_1('#skF_6',D_342) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2698])).

tff(c_1402,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( v1_funct_1(k2_partfun1(A_200,B_201,C_202,D_203))
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_1(C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1409,plain,(
    ! [D_203] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6',D_203))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_1402])).

tff(c_1415,plain,(
    ! [D_203] : v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6',D_203)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1409])).

tff(c_76,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_162,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_1418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1415,c_162])).

tff(c_1419,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1506,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1419])).

tff(c_2708,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2704,c_1506])).

tff(c_2760,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2727,c_2708])).

tff(c_2809,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2760])).

tff(c_2812,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_2809])).

tff(c_2816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_2812])).

tff(c_2817,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2760])).

tff(c_3164,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2817])).

tff(c_3170,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_6','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3164])).

tff(c_3179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_2241,c_3170])).

tff(c_3180,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2817])).

tff(c_3205,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2926,c_3180])).

tff(c_3220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_14,c_3205])).

tff(c_3221,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2896])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3270,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3221,c_8])).

tff(c_3272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3270])).

tff(c_3274,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1419])).

tff(c_3915,plain,(
    k1_relset_1('#skF_3','#skF_4',k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) = k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3274,c_3898])).

tff(c_4653,plain,(
    k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) = k1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4649,c_4649,c_3915])).

tff(c_3273,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1419])).

tff(c_4660,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4649,c_3273])).

tff(c_4659,plain,(
    m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4649,c_3274])).

tff(c_64,plain,(
    ! [B_46,C_47,A_45] :
      ( k1_xboole_0 = B_46
      | v1_funct_2(C_47,A_45,B_46)
      | k1_relset_1(A_45,B_46,C_47) != A_45
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4859,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4659,c_64])).

tff(c_4888,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4660,c_4859])).

tff(c_5040,plain,(
    k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4888])).

tff(c_5180,plain,(
    k1_relat_1(k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4653,c_5040])).

tff(c_5187,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4724,c_5180])).

tff(c_5194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5187])).

tff(c_5195,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4888])).

tff(c_5247,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5195,c_8])).

tff(c_5249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3588,c_5247])).

tff(c_5250,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4692])).

tff(c_5298,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_8])).

tff(c_5300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5298])).

tff(c_5301,plain,(
    k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_12474,plain,(
    k9_relat_1('#skF_6','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_12468,c_5301])).

tff(c_38,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10115,plain,(
    ! [A_912,B_913,C_914,D_915] :
      ( k7_relset_1(A_912,B_913,C_914,D_915) = k9_relat_1(C_914,D_915)
      | ~ m1_subset_1(C_914,k1_zfmisc_1(k2_zfmisc_1(A_912,B_913))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10130,plain,(
    ! [D_916] : k7_relset_1('#skF_2','#skF_5','#skF_6',D_916) = k9_relat_1('#skF_6',D_916) ),
    inference(resolution,[status(thm)],[c_82,c_10115])).

tff(c_10136,plain,(
    k9_relat_1('#skF_6','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10130,c_5301])).

tff(c_10400,plain,(
    ! [A_941,B_942,C_943,D_944] :
      ( k2_partfun1(A_941,B_942,C_943,D_944) = k7_relat_1(C_943,D_944)
      | ~ m1_subset_1(C_943,k1_zfmisc_1(k2_zfmisc_1(A_941,B_942)))
      | ~ v1_funct_1(C_943) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_10411,plain,(
    ! [D_944] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_944) = k7_relat_1('#skF_6',D_944)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_10400])).

tff(c_10447,plain,(
    ! [D_946] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_946) = k7_relat_1('#skF_6',D_946) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_10411])).

tff(c_7284,plain,(
    ! [A_732,B_733,C_734] :
      ( k1_relset_1(A_732,B_733,C_734) = k1_relat_1(C_734)
      | ~ m1_subset_1(C_734,k1_zfmisc_1(k2_zfmisc_1(A_732,B_733))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7303,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_7284])).

tff(c_8262,plain,(
    ! [B_801,A_802,C_803] :
      ( k1_xboole_0 = B_801
      | k1_relset_1(A_802,B_801,C_803) = A_802
      | ~ v1_funct_2(C_803,A_802,B_801)
      | ~ m1_subset_1(C_803,k1_zfmisc_1(k2_zfmisc_1(A_802,B_801))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8278,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_8262])).

tff(c_8288,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7303,c_8278])).

tff(c_8290,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8288])).

tff(c_8298,plain,(
    ! [A_27] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_27)) = A_27
      | ~ r1_tarski(A_27,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8290,c_44])).

tff(c_8514,plain,(
    ! [A_811] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_811)) = A_811
      | ~ r1_tarski(A_811,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_8298])).

tff(c_8009,plain,(
    ! [A_780,B_781,C_782,D_783] :
      ( k2_partfun1(A_780,B_781,C_782,D_783) = k7_relat_1(C_782,D_783)
      | ~ m1_subset_1(C_782,k1_zfmisc_1(k2_zfmisc_1(A_780,B_781)))
      | ~ v1_funct_1(C_782) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_8018,plain,(
    ! [D_783] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_783) = k7_relat_1('#skF_6',D_783)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_8009])).

tff(c_8027,plain,(
    ! [D_783] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_783) = k7_relat_1('#skF_6',D_783) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8018])).

tff(c_42,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_26,A_25)),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6056,plain,(
    ! [A_617,B_618,C_619,D_620] :
      ( k7_relset_1(A_617,B_618,C_619,D_620) = k9_relat_1(C_619,D_620)
      | ~ m1_subset_1(C_619,k1_zfmisc_1(k2_zfmisc_1(A_617,B_618))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6075,plain,(
    ! [D_622] : k7_relset_1('#skF_2','#skF_5','#skF_6',D_622) = k9_relat_1('#skF_6',D_622) ),
    inference(resolution,[status(thm)],[c_82,c_6056])).

tff(c_6081,plain,(
    k9_relat_1('#skF_6','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6075,c_5301])).

tff(c_6265,plain,(
    ! [C_633,A_634,B_635] :
      ( m1_subset_1(C_633,k1_zfmisc_1(k2_zfmisc_1(A_634,B_635)))
      | ~ r1_tarski(k2_relat_1(C_633),B_635)
      | ~ r1_tarski(k1_relat_1(C_633),A_634)
      | ~ v1_relat_1(C_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6130,plain,(
    ! [A_624,B_625,C_626,D_627] :
      ( k2_partfun1(A_624,B_625,C_626,D_627) = k7_relat_1(C_626,D_627)
      | ~ m1_subset_1(C_626,k1_zfmisc_1(k2_zfmisc_1(A_624,B_625)))
      | ~ v1_funct_1(C_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_6137,plain,(
    ! [D_627] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_627) = k7_relat_1('#skF_6',D_627)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_6130])).

tff(c_6143,plain,(
    ! [D_627] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_627) = k7_relat_1('#skF_6',D_627) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6137])).

tff(c_5303,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1419])).

tff(c_6147,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6143,c_5303])).

tff(c_6298,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6265,c_6147])).

tff(c_6443,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6298])).

tff(c_6446,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_6443])).

tff(c_6450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_6446])).

tff(c_6451,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6298])).

tff(c_6581,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6451])).

tff(c_6587,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_6','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6581])).

tff(c_6596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_14,c_6081,c_6587])).

tff(c_6597,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_6451])).

tff(c_6631,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_6597])).

tff(c_6641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_6631])).

tff(c_6642,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1419])).

tff(c_8038,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8027,c_6642])).

tff(c_6643,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1419])).

tff(c_7301,plain,(
    k1_relset_1('#skF_3','#skF_4',k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) = k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6643,c_7284])).

tff(c_8031,plain,(
    k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) = k1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8027,c_8027,c_7301])).

tff(c_8037,plain,(
    m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8027,c_6643])).

tff(c_8396,plain,(
    ! [B_805,C_806,A_807] :
      ( k1_xboole_0 = B_805
      | v1_funct_2(C_806,A_807,B_805)
      | k1_relset_1(A_807,B_805,C_806) != A_807
      | ~ m1_subset_1(C_806,k1_zfmisc_1(k2_zfmisc_1(A_807,B_805))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8402,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_8037,c_8396])).

tff(c_8418,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4')
    | k1_relat_1(k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8031,c_8402])).

tff(c_8419,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_8038,c_8418])).

tff(c_8475,plain,(
    k1_relat_1(k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8419])).

tff(c_8523,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8514,c_8475])).

tff(c_8599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8523])).

tff(c_8600,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8419])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_45] :
      ( v1_funct_2(k1_xboole_0,A_45,k1_xboole_0)
      | k1_xboole_0 = A_45
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_45,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_92,plain,(
    ! [A_45] :
      ( v1_funct_2(k1_xboole_0,A_45,k1_xboole_0)
      | k1_xboole_0 = A_45
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_58])).

tff(c_7204,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_7207,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_7204])).

tff(c_7211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7207])).

tff(c_7213,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_26,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7215,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7213,c_26])).

tff(c_7237,plain,(
    ! [A_730] : ~ r2_hidden(A_730,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7215])).

tff(c_7242,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_7237])).

tff(c_8635,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8600,c_7242])).

tff(c_8653,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8600,c_8600,c_18])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6731,plain,(
    r1_tarski(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6643,c_22])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6800,plain,
    ( k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3') = k2_zfmisc_1('#skF_3','#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6731,c_10])).

tff(c_6853,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6800])).

tff(c_8032,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k7_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8027,c_6853])).

tff(c_8979,plain,(
    ~ r1_tarski('#skF_4',k7_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8653,c_8032])).

tff(c_8984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8635,c_8979])).

tff(c_8985,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8288])).

tff(c_9035,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8985,c_8])).

tff(c_9037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_9035])).

tff(c_9038,plain,(
    k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6800])).

tff(c_10453,plain,(
    k7_relat_1('#skF_6','#skF_3') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10447,c_9038])).

tff(c_10471,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) = k9_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10453,c_40])).

tff(c_10484,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_10136,c_10471])).

tff(c_9082,plain,(
    ! [C_832,B_833,A_834] :
      ( ~ v1_xboole_0(C_832)
      | ~ m1_subset_1(B_833,k1_zfmisc_1(C_832))
      | ~ r2_hidden(A_834,B_833) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_9100,plain,(
    ! [B_838,A_839,A_840] :
      ( ~ v1_xboole_0(B_838)
      | ~ r2_hidden(A_839,A_840)
      | ~ r1_tarski(A_840,B_838) ) ),
    inference(resolution,[status(thm)],[c_24,c_9082])).

tff(c_9127,plain,(
    ! [B_841,A_842,B_843] :
      ( ~ v1_xboole_0(B_841)
      | ~ r1_tarski(A_842,B_841)
      | r1_tarski(A_842,B_843) ) ),
    inference(resolution,[status(thm)],[c_6,c_9100])).

tff(c_9142,plain,(
    ! [B_7,B_843] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_843) ) ),
    inference(resolution,[status(thm)],[c_14,c_9127])).

tff(c_9254,plain,(
    ! [B_855,A_856] :
      ( v5_relat_1(B_855,A_856)
      | ~ r1_tarski(k2_relat_1(B_855),A_856)
      | ~ v1_relat_1(B_855) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_9269,plain,(
    ! [B_855,B_843] :
      ( v5_relat_1(B_855,B_843)
      | ~ v1_relat_1(B_855)
      | ~ v1_xboole_0(k2_relat_1(B_855)) ) ),
    inference(resolution,[status(thm)],[c_9142,c_9254])).

tff(c_10492,plain,(
    ! [B_843] :
      ( v5_relat_1(k2_zfmisc_1('#skF_3','#skF_4'),B_843)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10484,c_9269])).

tff(c_10508,plain,(
    ! [B_843] :
      ( v5_relat_1(k2_zfmisc_1('#skF_3','#skF_4'),B_843)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10492])).

tff(c_10535,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10508])).

tff(c_9045,plain,(
    ~ v1_funct_2(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9038,c_6642])).

tff(c_9044,plain,(
    m1_subset_1(k2_zfmisc_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9038,c_6643])).

tff(c_9595,plain,(
    ! [A_881,B_882,C_883] :
      ( k1_relset_1(A_881,B_882,C_883) = k1_relat_1(C_883)
      | ~ m1_subset_1(C_883,k1_zfmisc_1(k2_zfmisc_1(A_881,B_882))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_9612,plain,(
    k1_relset_1('#skF_3','#skF_4',k2_zfmisc_1('#skF_3','#skF_4')) = k1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9044,c_9595])).

tff(c_10670,plain,(
    ! [B_951,C_952,A_953] :
      ( k1_xboole_0 = B_951
      | v1_funct_2(C_952,A_953,B_951)
      | k1_relset_1(A_953,B_951,C_952) != A_953
      | ~ m1_subset_1(C_952,k1_zfmisc_1(k2_zfmisc_1(A_953,B_951))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10676,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4',k2_zfmisc_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_9044,c_10670])).

tff(c_10692,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_3','#skF_4')
    | k1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9612,c_10676])).

tff(c_10693,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_9045,c_10692])).

tff(c_10749,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10693])).

tff(c_9614,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_9595])).

tff(c_10536,plain,(
    ! [B_948,A_949,C_950] :
      ( k1_xboole_0 = B_948
      | k1_relset_1(A_949,B_948,C_950) = A_949
      | ~ v1_funct_2(C_950,A_949,B_948)
      | ~ m1_subset_1(C_950,k1_zfmisc_1(k2_zfmisc_1(A_949,B_948))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10552,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_10536])).

tff(c_10562,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_9614,c_10552])).

tff(c_10564,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10562])).

tff(c_10575,plain,(
    ! [A_27] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_27)) = A_27
      | ~ r1_tarski(A_27,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10564,c_44])).

tff(c_11042,plain,(
    ! [A_970] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_970)) = A_970
      | ~ r1_tarski(A_970,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_10575])).

tff(c_11110,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10453,c_11042])).

tff(c_11166,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11110])).

tff(c_11168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10749,c_11166])).

tff(c_11169,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10693])).

tff(c_11223,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11169,c_8])).

tff(c_11225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10535,c_11223])).

tff(c_11226,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10562])).

tff(c_11276,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11226,c_8])).

tff(c_11278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_11276])).

tff(c_11280,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_10508])).

tff(c_9175,plain,(
    ! [B_846,B_847] :
      ( ~ v1_xboole_0(B_846)
      | r1_tarski(B_846,B_847) ) ),
    inference(resolution,[status(thm)],[c_14,c_9127])).

tff(c_9224,plain,(
    ! [B_854,B_853] :
      ( B_854 = B_853
      | ~ r1_tarski(B_853,B_854)
      | ~ v1_xboole_0(B_854) ) ),
    inference(resolution,[status(thm)],[c_9175,c_10])).

tff(c_9276,plain,(
    ! [B_859,B_858] :
      ( B_859 = B_858
      | ~ v1_xboole_0(B_858)
      | ~ v1_xboole_0(B_859) ) ),
    inference(resolution,[status(thm)],[c_9142,c_9224])).

tff(c_9279,plain,(
    ! [B_859] :
      ( k1_xboole_0 = B_859
      | ~ v1_xboole_0(B_859) ) ),
    inference(resolution,[status(thm)],[c_8,c_9276])).

tff(c_11303,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11280,c_9279])).

tff(c_11381,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11303,c_11303,c_18])).

tff(c_9118,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_12,k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_9044,c_26])).

tff(c_9221,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9118])).

tff(c_11641,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11381,c_9221])).

tff(c_11651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11280,c_11641])).

tff(c_11659,plain,(
    ! [A_986] : ~ r2_hidden(A_986,k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_9118])).

tff(c_11664,plain,(
    ! [B_2] : r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),B_2) ),
    inference(resolution,[status(thm)],[c_6,c_11659])).

tff(c_11721,plain,(
    ! [B_998,B_997] :
      ( B_998 = B_997
      | ~ r1_tarski(B_997,B_998)
      | ~ v1_xboole_0(B_998) ) ),
    inference(resolution,[status(thm)],[c_9175,c_10])).

tff(c_11756,plain,(
    ! [B_999] :
      ( k2_zfmisc_1('#skF_3','#skF_4') = B_999
      | ~ v1_xboole_0(B_999) ) ),
    inference(resolution,[status(thm)],[c_11664,c_11721])).

tff(c_11765,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_11756])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11811,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_11765,c_16])).

tff(c_11898,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11811])).

tff(c_102,plain,(
    ! [A_59,B_60] : v1_relat_1(k2_zfmisc_1(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_104,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_102])).

tff(c_11918,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_104])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6817,plain,(
    ! [C_673,B_674,A_675] :
      ( v5_relat_1(C_673,B_674)
      | ~ m1_subset_1(C_673,k1_zfmisc_1(k2_zfmisc_1(A_675,B_674))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_9055,plain,(
    ! [A_829,B_830,A_831] :
      ( v5_relat_1(A_829,B_830)
      | ~ r1_tarski(A_829,k2_zfmisc_1(A_831,B_830)) ) ),
    inference(resolution,[status(thm)],[c_24,c_6817])).

tff(c_9090,plain,(
    ! [A_835,B_836] : v5_relat_1(k2_zfmisc_1(A_835,B_836),B_836) ),
    inference(resolution,[status(thm)],[c_14,c_9055])).

tff(c_9093,plain,(
    ! [B_9] : v5_relat_1(k1_xboole_0,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_9090])).

tff(c_11906,plain,(
    ! [B_9] : v5_relat_1('#skF_3',B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_9093])).

tff(c_34,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11820,plain,(
    ! [B_1001] : r1_tarski(k1_xboole_0,B_1001) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11765,c_11664])).

tff(c_11855,plain,(
    ! [B_1001] :
      ( k1_xboole_0 = B_1001
      | ~ r1_tarski(B_1001,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_11820,c_10])).

tff(c_12109,plain,(
    ! [B_1015] :
      ( B_1015 = '#skF_3'
      | ~ r1_tarski(B_1015,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_11898,c_11855])).

tff(c_12395,plain,(
    ! [B_1052] :
      ( k2_relat_1(B_1052) = '#skF_3'
      | ~ v5_relat_1(B_1052,'#skF_3')
      | ~ v1_relat_1(B_1052) ) ),
    inference(resolution,[status(thm)],[c_34,c_12109])).

tff(c_12403,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11906,c_12395])).

tff(c_12415,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11918,c_12403])).

tff(c_12738,plain,(
    ! [A_1064,B_1065,C_1066,D_1067] :
      ( k2_partfun1(A_1064,B_1065,C_1066,D_1067) = k7_relat_1(C_1066,D_1067)
      | ~ m1_subset_1(C_1066,k1_zfmisc_1(k2_zfmisc_1(A_1064,B_1065)))
      | ~ v1_funct_1(C_1066) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_12747,plain,(
    ! [D_1067] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_1067) = k7_relat_1('#skF_6',D_1067)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_12738])).

tff(c_12753,plain,(
    ! [D_1068] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_1068) = k7_relat_1('#skF_6',D_1068) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_12747])).

tff(c_11775,plain,(
    k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11765,c_9038])).

tff(c_12003,plain,(
    k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_11775])).

tff(c_12759,plain,(
    k7_relat_1('#skF_6','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12753,c_12003])).

tff(c_12783,plain,
    ( k9_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12759,c_40])).

tff(c_12800,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_12474,c_12415,c_12783])).

tff(c_6686,plain,(
    ! [C_650,A_651,B_652] :
      ( v4_relat_1(C_650,A_651)
      | ~ m1_subset_1(C_650,k1_zfmisc_1(k2_zfmisc_1(A_651,B_652))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6738,plain,(
    ! [A_662,A_663,B_664] :
      ( v4_relat_1(A_662,A_663)
      | ~ r1_tarski(A_662,k2_zfmisc_1(A_663,B_664)) ) ),
    inference(resolution,[status(thm)],[c_24,c_6686])).

tff(c_6779,plain,(
    ! [A_667,B_668] : v4_relat_1(k2_zfmisc_1(A_667,B_668),A_667) ),
    inference(resolution,[status(thm)],[c_14,c_6738])).

tff(c_6785,plain,(
    ! [A_8] : v4_relat_1(k1_xboole_0,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6779])).

tff(c_11910,plain,(
    ! [A_8] : v4_relat_1('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_6785])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12288,plain,(
    ! [B_1038] :
      ( k1_relat_1(B_1038) = '#skF_3'
      | ~ v4_relat_1(B_1038,'#skF_3')
      | ~ v1_relat_1(B_1038) ) ),
    inference(resolution,[status(thm)],[c_30,c_12109])).

tff(c_12296,plain,
    ( k1_relat_1('#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11910,c_12288])).

tff(c_12308,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11918,c_12296])).

tff(c_12820,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12800,c_12800,c_12308])).

tff(c_11769,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11765,c_11664])).

tff(c_11902,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_11769])).

tff(c_12842,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12800,c_11902])).

tff(c_12180,plain,(
    ! [A_1019,B_1020,C_1021] :
      ( k1_relset_1(A_1019,B_1020,C_1021) = k1_relat_1(C_1021)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1(k2_zfmisc_1(A_1019,B_1020))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_13463,plain,(
    ! [A_1098,B_1099,A_1100] :
      ( k1_relset_1(A_1098,B_1099,A_1100) = k1_relat_1(A_1100)
      | ~ r1_tarski(A_1100,k2_zfmisc_1(A_1098,B_1099)) ) ),
    inference(resolution,[status(thm)],[c_24,c_12180])).

tff(c_13473,plain,(
    ! [A_1098,B_1099] : k1_relset_1(A_1098,B_1099,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12842,c_13463])).

tff(c_13498,plain,(
    ! [A_1098,B_1099] : k1_relset_1(A_1098,B_1099,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12820,c_13473])).

tff(c_11856,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_11860,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_11856])).

tff(c_11864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_11860])).

tff(c_11866,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_11900,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_11898,c_11866])).

tff(c_62,plain,(
    ! [C_47,B_46] :
      ( v1_funct_2(C_47,k1_xboole_0,B_46)
      | k1_relset_1(k1_xboole_0,B_46,C_47) != k1_xboole_0
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_90,plain,(
    ! [C_47,B_46] :
      ( v1_funct_2(C_47,k1_xboole_0,B_46)
      | k1_relset_1(k1_xboole_0,B_46,C_47) != k1_xboole_0
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_12242,plain,(
    ! [C_1028,B_1029] :
      ( v1_funct_2(C_1028,'#skF_3',B_1029)
      | k1_relset_1('#skF_3',B_1029,C_1028) != '#skF_3'
      | ~ m1_subset_1(C_1028,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_11898,c_11898,c_11898,c_90])).

tff(c_12248,plain,(
    ! [B_1029] :
      ( v1_funct_2('#skF_3','#skF_3',B_1029)
      | k1_relset_1('#skF_3',B_1029,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_11900,c_12242])).

tff(c_15218,plain,(
    ! [B_1029] : v1_funct_2('#skF_4','#skF_4',B_1029) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12800,c_13498,c_12800,c_12800,c_12800,c_12800,c_12248])).

tff(c_11773,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11765,c_9045])).

tff(c_11901,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_11773])).

tff(c_12844,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12800,c_12800,c_11901])).

tff(c_15221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15218,c_12844])).

tff(c_15222,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11811])).

tff(c_15223,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11811])).

tff(c_15255,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15222,c_15223])).

tff(c_11865,plain,(
    ! [A_45] :
      ( v1_funct_2(k1_xboole_0,A_45,k1_xboole_0)
      | k1_xboole_0 = A_45 ) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_15261,plain,(
    ! [A_45] :
      ( v1_funct_2('#skF_4',A_45,'#skF_4')
      | A_45 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15222,c_15222,c_15222,c_11865])).

tff(c_15231,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15222,c_11773])).

tff(c_15295,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15261,c_15231])).

tff(c_15299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15255,c_15295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.17/3.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.39/3.20  
% 9.39/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.39/3.20  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.39/3.20  
% 9.39/3.20  %Foreground sorts:
% 9.39/3.20  
% 9.39/3.20  
% 9.39/3.20  %Background operators:
% 9.39/3.20  
% 9.39/3.20  
% 9.39/3.20  %Foreground operators:
% 9.39/3.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.39/3.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.39/3.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.39/3.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.39/3.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.39/3.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.39/3.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.39/3.20  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.39/3.20  tff('#skF_5', type, '#skF_5': $i).
% 9.39/3.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.39/3.20  tff('#skF_6', type, '#skF_6': $i).
% 9.39/3.20  tff('#skF_2', type, '#skF_2': $i).
% 9.39/3.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.39/3.20  tff('#skF_3', type, '#skF_3': $i).
% 9.39/3.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.39/3.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.39/3.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.39/3.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.39/3.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.39/3.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.39/3.20  tff('#skF_4', type, '#skF_4': $i).
% 9.39/3.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.39/3.20  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.39/3.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.39/3.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.39/3.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.39/3.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.39/3.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.39/3.20  
% 9.39/3.24  tff(f_167, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 9.39/3.24  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.39/3.24  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.39/3.24  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.39/3.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.39/3.24  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.39/3.24  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 9.39/3.24  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.39/3.24  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.39/3.24  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.39/3.24  tff(f_146, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.39/3.24  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.39/3.24  tff(f_72, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.39/3.24  tff(f_114, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 9.39/3.24  tff(f_140, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.39/3.24  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.39/3.24  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.39/3.24  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 9.39/3.24  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.39/3.24  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.39/3.24  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.39/3.24  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.39/3.24  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.39/3.24  tff(c_1433, plain, (![C_210, A_211, B_212]: (v1_relat_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.39/3.24  tff(c_1446, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_1433])).
% 9.39/3.24  tff(c_12456, plain, (![A_1054, B_1055, C_1056, D_1057]: (k7_relset_1(A_1054, B_1055, C_1056, D_1057)=k9_relat_1(C_1056, D_1057) | ~m1_subset_1(C_1056, k1_zfmisc_1(k2_zfmisc_1(A_1054, B_1055))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.39/3.24  tff(c_12468, plain, (![D_1058]: (k7_relset_1('#skF_2', '#skF_5', '#skF_6', D_1058)=k9_relat_1('#skF_6', D_1058))), inference(resolution, [status(thm)], [c_82, c_12456])).
% 9.39/3.24  tff(c_88, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.39/3.24  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.39/3.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.39/3.24  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.39/3.24  tff(c_3470, plain, (![C_404, B_405, A_406]: (~v1_xboole_0(C_404) | ~m1_subset_1(B_405, k1_zfmisc_1(C_404)) | ~r2_hidden(A_406, B_405))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.39/3.24  tff(c_3483, plain, (![B_407, A_408, A_409]: (~v1_xboole_0(B_407) | ~r2_hidden(A_408, A_409) | ~r1_tarski(A_409, B_407))), inference(resolution, [status(thm)], [c_24, c_3470])).
% 9.39/3.24  tff(c_3487, plain, (![B_410, A_411, B_412]: (~v1_xboole_0(B_410) | ~r1_tarski(A_411, B_410) | r1_tarski(A_411, B_412))), inference(resolution, [status(thm)], [c_6, c_3483])).
% 9.39/3.24  tff(c_3544, plain, (![B_415, B_416]: (~v1_xboole_0(B_415) | r1_tarski(B_415, B_416))), inference(resolution, [status(thm)], [c_14, c_3487])).
% 9.39/3.24  tff(c_78, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.39/3.24  tff(c_145, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.39/3.24  tff(c_154, plain, (k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_145])).
% 9.39/3.24  tff(c_1453, plain, (~r1_tarski('#skF_4', k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_154])).
% 9.39/3.24  tff(c_3588, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_3544, c_1453])).
% 9.39/3.24  tff(c_80, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.39/3.24  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.39/3.24  tff(c_3898, plain, (![A_439, B_440, C_441]: (k1_relset_1(A_439, B_440, C_441)=k1_relat_1(C_441) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.39/3.24  tff(c_3917, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_3898])).
% 9.39/3.24  tff(c_4671, plain, (![B_497, A_498, C_499]: (k1_xboole_0=B_497 | k1_relset_1(A_498, B_497, C_499)=A_498 | ~v1_funct_2(C_499, A_498, B_497) | ~m1_subset_1(C_499, k1_zfmisc_1(k2_zfmisc_1(A_498, B_497))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.39/3.24  tff(c_4684, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_4671])).
% 9.39/3.24  tff(c_4692, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3917, c_4684])).
% 9.39/3.24  tff(c_4694, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_4692])).
% 9.39/3.24  tff(c_44, plain, (![B_28, A_27]: (k1_relat_1(k7_relat_1(B_28, A_27))=A_27 | ~r1_tarski(A_27, k1_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.39/3.24  tff(c_4704, plain, (![A_27]: (k1_relat_1(k7_relat_1('#skF_6', A_27))=A_27 | ~r1_tarski(A_27, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4694, c_44])).
% 9.39/3.24  tff(c_4724, plain, (![A_27]: (k1_relat_1(k7_relat_1('#skF_6', A_27))=A_27 | ~r1_tarski(A_27, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_4704])).
% 9.39/3.24  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.39/3.24  tff(c_4628, plain, (![A_491, B_492, C_493, D_494]: (k2_partfun1(A_491, B_492, C_493, D_494)=k7_relat_1(C_493, D_494) | ~m1_subset_1(C_493, k1_zfmisc_1(k2_zfmisc_1(A_491, B_492))) | ~v1_funct_1(C_493))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.39/3.24  tff(c_4639, plain, (![D_494]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_494)=k7_relat_1('#skF_6', D_494) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_4628])).
% 9.39/3.24  tff(c_4649, plain, (![D_494]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_494)=k7_relat_1('#skF_6', D_494))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4639])).
% 9.39/3.24  tff(c_2050, plain, (![A_299, B_300, C_301]: (k1_relset_1(A_299, B_300, C_301)=k1_relat_1(C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.39/3.24  tff(c_2065, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_2050])).
% 9.39/3.24  tff(c_2875, plain, (![B_359, A_360, C_361]: (k1_xboole_0=B_359 | k1_relset_1(A_360, B_359, C_361)=A_360 | ~v1_funct_2(C_361, A_360, B_359) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_360, B_359))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.39/3.24  tff(c_2888, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_2875])).
% 9.39/3.24  tff(c_2896, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2065, c_2888])).
% 9.39/3.24  tff(c_2898, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_2896])).
% 9.39/3.24  tff(c_2906, plain, (![A_27]: (k1_relat_1(k7_relat_1('#skF_6', A_27))=A_27 | ~r1_tarski(A_27, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2898, c_44])).
% 9.39/3.24  tff(c_2926, plain, (![A_27]: (k1_relat_1(k7_relat_1('#skF_6', A_27))=A_27 | ~r1_tarski(A_27, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_2906])).
% 9.39/3.24  tff(c_2221, plain, (![A_308, B_309, C_310, D_311]: (k7_relset_1(A_308, B_309, C_310, D_311)=k9_relat_1(C_310, D_311) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_308, B_309))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.39/3.24  tff(c_2232, plain, (![D_311]: (k7_relset_1('#skF_2', '#skF_5', '#skF_6', D_311)=k9_relat_1('#skF_6', D_311))), inference(resolution, [status(thm)], [c_82, c_2221])).
% 9.39/3.24  tff(c_2241, plain, (r1_tarski(k9_relat_1('#skF_6', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2232, c_78])).
% 9.39/3.24  tff(c_40, plain, (![B_24, A_23]: (k2_relat_1(k7_relat_1(B_24, A_23))=k9_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.39/3.24  tff(c_36, plain, (![A_19, B_20]: (v1_relat_1(k7_relat_1(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.39/3.24  tff(c_2727, plain, (![C_345, A_346, B_347]: (m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(A_346, B_347))) | ~r1_tarski(k2_relat_1(C_345), B_347) | ~r1_tarski(k1_relat_1(C_345), A_346) | ~v1_relat_1(C_345))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.39/3.24  tff(c_2691, plain, (![A_339, B_340, C_341, D_342]: (k2_partfun1(A_339, B_340, C_341, D_342)=k7_relat_1(C_341, D_342) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))) | ~v1_funct_1(C_341))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.39/3.24  tff(c_2698, plain, (![D_342]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_342)=k7_relat_1('#skF_6', D_342) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_2691])).
% 9.39/3.24  tff(c_2704, plain, (![D_342]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_342)=k7_relat_1('#skF_6', D_342))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2698])).
% 9.39/3.24  tff(c_1402, plain, (![A_200, B_201, C_202, D_203]: (v1_funct_1(k2_partfun1(A_200, B_201, C_202, D_203)) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_1(C_202))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.39/3.24  tff(c_1409, plain, (![D_203]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_203)) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_1402])).
% 9.39/3.24  tff(c_1415, plain, (![D_203]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_203)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1409])).
% 9.39/3.24  tff(c_76, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.39/3.24  tff(c_162, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_76])).
% 9.39/3.24  tff(c_1418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1415, c_162])).
% 9.39/3.24  tff(c_1419, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_76])).
% 9.39/3.24  tff(c_1506, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1419])).
% 9.39/3.24  tff(c_2708, plain, (~m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2704, c_1506])).
% 9.39/3.24  tff(c_2760, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_2727, c_2708])).
% 9.39/3.24  tff(c_2809, plain, (~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2760])).
% 9.39/3.24  tff(c_2812, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_2809])).
% 9.39/3.24  tff(c_2816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1446, c_2812])).
% 9.39/3.24  tff(c_2817, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_2760])).
% 9.39/3.24  tff(c_3164, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_2817])).
% 9.39/3.24  tff(c_3170, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_3164])).
% 9.39/3.24  tff(c_3179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1446, c_2241, c_3170])).
% 9.39/3.24  tff(c_3180, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_2817])).
% 9.39/3.24  tff(c_3205, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2926, c_3180])).
% 9.39/3.24  tff(c_3220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_14, c_3205])).
% 9.39/3.24  tff(c_3221, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2896])).
% 9.39/3.24  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.39/3.24  tff(c_3270, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3221, c_8])).
% 9.39/3.24  tff(c_3272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3270])).
% 9.39/3.24  tff(c_3274, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1419])).
% 9.39/3.24  tff(c_3915, plain, (k1_relset_1('#skF_3', '#skF_4', k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_3274, c_3898])).
% 9.39/3.24  tff(c_4653, plain, (k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4649, c_4649, c_3915])).
% 9.39/3.24  tff(c_3273, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1419])).
% 9.39/3.24  tff(c_4660, plain, (~v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4649, c_3273])).
% 9.39/3.24  tff(c_4659, plain, (m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4649, c_3274])).
% 9.39/3.24  tff(c_64, plain, (![B_46, C_47, A_45]: (k1_xboole_0=B_46 | v1_funct_2(C_47, A_45, B_46) | k1_relset_1(A_45, B_46, C_47)!=A_45 | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.39/3.24  tff(c_4859, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_4659, c_64])).
% 9.39/3.24  tff(c_4888, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4660, c_4859])).
% 9.39/3.24  tff(c_5040, plain, (k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_4888])).
% 9.39/3.24  tff(c_5180, plain, (k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4653, c_5040])).
% 9.39/3.24  tff(c_5187, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4724, c_5180])).
% 9.39/3.24  tff(c_5194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_5187])).
% 9.39/3.24  tff(c_5195, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4888])).
% 9.39/3.24  tff(c_5247, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5195, c_8])).
% 9.39/3.24  tff(c_5249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3588, c_5247])).
% 9.39/3.24  tff(c_5250, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_4692])).
% 9.39/3.24  tff(c_5298, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_8])).
% 9.39/3.24  tff(c_5300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_5298])).
% 9.39/3.24  tff(c_5301, plain, (k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_154])).
% 9.39/3.24  tff(c_12474, plain, (k9_relat_1('#skF_6', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_12468, c_5301])).
% 9.39/3.24  tff(c_38, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.39/3.24  tff(c_10115, plain, (![A_912, B_913, C_914, D_915]: (k7_relset_1(A_912, B_913, C_914, D_915)=k9_relat_1(C_914, D_915) | ~m1_subset_1(C_914, k1_zfmisc_1(k2_zfmisc_1(A_912, B_913))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.39/3.24  tff(c_10130, plain, (![D_916]: (k7_relset_1('#skF_2', '#skF_5', '#skF_6', D_916)=k9_relat_1('#skF_6', D_916))), inference(resolution, [status(thm)], [c_82, c_10115])).
% 9.39/3.24  tff(c_10136, plain, (k9_relat_1('#skF_6', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10130, c_5301])).
% 9.39/3.24  tff(c_10400, plain, (![A_941, B_942, C_943, D_944]: (k2_partfun1(A_941, B_942, C_943, D_944)=k7_relat_1(C_943, D_944) | ~m1_subset_1(C_943, k1_zfmisc_1(k2_zfmisc_1(A_941, B_942))) | ~v1_funct_1(C_943))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.39/3.24  tff(c_10411, plain, (![D_944]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_944)=k7_relat_1('#skF_6', D_944) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_10400])).
% 9.39/3.24  tff(c_10447, plain, (![D_946]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_946)=k7_relat_1('#skF_6', D_946))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_10411])).
% 9.39/3.24  tff(c_7284, plain, (![A_732, B_733, C_734]: (k1_relset_1(A_732, B_733, C_734)=k1_relat_1(C_734) | ~m1_subset_1(C_734, k1_zfmisc_1(k2_zfmisc_1(A_732, B_733))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.39/3.24  tff(c_7303, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_7284])).
% 9.39/3.24  tff(c_8262, plain, (![B_801, A_802, C_803]: (k1_xboole_0=B_801 | k1_relset_1(A_802, B_801, C_803)=A_802 | ~v1_funct_2(C_803, A_802, B_801) | ~m1_subset_1(C_803, k1_zfmisc_1(k2_zfmisc_1(A_802, B_801))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.39/3.24  tff(c_8278, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_8262])).
% 9.39/3.24  tff(c_8288, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7303, c_8278])).
% 9.39/3.24  tff(c_8290, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_8288])).
% 9.39/3.24  tff(c_8298, plain, (![A_27]: (k1_relat_1(k7_relat_1('#skF_6', A_27))=A_27 | ~r1_tarski(A_27, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8290, c_44])).
% 9.39/3.24  tff(c_8514, plain, (![A_811]: (k1_relat_1(k7_relat_1('#skF_6', A_811))=A_811 | ~r1_tarski(A_811, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_8298])).
% 9.39/3.24  tff(c_8009, plain, (![A_780, B_781, C_782, D_783]: (k2_partfun1(A_780, B_781, C_782, D_783)=k7_relat_1(C_782, D_783) | ~m1_subset_1(C_782, k1_zfmisc_1(k2_zfmisc_1(A_780, B_781))) | ~v1_funct_1(C_782))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.39/3.24  tff(c_8018, plain, (![D_783]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_783)=k7_relat_1('#skF_6', D_783) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_8009])).
% 9.39/3.24  tff(c_8027, plain, (![D_783]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_783)=k7_relat_1('#skF_6', D_783))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8018])).
% 9.39/3.24  tff(c_42, plain, (![B_26, A_25]: (r1_tarski(k1_relat_1(k7_relat_1(B_26, A_25)), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.39/3.24  tff(c_6056, plain, (![A_617, B_618, C_619, D_620]: (k7_relset_1(A_617, B_618, C_619, D_620)=k9_relat_1(C_619, D_620) | ~m1_subset_1(C_619, k1_zfmisc_1(k2_zfmisc_1(A_617, B_618))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.39/3.24  tff(c_6075, plain, (![D_622]: (k7_relset_1('#skF_2', '#skF_5', '#skF_6', D_622)=k9_relat_1('#skF_6', D_622))), inference(resolution, [status(thm)], [c_82, c_6056])).
% 9.39/3.24  tff(c_6081, plain, (k9_relat_1('#skF_6', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6075, c_5301])).
% 9.39/3.24  tff(c_6265, plain, (![C_633, A_634, B_635]: (m1_subset_1(C_633, k1_zfmisc_1(k2_zfmisc_1(A_634, B_635))) | ~r1_tarski(k2_relat_1(C_633), B_635) | ~r1_tarski(k1_relat_1(C_633), A_634) | ~v1_relat_1(C_633))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.39/3.24  tff(c_6130, plain, (![A_624, B_625, C_626, D_627]: (k2_partfun1(A_624, B_625, C_626, D_627)=k7_relat_1(C_626, D_627) | ~m1_subset_1(C_626, k1_zfmisc_1(k2_zfmisc_1(A_624, B_625))) | ~v1_funct_1(C_626))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.39/3.24  tff(c_6137, plain, (![D_627]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_627)=k7_relat_1('#skF_6', D_627) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_6130])).
% 9.39/3.24  tff(c_6143, plain, (![D_627]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_627)=k7_relat_1('#skF_6', D_627))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6137])).
% 9.39/3.24  tff(c_5303, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1419])).
% 9.39/3.24  tff(c_6147, plain, (~m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6143, c_5303])).
% 9.39/3.24  tff(c_6298, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_6265, c_6147])).
% 9.39/3.24  tff(c_6443, plain, (~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6298])).
% 9.39/3.24  tff(c_6446, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_6443])).
% 9.39/3.24  tff(c_6450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1446, c_6446])).
% 9.39/3.24  tff(c_6451, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_6298])).
% 9.39/3.24  tff(c_6581, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_6451])).
% 9.39/3.24  tff(c_6587, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_6581])).
% 9.39/3.24  tff(c_6596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1446, c_14, c_6081, c_6587])).
% 9.39/3.24  tff(c_6597, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_6451])).
% 9.39/3.24  tff(c_6631, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_6597])).
% 9.39/3.24  tff(c_6641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1446, c_6631])).
% 9.39/3.24  tff(c_6642, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1419])).
% 9.39/3.24  tff(c_8038, plain, (~v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8027, c_6642])).
% 9.39/3.24  tff(c_6643, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1419])).
% 9.39/3.24  tff(c_7301, plain, (k1_relset_1('#skF_3', '#skF_4', k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_6643, c_7284])).
% 9.39/3.24  tff(c_8031, plain, (k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8027, c_8027, c_7301])).
% 9.39/3.24  tff(c_8037, plain, (m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8027, c_6643])).
% 9.39/3.24  tff(c_8396, plain, (![B_805, C_806, A_807]: (k1_xboole_0=B_805 | v1_funct_2(C_806, A_807, B_805) | k1_relset_1(A_807, B_805, C_806)!=A_807 | ~m1_subset_1(C_806, k1_zfmisc_1(k2_zfmisc_1(A_807, B_805))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.39/3.24  tff(c_8402, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_8037, c_8396])).
% 9.39/3.24  tff(c_8418, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8031, c_8402])).
% 9.39/3.24  tff(c_8419, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_8038, c_8418])).
% 9.39/3.24  tff(c_8475, plain, (k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_8419])).
% 9.39/3.24  tff(c_8523, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8514, c_8475])).
% 9.39/3.24  tff(c_8599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_8523])).
% 9.39/3.24  tff(c_8600, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8419])).
% 9.39/3.24  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.39/3.24  tff(c_58, plain, (![A_45]: (v1_funct_2(k1_xboole_0, A_45, k1_xboole_0) | k1_xboole_0=A_45 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_45, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.39/3.24  tff(c_92, plain, (![A_45]: (v1_funct_2(k1_xboole_0, A_45, k1_xboole_0) | k1_xboole_0=A_45 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_58])).
% 9.39/3.24  tff(c_7204, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_92])).
% 9.39/3.24  tff(c_7207, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_7204])).
% 9.39/3.24  tff(c_7211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_7207])).
% 9.39/3.24  tff(c_7213, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_92])).
% 9.39/3.24  tff(c_26, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.39/3.24  tff(c_7215, plain, (![A_12]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_7213, c_26])).
% 9.39/3.24  tff(c_7237, plain, (![A_730]: (~r2_hidden(A_730, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_7215])).
% 9.39/3.24  tff(c_7242, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_7237])).
% 9.39/3.24  tff(c_8635, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_8600, c_7242])).
% 9.39/3.24  tff(c_8653, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8600, c_8600, c_18])).
% 9.39/3.24  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.39/3.24  tff(c_6731, plain, (r1_tarski(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6643, c_22])).
% 9.39/3.24  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.39/3.24  tff(c_6800, plain, (k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')=k2_zfmisc_1('#skF_3', '#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_6731, c_10])).
% 9.39/3.24  tff(c_6853, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6800])).
% 9.39/3.24  tff(c_8032, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k7_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8027, c_6853])).
% 9.39/3.24  tff(c_8979, plain, (~r1_tarski('#skF_4', k7_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8653, c_8032])).
% 9.39/3.24  tff(c_8984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8635, c_8979])).
% 9.39/3.24  tff(c_8985, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_8288])).
% 9.39/3.24  tff(c_9035, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8985, c_8])).
% 9.39/3.24  tff(c_9037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_9035])).
% 9.39/3.24  tff(c_9038, plain, (k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_6800])).
% 9.39/3.24  tff(c_10453, plain, (k7_relat_1('#skF_6', '#skF_3')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10447, c_9038])).
% 9.39/3.24  tff(c_10471, plain, (k2_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))=k9_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10453, c_40])).
% 9.39/3.24  tff(c_10484, plain, (k2_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_10136, c_10471])).
% 9.39/3.24  tff(c_9082, plain, (![C_832, B_833, A_834]: (~v1_xboole_0(C_832) | ~m1_subset_1(B_833, k1_zfmisc_1(C_832)) | ~r2_hidden(A_834, B_833))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.39/3.24  tff(c_9100, plain, (![B_838, A_839, A_840]: (~v1_xboole_0(B_838) | ~r2_hidden(A_839, A_840) | ~r1_tarski(A_840, B_838))), inference(resolution, [status(thm)], [c_24, c_9082])).
% 9.39/3.24  tff(c_9127, plain, (![B_841, A_842, B_843]: (~v1_xboole_0(B_841) | ~r1_tarski(A_842, B_841) | r1_tarski(A_842, B_843))), inference(resolution, [status(thm)], [c_6, c_9100])).
% 9.39/3.24  tff(c_9142, plain, (![B_7, B_843]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_843))), inference(resolution, [status(thm)], [c_14, c_9127])).
% 9.39/3.24  tff(c_9254, plain, (![B_855, A_856]: (v5_relat_1(B_855, A_856) | ~r1_tarski(k2_relat_1(B_855), A_856) | ~v1_relat_1(B_855))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.39/3.24  tff(c_9269, plain, (![B_855, B_843]: (v5_relat_1(B_855, B_843) | ~v1_relat_1(B_855) | ~v1_xboole_0(k2_relat_1(B_855)))), inference(resolution, [status(thm)], [c_9142, c_9254])).
% 9.39/3.24  tff(c_10492, plain, (![B_843]: (v5_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'), B_843) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10484, c_9269])).
% 9.39/3.24  tff(c_10508, plain, (![B_843]: (v5_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'), B_843) | ~v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10492])).
% 9.39/3.24  tff(c_10535, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_10508])).
% 9.39/3.24  tff(c_9045, plain, (~v1_funct_2(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9038, c_6642])).
% 9.39/3.24  tff(c_9044, plain, (m1_subset_1(k2_zfmisc_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9038, c_6643])).
% 9.39/3.24  tff(c_9595, plain, (![A_881, B_882, C_883]: (k1_relset_1(A_881, B_882, C_883)=k1_relat_1(C_883) | ~m1_subset_1(C_883, k1_zfmisc_1(k2_zfmisc_1(A_881, B_882))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.39/3.24  tff(c_9612, plain, (k1_relset_1('#skF_3', '#skF_4', k2_zfmisc_1('#skF_3', '#skF_4'))=k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_9044, c_9595])).
% 9.39/3.24  tff(c_10670, plain, (![B_951, C_952, A_953]: (k1_xboole_0=B_951 | v1_funct_2(C_952, A_953, B_951) | k1_relset_1(A_953, B_951, C_952)!=A_953 | ~m1_subset_1(C_952, k1_zfmisc_1(k2_zfmisc_1(A_953, B_951))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.39/3.24  tff(c_10676, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', k2_zfmisc_1('#skF_3', '#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_9044, c_10670])).
% 9.39/3.24  tff(c_10692, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_3', '#skF_4') | k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9612, c_10676])).
% 9.39/3.24  tff(c_10693, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_9045, c_10692])).
% 9.39/3.24  tff(c_10749, plain, (k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_10693])).
% 9.39/3.24  tff(c_9614, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_9595])).
% 9.39/3.24  tff(c_10536, plain, (![B_948, A_949, C_950]: (k1_xboole_0=B_948 | k1_relset_1(A_949, B_948, C_950)=A_949 | ~v1_funct_2(C_950, A_949, B_948) | ~m1_subset_1(C_950, k1_zfmisc_1(k2_zfmisc_1(A_949, B_948))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.39/3.24  tff(c_10552, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_10536])).
% 9.39/3.24  tff(c_10562, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_9614, c_10552])).
% 9.39/3.24  tff(c_10564, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_10562])).
% 9.39/3.24  tff(c_10575, plain, (![A_27]: (k1_relat_1(k7_relat_1('#skF_6', A_27))=A_27 | ~r1_tarski(A_27, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10564, c_44])).
% 9.39/3.24  tff(c_11042, plain, (![A_970]: (k1_relat_1(k7_relat_1('#skF_6', A_970))=A_970 | ~r1_tarski(A_970, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_10575])).
% 9.39/3.24  tff(c_11110, plain, (k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10453, c_11042])).
% 9.39/3.24  tff(c_11166, plain, (k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11110])).
% 9.39/3.24  tff(c_11168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10749, c_11166])).
% 9.39/3.24  tff(c_11169, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_10693])).
% 9.39/3.24  tff(c_11223, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11169, c_8])).
% 9.39/3.24  tff(c_11225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10535, c_11223])).
% 9.39/3.24  tff(c_11226, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_10562])).
% 9.39/3.24  tff(c_11276, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11226, c_8])).
% 9.39/3.24  tff(c_11278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_11276])).
% 9.39/3.24  tff(c_11280, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_10508])).
% 9.39/3.24  tff(c_9175, plain, (![B_846, B_847]: (~v1_xboole_0(B_846) | r1_tarski(B_846, B_847))), inference(resolution, [status(thm)], [c_14, c_9127])).
% 9.39/3.24  tff(c_9224, plain, (![B_854, B_853]: (B_854=B_853 | ~r1_tarski(B_853, B_854) | ~v1_xboole_0(B_854))), inference(resolution, [status(thm)], [c_9175, c_10])).
% 9.39/3.24  tff(c_9276, plain, (![B_859, B_858]: (B_859=B_858 | ~v1_xboole_0(B_858) | ~v1_xboole_0(B_859))), inference(resolution, [status(thm)], [c_9142, c_9224])).
% 9.39/3.24  tff(c_9279, plain, (![B_859]: (k1_xboole_0=B_859 | ~v1_xboole_0(B_859))), inference(resolution, [status(thm)], [c_8, c_9276])).
% 9.39/3.24  tff(c_11303, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_11280, c_9279])).
% 9.39/3.24  tff(c_11381, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11303, c_11303, c_18])).
% 9.39/3.24  tff(c_9118, plain, (![A_12]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_12, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_9044, c_26])).
% 9.39/3.24  tff(c_9221, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_9118])).
% 9.39/3.24  tff(c_11641, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11381, c_9221])).
% 9.39/3.24  tff(c_11651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11280, c_11641])).
% 9.39/3.24  tff(c_11659, plain, (![A_986]: (~r2_hidden(A_986, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_9118])).
% 9.39/3.24  tff(c_11664, plain, (![B_2]: (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), B_2))), inference(resolution, [status(thm)], [c_6, c_11659])).
% 9.39/3.24  tff(c_11721, plain, (![B_998, B_997]: (B_998=B_997 | ~r1_tarski(B_997, B_998) | ~v1_xboole_0(B_998))), inference(resolution, [status(thm)], [c_9175, c_10])).
% 9.39/3.24  tff(c_11756, plain, (![B_999]: (k2_zfmisc_1('#skF_3', '#skF_4')=B_999 | ~v1_xboole_0(B_999))), inference(resolution, [status(thm)], [c_11664, c_11721])).
% 9.39/3.24  tff(c_11765, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_11756])).
% 9.39/3.24  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.39/3.24  tff(c_11811, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_11765, c_16])).
% 9.39/3.24  tff(c_11898, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_11811])).
% 9.39/3.24  tff(c_102, plain, (![A_59, B_60]: (v1_relat_1(k2_zfmisc_1(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.39/3.24  tff(c_104, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_102])).
% 9.39/3.24  tff(c_11918, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_104])).
% 9.39/3.24  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.39/3.24  tff(c_6817, plain, (![C_673, B_674, A_675]: (v5_relat_1(C_673, B_674) | ~m1_subset_1(C_673, k1_zfmisc_1(k2_zfmisc_1(A_675, B_674))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.39/3.24  tff(c_9055, plain, (![A_829, B_830, A_831]: (v5_relat_1(A_829, B_830) | ~r1_tarski(A_829, k2_zfmisc_1(A_831, B_830)))), inference(resolution, [status(thm)], [c_24, c_6817])).
% 9.39/3.24  tff(c_9090, plain, (![A_835, B_836]: (v5_relat_1(k2_zfmisc_1(A_835, B_836), B_836))), inference(resolution, [status(thm)], [c_14, c_9055])).
% 9.39/3.24  tff(c_9093, plain, (![B_9]: (v5_relat_1(k1_xboole_0, B_9))), inference(superposition, [status(thm), theory('equality')], [c_20, c_9090])).
% 9.39/3.24  tff(c_11906, plain, (![B_9]: (v5_relat_1('#skF_3', B_9))), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_9093])).
% 9.39/3.24  tff(c_34, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.39/3.24  tff(c_11820, plain, (![B_1001]: (r1_tarski(k1_xboole_0, B_1001))), inference(demodulation, [status(thm), theory('equality')], [c_11765, c_11664])).
% 9.39/3.24  tff(c_11855, plain, (![B_1001]: (k1_xboole_0=B_1001 | ~r1_tarski(B_1001, k1_xboole_0))), inference(resolution, [status(thm)], [c_11820, c_10])).
% 9.39/3.24  tff(c_12109, plain, (![B_1015]: (B_1015='#skF_3' | ~r1_tarski(B_1015, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_11898, c_11855])).
% 9.39/3.24  tff(c_12395, plain, (![B_1052]: (k2_relat_1(B_1052)='#skF_3' | ~v5_relat_1(B_1052, '#skF_3') | ~v1_relat_1(B_1052))), inference(resolution, [status(thm)], [c_34, c_12109])).
% 9.39/3.24  tff(c_12403, plain, (k2_relat_1('#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11906, c_12395])).
% 9.39/3.24  tff(c_12415, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11918, c_12403])).
% 9.39/3.24  tff(c_12738, plain, (![A_1064, B_1065, C_1066, D_1067]: (k2_partfun1(A_1064, B_1065, C_1066, D_1067)=k7_relat_1(C_1066, D_1067) | ~m1_subset_1(C_1066, k1_zfmisc_1(k2_zfmisc_1(A_1064, B_1065))) | ~v1_funct_1(C_1066))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.39/3.24  tff(c_12747, plain, (![D_1067]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_1067)=k7_relat_1('#skF_6', D_1067) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_12738])).
% 9.39/3.24  tff(c_12753, plain, (![D_1068]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_1068)=k7_relat_1('#skF_6', D_1068))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_12747])).
% 9.39/3.24  tff(c_11775, plain, (k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11765, c_9038])).
% 9.39/3.24  tff(c_12003, plain, (k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_11775])).
% 9.39/3.24  tff(c_12759, plain, (k7_relat_1('#skF_6', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12753, c_12003])).
% 9.39/3.24  tff(c_12783, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12759, c_40])).
% 9.39/3.24  tff(c_12800, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_12474, c_12415, c_12783])).
% 9.39/3.24  tff(c_6686, plain, (![C_650, A_651, B_652]: (v4_relat_1(C_650, A_651) | ~m1_subset_1(C_650, k1_zfmisc_1(k2_zfmisc_1(A_651, B_652))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.39/3.24  tff(c_6738, plain, (![A_662, A_663, B_664]: (v4_relat_1(A_662, A_663) | ~r1_tarski(A_662, k2_zfmisc_1(A_663, B_664)))), inference(resolution, [status(thm)], [c_24, c_6686])).
% 9.39/3.24  tff(c_6779, plain, (![A_667, B_668]: (v4_relat_1(k2_zfmisc_1(A_667, B_668), A_667))), inference(resolution, [status(thm)], [c_14, c_6738])).
% 9.39/3.24  tff(c_6785, plain, (![A_8]: (v4_relat_1(k1_xboole_0, A_8))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6779])).
% 9.39/3.24  tff(c_11910, plain, (![A_8]: (v4_relat_1('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_6785])).
% 9.39/3.24  tff(c_30, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.39/3.24  tff(c_12288, plain, (![B_1038]: (k1_relat_1(B_1038)='#skF_3' | ~v4_relat_1(B_1038, '#skF_3') | ~v1_relat_1(B_1038))), inference(resolution, [status(thm)], [c_30, c_12109])).
% 9.39/3.24  tff(c_12296, plain, (k1_relat_1('#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11910, c_12288])).
% 9.39/3.24  tff(c_12308, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11918, c_12296])).
% 9.39/3.24  tff(c_12820, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12800, c_12800, c_12308])).
% 9.39/3.24  tff(c_11769, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_11765, c_11664])).
% 9.39/3.24  tff(c_11902, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_11769])).
% 9.39/3.24  tff(c_12842, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_12800, c_11902])).
% 9.39/3.24  tff(c_12180, plain, (![A_1019, B_1020, C_1021]: (k1_relset_1(A_1019, B_1020, C_1021)=k1_relat_1(C_1021) | ~m1_subset_1(C_1021, k1_zfmisc_1(k2_zfmisc_1(A_1019, B_1020))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.39/3.24  tff(c_13463, plain, (![A_1098, B_1099, A_1100]: (k1_relset_1(A_1098, B_1099, A_1100)=k1_relat_1(A_1100) | ~r1_tarski(A_1100, k2_zfmisc_1(A_1098, B_1099)))), inference(resolution, [status(thm)], [c_24, c_12180])).
% 9.39/3.24  tff(c_13473, plain, (![A_1098, B_1099]: (k1_relset_1(A_1098, B_1099, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12842, c_13463])).
% 9.39/3.24  tff(c_13498, plain, (![A_1098, B_1099]: (k1_relset_1(A_1098, B_1099, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12820, c_13473])).
% 9.39/3.24  tff(c_11856, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_92])).
% 9.39/3.24  tff(c_11860, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_11856])).
% 9.39/3.24  tff(c_11864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_11860])).
% 9.39/3.24  tff(c_11866, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_92])).
% 9.39/3.24  tff(c_11900, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_11898, c_11866])).
% 9.39/3.24  tff(c_62, plain, (![C_47, B_46]: (v1_funct_2(C_47, k1_xboole_0, B_46) | k1_relset_1(k1_xboole_0, B_46, C_47)!=k1_xboole_0 | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_46))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.39/3.24  tff(c_90, plain, (![C_47, B_46]: (v1_funct_2(C_47, k1_xboole_0, B_46) | k1_relset_1(k1_xboole_0, B_46, C_47)!=k1_xboole_0 | ~m1_subset_1(C_47, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_62])).
% 9.39/3.24  tff(c_12242, plain, (![C_1028, B_1029]: (v1_funct_2(C_1028, '#skF_3', B_1029) | k1_relset_1('#skF_3', B_1029, C_1028)!='#skF_3' | ~m1_subset_1(C_1028, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_11898, c_11898, c_11898, c_90])).
% 9.39/3.24  tff(c_12248, plain, (![B_1029]: (v1_funct_2('#skF_3', '#skF_3', B_1029) | k1_relset_1('#skF_3', B_1029, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_11900, c_12242])).
% 9.39/3.24  tff(c_15218, plain, (![B_1029]: (v1_funct_2('#skF_4', '#skF_4', B_1029))), inference(demodulation, [status(thm), theory('equality')], [c_12800, c_13498, c_12800, c_12800, c_12800, c_12800, c_12248])).
% 9.39/3.24  tff(c_11773, plain, (~v1_funct_2(k1_xboole_0, '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11765, c_9045])).
% 9.39/3.24  tff(c_11901, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_11773])).
% 9.39/3.24  tff(c_12844, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12800, c_12800, c_11901])).
% 9.39/3.24  tff(c_15221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15218, c_12844])).
% 9.39/3.24  tff(c_15222, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_11811])).
% 9.39/3.24  tff(c_15223, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_11811])).
% 9.39/3.24  tff(c_15255, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15222, c_15223])).
% 9.39/3.24  tff(c_11865, plain, (![A_45]: (v1_funct_2(k1_xboole_0, A_45, k1_xboole_0) | k1_xboole_0=A_45)), inference(splitRight, [status(thm)], [c_92])).
% 9.39/3.24  tff(c_15261, plain, (![A_45]: (v1_funct_2('#skF_4', A_45, '#skF_4') | A_45='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15222, c_15222, c_15222, c_11865])).
% 9.39/3.24  tff(c_15231, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15222, c_11773])).
% 9.39/3.24  tff(c_15295, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_15261, c_15231])).
% 9.39/3.24  tff(c_15299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15255, c_15295])).
% 9.39/3.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.39/3.24  
% 9.39/3.24  Inference rules
% 9.39/3.24  ----------------------
% 9.39/3.24  #Ref     : 0
% 9.39/3.24  #Sup     : 3246
% 9.39/3.24  #Fact    : 0
% 9.39/3.24  #Define  : 0
% 9.39/3.24  #Split   : 68
% 9.39/3.24  #Chain   : 0
% 9.39/3.24  #Close   : 0
% 9.39/3.24  
% 9.39/3.24  Ordering : KBO
% 9.39/3.24  
% 9.39/3.24  Simplification rules
% 9.39/3.24  ----------------------
% 9.39/3.24  #Subsume      : 441
% 9.39/3.24  #Demod        : 2959
% 9.39/3.24  #Tautology    : 1329
% 9.39/3.24  #SimpNegUnit  : 19
% 9.39/3.24  #BackRed      : 596
% 9.39/3.24  
% 9.39/3.24  #Partial instantiations: 0
% 9.39/3.24  #Strategies tried      : 1
% 9.39/3.24  
% 9.39/3.24  Timing (in seconds)
% 9.39/3.24  ----------------------
% 9.39/3.24  Preprocessing        : 0.36
% 9.39/3.25  Parsing              : 0.18
% 9.39/3.25  CNF conversion       : 0.03
% 9.39/3.25  Main loop            : 2.05
% 9.39/3.25  Inferencing          : 0.66
% 9.39/3.25  Reduction            : 0.73
% 9.39/3.25  Demodulation         : 0.52
% 9.39/3.25  BG Simplification    : 0.07
% 9.39/3.25  Subsumption          : 0.40
% 9.39/3.25  Abstraction          : 0.08
% 9.39/3.25  MUC search           : 0.00
% 9.39/3.25  Cooper               : 0.00
% 9.39/3.25  Total                : 2.51
% 9.39/3.25  Index Insertion      : 0.00
% 9.39/3.25  Index Deletion       : 0.00
% 9.39/3.25  Index Matching       : 0.00
% 9.39/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

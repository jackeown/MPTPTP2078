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
% DateTime   : Thu Dec  3 10:16:01 EST 2020

% Result     : Theorem 23.38s
% Output     : CNFRefutation 23.49s
% Verified   : 
% Statistics : Number of formulae       :  335 (6991 expanded)
%              Number of leaves         :   53 (2255 expanded)
%              Depth                    :   22
%              Number of atoms          :  677 (16171 expanded)
%              Number of equality atoms :  172 (5235 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_218,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_155,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_177,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_175,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_151,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_165,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_205,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_102,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_33109,plain,(
    ! [C_4377,A_4378,B_4379] :
      ( v1_relat_1(C_4377)
      | ~ m1_subset_1(C_4377,k1_zfmisc_1(k2_zfmisc_1(A_4378,B_4379))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_33131,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_33109])).

tff(c_108,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_104,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_34517,plain,(
    ! [C_4569,A_4570,B_4571] :
      ( v2_funct_1(C_4569)
      | ~ v3_funct_2(C_4569,A_4570,B_4571)
      | ~ v1_funct_1(C_4569)
      | ~ m1_subset_1(C_4569,k1_zfmisc_1(k2_zfmisc_1(A_4570,B_4571))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34534,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_34517])).

tff(c_34543,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_104,c_34534])).

tff(c_80,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_35329,plain,(
    ! [A_4642,B_4643,C_4644,D_4645] :
      ( r2_relset_1(A_4642,B_4643,C_4644,C_4644)
      | ~ m1_subset_1(D_4645,k1_zfmisc_1(k2_zfmisc_1(A_4642,B_4643)))
      | ~ m1_subset_1(C_4644,k1_zfmisc_1(k2_zfmisc_1(A_4642,B_4643))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_35355,plain,(
    ! [A_4646,C_4647] :
      ( r2_relset_1(A_4646,A_4646,C_4647,C_4647)
      | ~ m1_subset_1(C_4647,k1_zfmisc_1(k2_zfmisc_1(A_4646,A_4646))) ) ),
    inference(resolution,[status(thm)],[c_80,c_35329])).

tff(c_35383,plain,(
    ! [A_41] : r2_relset_1(A_41,A_41,k6_partfun1(A_41),k6_partfun1(A_41)) ),
    inference(resolution,[status(thm)],[c_80,c_35355])).

tff(c_33366,plain,(
    ! [C_4406,B_4407,A_4408] :
      ( v5_relat_1(C_4406,B_4407)
      | ~ m1_subset_1(C_4406,k1_zfmisc_1(k2_zfmisc_1(A_4408,B_4407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_33390,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_33366])).

tff(c_33541,plain,(
    ! [B_4440,A_4441] :
      ( k2_relat_1(B_4440) = A_4441
      | ~ v2_funct_2(B_4440,A_4441)
      | ~ v5_relat_1(B_4440,A_4441)
      | ~ v1_relat_1(B_4440) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_33553,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_33390,c_33541])).

tff(c_33566,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33131,c_33553])).

tff(c_33582,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_33566])).

tff(c_34181,plain,(
    ! [C_4520,B_4521,A_4522] :
      ( v2_funct_2(C_4520,B_4521)
      | ~ v3_funct_2(C_4520,A_4522,B_4521)
      | ~ v1_funct_1(C_4520)
      | ~ m1_subset_1(C_4520,k1_zfmisc_1(k2_zfmisc_1(A_4522,B_4521))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34201,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_34181])).

tff(c_34212,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_104,c_34201])).

tff(c_34214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33582,c_34212])).

tff(c_34215,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_33566])).

tff(c_86,plain,(
    ! [A_50] : k6_relat_1(A_50) = k6_partfun1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_32,plain,(
    ! [A_14] :
      ( k5_relat_1(k2_funct_1(A_14),A_14) = k6_relat_1(k2_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_110,plain,(
    ! [A_14] :
      ( k5_relat_1(k2_funct_1(A_14),A_14) = k6_partfun1(k2_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_32])).

tff(c_106,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_35543,plain,(
    ! [A_4664,B_4665] :
      ( k2_funct_2(A_4664,B_4665) = k2_funct_1(B_4665)
      | ~ m1_subset_1(B_4665,k1_zfmisc_1(k2_zfmisc_1(A_4664,A_4664)))
      | ~ v3_funct_2(B_4665,A_4664,A_4664)
      | ~ v1_funct_2(B_4665,A_4664,A_4664)
      | ~ v1_funct_1(B_4665) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_35569,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_35543])).

tff(c_35583,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_35569])).

tff(c_35420,plain,(
    ! [A_4653,B_4654] :
      ( v1_funct_1(k2_funct_2(A_4653,B_4654))
      | ~ m1_subset_1(B_4654,k1_zfmisc_1(k2_zfmisc_1(A_4653,A_4653)))
      | ~ v3_funct_2(B_4654,A_4653,A_4653)
      | ~ v1_funct_2(B_4654,A_4653,A_4653)
      | ~ v1_funct_1(B_4654) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_35446,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_35420])).

tff(c_35460,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_35446])).

tff(c_35584,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35583,c_35460])).

tff(c_70,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k2_funct_2(A_39,B_40),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_zfmisc_1(A_39,A_39)))
      | ~ v3_funct_2(B_40,A_39,A_39)
      | ~ v1_funct_2(B_40,A_39,A_39)
      | ~ v1_funct_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_36254,plain,(
    ! [F_4721,C_4722,D_4718,B_4719,E_4717,A_4720] :
      ( k1_partfun1(A_4720,B_4719,C_4722,D_4718,E_4717,F_4721) = k5_relat_1(E_4717,F_4721)
      | ~ m1_subset_1(F_4721,k1_zfmisc_1(k2_zfmisc_1(C_4722,D_4718)))
      | ~ v1_funct_1(F_4721)
      | ~ m1_subset_1(E_4717,k1_zfmisc_1(k2_zfmisc_1(A_4720,B_4719)))
      | ~ v1_funct_1(E_4717) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_36276,plain,(
    ! [A_4720,B_4719,E_4717] :
      ( k1_partfun1(A_4720,B_4719,'#skF_1','#skF_1',E_4717,'#skF_2') = k5_relat_1(E_4717,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_4717,k1_zfmisc_1(k2_zfmisc_1(A_4720,B_4719)))
      | ~ v1_funct_1(E_4717) ) ),
    inference(resolution,[status(thm)],[c_102,c_36254])).

tff(c_36313,plain,(
    ! [A_4723,B_4724,E_4725] :
      ( k1_partfun1(A_4723,B_4724,'#skF_1','#skF_1',E_4725,'#skF_2') = k5_relat_1(E_4725,'#skF_2')
      | ~ m1_subset_1(E_4725,k1_zfmisc_1(k2_zfmisc_1(A_4723,B_4724)))
      | ~ v1_funct_1(E_4725) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_36276])).

tff(c_37368,plain,(
    ! [A_4762,B_4763] :
      ( k1_partfun1(A_4762,A_4762,'#skF_1','#skF_1',k2_funct_2(A_4762,B_4763),'#skF_2') = k5_relat_1(k2_funct_2(A_4762,B_4763),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_4762,B_4763))
      | ~ m1_subset_1(B_4763,k1_zfmisc_1(k2_zfmisc_1(A_4762,A_4762)))
      | ~ v3_funct_2(B_4763,A_4762,A_4762)
      | ~ v1_funct_2(B_4763,A_4762,A_4762)
      | ~ v1_funct_1(B_4763) ) ),
    inference(resolution,[status(thm)],[c_70,c_36313])).

tff(c_37401,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_37368])).

tff(c_37428,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_35584,c_35583,c_35583,c_35583,c_37401])).

tff(c_298,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_320,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_298])).

tff(c_1497,plain,(
    ! [C_241,A_242,B_243] :
      ( v2_funct_1(C_241)
      | ~ v3_funct_2(C_241,A_242,B_243)
      | ~ v1_funct_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1514,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_1497])).

tff(c_1523,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_104,c_1514])).

tff(c_2285,plain,(
    ! [A_311,B_312,C_313,D_314] :
      ( r2_relset_1(A_311,B_312,C_313,C_313)
      | ~ m1_subset_1(D_314,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312)))
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2311,plain,(
    ! [A_315,C_316] :
      ( r2_relset_1(A_315,A_315,C_316,C_316)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_315,A_315))) ) ),
    inference(resolution,[status(thm)],[c_80,c_2285])).

tff(c_2339,plain,(
    ! [A_41] : r2_relset_1(A_41,A_41,k6_partfun1(A_41),k6_partfun1(A_41)) ),
    inference(resolution,[status(thm)],[c_80,c_2311])).

tff(c_30,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_111,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_30])).

tff(c_368,plain,(
    ! [A_85] : v1_relat_1(k6_partfun1(A_85)) ),
    inference(resolution,[status(thm)],[c_80,c_298])).

tff(c_24,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_374,plain,(
    ! [A_85] :
      ( k2_relat_1(k6_partfun1(A_85)) != k1_xboole_0
      | k6_partfun1(A_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_368,c_24])).

tff(c_390,plain,(
    ! [A_88] :
      ( k1_xboole_0 != A_88
      | k6_partfun1(A_88) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_374])).

tff(c_100,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_185,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_401,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_185])).

tff(c_500,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_1213,plain,(
    ! [A_199,B_200,C_201] :
      ( k1_relset_1(A_199,B_200,C_201) = k1_relat_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1239,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_1213])).

tff(c_2093,plain,(
    ! [B_300,A_301,C_302] :
      ( k1_xboole_0 = B_300
      | k1_relset_1(A_301,B_300,C_302) = A_301
      | ~ v1_funct_2(C_302,A_301,B_300)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_301,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2113,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_2093])).

tff(c_2125,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1239,c_2113])).

tff(c_2126,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_2125])).

tff(c_34,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k2_funct_1(A_14)) = k6_relat_1(k1_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_109,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k2_funct_1(A_14)) = k6_partfun1(k1_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_34])).

tff(c_2501,plain,(
    ! [A_335,B_336] :
      ( k2_funct_2(A_335,B_336) = k2_funct_1(B_336)
      | ~ m1_subset_1(B_336,k1_zfmisc_1(k2_zfmisc_1(A_335,A_335)))
      | ~ v3_funct_2(B_336,A_335,A_335)
      | ~ v1_funct_2(B_336,A_335,A_335)
      | ~ v1_funct_1(B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2527,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_2501])).

tff(c_2541,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_2527])).

tff(c_2373,plain,(
    ! [A_322,B_323] :
      ( v1_funct_1(k2_funct_2(A_322,B_323))
      | ~ m1_subset_1(B_323,k1_zfmisc_1(k2_zfmisc_1(A_322,A_322)))
      | ~ v3_funct_2(B_323,A_322,A_322)
      | ~ v1_funct_2(B_323,A_322,A_322)
      | ~ v1_funct_1(B_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2399,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_2373])).

tff(c_2413,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_2399])).

tff(c_2542,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2541,c_2413])).

tff(c_2949,plain,(
    ! [A_387,B_388] :
      ( m1_subset_1(k2_funct_2(A_387,B_388),k1_zfmisc_1(k2_zfmisc_1(A_387,A_387)))
      | ~ m1_subset_1(B_388,k1_zfmisc_1(k2_zfmisc_1(A_387,A_387)))
      | ~ v3_funct_2(B_388,A_387,A_387)
      | ~ v1_funct_2(B_388,A_387,A_387)
      | ~ v1_funct_1(B_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2999,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2541,c_2949])).

tff(c_3026,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_102,c_2999])).

tff(c_3249,plain,(
    ! [B_394,E_392,C_397,D_393,F_396,A_395] :
      ( k1_partfun1(A_395,B_394,C_397,D_393,E_392,F_396) = k5_relat_1(E_392,F_396)
      | ~ m1_subset_1(F_396,k1_zfmisc_1(k2_zfmisc_1(C_397,D_393)))
      | ~ v1_funct_1(F_396)
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(A_395,B_394)))
      | ~ v1_funct_1(E_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3251,plain,(
    ! [A_395,B_394,E_392] :
      ( k1_partfun1(A_395,B_394,'#skF_1','#skF_1',E_392,k2_funct_1('#skF_2')) = k5_relat_1(E_392,k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(A_395,B_394)))
      | ~ v1_funct_1(E_392) ) ),
    inference(resolution,[status(thm)],[c_3026,c_3249])).

tff(c_13584,plain,(
    ! [A_783,B_784,E_785] :
      ( k1_partfun1(A_783,B_784,'#skF_1','#skF_1',E_785,k2_funct_1('#skF_2')) = k5_relat_1(E_785,k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_785,k1_zfmisc_1(k2_zfmisc_1(A_783,B_784)))
      | ~ v1_funct_1(E_785) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_3251])).

tff(c_13655,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_13584])).

tff(c_13710,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_13655])).

tff(c_2543,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2541,c_185])).

tff(c_13711,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13710,c_2543])).

tff(c_13718,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_13711])).

tff(c_13724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_108,c_1523,c_2339,c_2126,c_13718])).

tff(c_13726,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13746,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13726,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13745,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13726,c_13726,c_12])).

tff(c_186,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_207,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_102,c_186])).

tff(c_231,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_207,c_231])).

tff(c_456,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_13811,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13745,c_456])).

tff(c_13816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13746,c_13811])).

tff(c_13817,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_13825,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13817,c_102])).

tff(c_15691,plain,(
    ! [C_1035,A_1036,B_1037] :
      ( v2_funct_1(C_1035)
      | ~ v3_funct_2(C_1035,A_1036,B_1037)
      | ~ v1_funct_1(C_1035)
      | ~ m1_subset_1(C_1035,k1_zfmisc_1(k2_zfmisc_1(A_1036,B_1037))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_15803,plain,(
    ! [C_1051] :
      ( v2_funct_1(C_1051)
      | ~ v3_funct_2(C_1051,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1051)
      | ~ m1_subset_1(C_1051,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13817,c_15691])).

tff(c_15809,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_13825,c_15803])).

tff(c_15821,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_104,c_15809])).

tff(c_16521,plain,(
    ! [A_1105,B_1106,C_1107,D_1108] :
      ( r2_relset_1(A_1105,B_1106,C_1107,C_1107)
      | ~ m1_subset_1(D_1108,k1_zfmisc_1(k2_zfmisc_1(A_1105,B_1106)))
      | ~ m1_subset_1(C_1107,k1_zfmisc_1(k2_zfmisc_1(A_1105,B_1106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16547,plain,(
    ! [A_1109,C_1110] :
      ( r2_relset_1(A_1109,A_1109,C_1110,C_1110)
      | ~ m1_subset_1(C_1110,k1_zfmisc_1(k2_zfmisc_1(A_1109,A_1109))) ) ),
    inference(resolution,[status(thm)],[c_80,c_16521])).

tff(c_16575,plain,(
    ! [A_41] : r2_relset_1(A_41,A_41,k6_partfun1(A_41),k6_partfun1(A_41)) ),
    inference(resolution,[status(thm)],[c_80,c_16547])).

tff(c_15219,plain,(
    ! [A_975,B_976,C_977] :
      ( k1_relset_1(A_975,B_976,C_977) = k1_relat_1(C_977)
      | ~ m1_subset_1(C_977,k1_zfmisc_1(k2_zfmisc_1(A_975,B_976))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_15278,plain,(
    ! [C_983] :
      ( k1_relset_1('#skF_1','#skF_1',C_983) = k1_relat_1(C_983)
      | ~ m1_subset_1(C_983,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13817,c_15219])).

tff(c_15295,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_13825,c_15278])).

tff(c_13883,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_16176,plain,(
    ! [B_1086,A_1087,C_1088] :
      ( k1_xboole_0 = B_1086
      | k1_relset_1(A_1087,B_1086,C_1088) = A_1087
      | ~ v1_funct_2(C_1088,A_1087,B_1086)
      | ~ m1_subset_1(C_1088,k1_zfmisc_1(k2_zfmisc_1(A_1087,B_1086))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_16182,plain,(
    ! [C_1088] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1('#skF_1','#skF_1',C_1088) = '#skF_1'
      | ~ v1_funct_2(C_1088,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1088,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13817,c_16176])).

tff(c_16235,plain,(
    ! [C_1091] :
      ( k1_relset_1('#skF_1','#skF_1',C_1091) = '#skF_1'
      | ~ v1_funct_2(C_1091,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1091,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13883,c_16182])).

tff(c_16241,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_13825,c_16235])).

tff(c_16254,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_15295,c_16241])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_430,plain,(
    ! [C_89,B_90,A_91] :
      ( v5_relat_1(C_89,B_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_454,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_430])).

tff(c_13983,plain,(
    ! [B_810,A_811] :
      ( k2_relat_1(B_810) = A_811
      | ~ v2_funct_2(B_810,A_811)
      | ~ v5_relat_1(B_810,A_811)
      | ~ v1_relat_1(B_810) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_13989,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_454,c_13983])).

tff(c_13998,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_13989])).

tff(c_14007,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_13998])).

tff(c_14905,plain,(
    ! [C_935,B_936,A_937] :
      ( v2_funct_2(C_935,B_936)
      | ~ v3_funct_2(C_935,A_937,B_936)
      | ~ v1_funct_1(C_935)
      | ~ m1_subset_1(C_935,k1_zfmisc_1(k2_zfmisc_1(A_937,B_936))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14932,plain,(
    ! [C_942] :
      ( v2_funct_2(C_942,'#skF_1')
      | ~ v3_funct_2(C_942,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_942)
      | ~ m1_subset_1(C_942,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13817,c_14905])).

tff(c_14938,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_13825,c_14932])).

tff(c_14951,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_104,c_14938])).

tff(c_14953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14007,c_14951])).

tff(c_14954,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13998])).

tff(c_94,plain,(
    ! [B_55,A_54] :
      ( m1_subset_1(B_55,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_55),A_54)))
      | ~ r1_tarski(k2_relat_1(B_55),A_54)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_16269,plain,(
    ! [A_54] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_54)))
      | ~ r1_tarski(k2_relat_1('#skF_2'),A_54)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16254,c_94])).

tff(c_16278,plain,(
    ! [A_54] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_54)))
      | ~ r1_tarski('#skF_1',A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_108,c_14954,c_16269])).

tff(c_16772,plain,(
    ! [A_1130,B_1131] :
      ( k2_funct_2(A_1130,B_1131) = k2_funct_1(B_1131)
      | ~ m1_subset_1(B_1131,k1_zfmisc_1(k2_zfmisc_1(A_1130,A_1130)))
      | ~ v3_funct_2(B_1131,A_1130,A_1130)
      | ~ v1_funct_2(B_1131,A_1130,A_1130)
      | ~ v1_funct_1(B_1131) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_16776,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_16278,c_16772])).

tff(c_16805,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_108,c_106,c_104,c_16776])).

tff(c_16616,plain,(
    ! [A_1117,B_1118] :
      ( v1_funct_1(k2_funct_2(A_1117,B_1118))
      | ~ m1_subset_1(B_1118,k1_zfmisc_1(k2_zfmisc_1(A_1117,A_1117)))
      | ~ v3_funct_2(B_1118,A_1117,A_1117)
      | ~ v1_funct_2(B_1118,A_1117,A_1117)
      | ~ v1_funct_1(B_1118) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_16620,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_16278,c_16616])).

tff(c_16649,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_108,c_106,c_104,c_16620])).

tff(c_16810,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16805,c_16649])).

tff(c_17167,plain,(
    ! [A_1174,B_1175] :
      ( v3_funct_2(k2_funct_2(A_1174,B_1175),A_1174,A_1174)
      | ~ m1_subset_1(B_1175,k1_zfmisc_1(k2_zfmisc_1(A_1174,A_1174)))
      | ~ v3_funct_2(B_1175,A_1174,A_1174)
      | ~ v1_funct_2(B_1175,A_1174,A_1174)
      | ~ v1_funct_1(B_1175) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_17170,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_16278,c_17167])).

tff(c_17192,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_108,c_106,c_104,c_16805,c_17170])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_15822,plain,(
    ! [A_7] :
      ( v2_funct_1(A_7)
      | ~ v3_funct_2(A_7,'#skF_1','#skF_1')
      | ~ v1_funct_1(A_7)
      | ~ r1_tarski(A_7,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_15803])).

tff(c_17199,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_17192,c_15822])).

tff(c_17202,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16810,c_17199])).

tff(c_17203,plain,(
    ~ r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_17202])).

tff(c_17282,plain,(
    ! [A_1179,B_1180] :
      ( m1_subset_1(k2_funct_2(A_1179,B_1180),k1_zfmisc_1(k2_zfmisc_1(A_1179,A_1179)))
      | ~ m1_subset_1(B_1180,k1_zfmisc_1(k2_zfmisc_1(A_1179,A_1179)))
      | ~ v3_funct_2(B_1180,A_1179,A_1179)
      | ~ v1_funct_2(B_1180,A_1179,A_1179)
      | ~ v1_funct_1(B_1180) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_17332,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16805,c_17282])).

tff(c_17362,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_13825,c_13817,c_13817,c_17332])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_17405,plain,(
    r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_17362,c_18])).

tff(c_17433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17203,c_17405])).

tff(c_17435,plain,(
    r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_17202])).

tff(c_17786,plain,(
    ! [A_1192,D_1190,B_1191,F_1193,E_1189,C_1194] :
      ( k1_partfun1(A_1192,B_1191,C_1194,D_1190,E_1189,F_1193) = k5_relat_1(E_1189,F_1193)
      | ~ m1_subset_1(F_1193,k1_zfmisc_1(k2_zfmisc_1(C_1194,D_1190)))
      | ~ v1_funct_1(F_1193)
      | ~ m1_subset_1(E_1189,k1_zfmisc_1(k2_zfmisc_1(A_1192,B_1191)))
      | ~ v1_funct_1(E_1189) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_26908,plain,(
    ! [E_1553,C_1554,D_1552,B_1557,A_1556,A_1555] :
      ( k1_partfun1(A_1556,B_1557,C_1554,D_1552,E_1553,A_1555) = k5_relat_1(E_1553,A_1555)
      | ~ v1_funct_1(A_1555)
      | ~ m1_subset_1(E_1553,k1_zfmisc_1(k2_zfmisc_1(A_1556,B_1557)))
      | ~ v1_funct_1(E_1553)
      | ~ r1_tarski(A_1555,k2_zfmisc_1(C_1554,D_1552)) ) ),
    inference(resolution,[status(thm)],[c_20,c_17786])).

tff(c_26979,plain,(
    ! [C_1558,D_1559,E_1560,A_1561] :
      ( k1_partfun1('#skF_1','#skF_1',C_1558,D_1559,E_1560,A_1561) = k5_relat_1(E_1560,A_1561)
      | ~ v1_funct_1(A_1561)
      | ~ m1_subset_1(E_1560,k1_zfmisc_1('#skF_2'))
      | ~ v1_funct_1(E_1560)
      | ~ r1_tarski(A_1561,k2_zfmisc_1(C_1558,D_1559)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13817,c_26908])).

tff(c_27001,plain,(
    ! [C_1558,D_1559,A_1561] :
      ( k1_partfun1('#skF_1','#skF_1',C_1558,D_1559,'#skF_2',A_1561) = k5_relat_1('#skF_2',A_1561)
      | ~ v1_funct_1(A_1561)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_1561,k2_zfmisc_1(C_1558,D_1559)) ) ),
    inference(resolution,[status(thm)],[c_13825,c_26979])).

tff(c_27076,plain,(
    ! [C_1565,D_1566,A_1567] :
      ( k1_partfun1('#skF_1','#skF_1',C_1565,D_1566,'#skF_2',A_1567) = k5_relat_1('#skF_2',A_1567)
      | ~ v1_funct_1(A_1567)
      | ~ r1_tarski(A_1567,k2_zfmisc_1(C_1565,D_1566)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_27001])).

tff(c_27251,plain,(
    ! [A_1572] :
      ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',A_1572) = k5_relat_1('#skF_2',A_1572)
      | ~ v1_funct_1(A_1572)
      | ~ r1_tarski(A_1572,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13817,c_27076])).

tff(c_27278,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_17435,c_27251])).

tff(c_27314,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16810,c_27278])).

tff(c_16811,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16805,c_185])).

tff(c_27320,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27314,c_16811])).

tff(c_27327,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_27320])).

tff(c_27333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_108,c_15821,c_16575,c_16254,c_27327])).

tff(c_27335,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_173,plain,(
    ! [A_66] : m1_subset_1(k6_partfun1(A_66),k1_zfmisc_1(k2_zfmisc_1(A_66,A_66))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_177,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_173])).

tff(c_202,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_177,c_186])).

tff(c_237,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_202,c_231])).

tff(c_246,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_237])).

tff(c_271,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_111])).

tff(c_27344,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27335,c_27335,c_271])).

tff(c_27352,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27335,c_27335,c_14])).

tff(c_27397,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27352,c_13817])).

tff(c_367,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_320,c_24])).

tff(c_428,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_27339,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27335,c_428])).

tff(c_27422,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27397,c_27339])).

tff(c_27435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27344,c_27422])).

tff(c_27436,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_28538,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27436,c_27436,c_401])).

tff(c_28539,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_28538])).

tff(c_27477,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27436,c_8])).

tff(c_28,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    ! [A_13] : k1_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_28])).

tff(c_26,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_371,plain,(
    ! [A_85] :
      ( k1_relat_1(k6_partfun1(A_85)) != k1_xboole_0
      | k6_partfun1(A_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_368,c_26])).

tff(c_378,plain,(
    ! [A_85] :
      ( k1_xboole_0 != A_85
      | k6_partfun1(A_85) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_371])).

tff(c_27660,plain,(
    ! [A_1595] :
      ( A_1595 != '#skF_2'
      | k6_partfun1(A_1595) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27436,c_27436,c_378])).

tff(c_27674,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_27660,c_185])).

tff(c_27702,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_27674])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27474,plain,(
    ! [A_6] : m1_subset_1('#skF_2',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27436,c_16])).

tff(c_28200,plain,(
    ! [C_1666,B_1667,A_1668] :
      ( v2_funct_2(C_1666,B_1667)
      | ~ v3_funct_2(C_1666,A_1668,B_1667)
      | ~ v1_funct_1(C_1666)
      | ~ m1_subset_1(C_1666,k1_zfmisc_1(k2_zfmisc_1(A_1668,B_1667))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28210,plain,(
    ! [B_1667,A_1668] :
      ( v2_funct_2('#skF_2',B_1667)
      | ~ v3_funct_2('#skF_2',A_1668,B_1667)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_27474,c_28200])).

tff(c_28228,plain,(
    ! [B_1669,A_1670] :
      ( v2_funct_2('#skF_2',B_1669)
      | ~ v3_funct_2('#skF_2',A_1670,B_1669) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_28210])).

tff(c_28232,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_104,c_28228])).

tff(c_27437,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_27487,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27436,c_27437])).

tff(c_27438,plain,(
    ! [C_1581,B_1582,A_1583] :
      ( v5_relat_1(C_1581,B_1582)
      | ~ m1_subset_1(C_1581,k1_zfmisc_1(k2_zfmisc_1(A_1583,B_1582))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_27461,plain,(
    ! [B_1582] : v5_relat_1(k1_xboole_0,B_1582) ),
    inference(resolution,[status(thm)],[c_16,c_27438])).

tff(c_27483,plain,(
    ! [B_1582] : v5_relat_1('#skF_2',B_1582) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27436,c_27461])).

tff(c_27720,plain,(
    ! [B_1598,A_1599] :
      ( k2_relat_1(B_1598) = A_1599
      | ~ v2_funct_2(B_1598,A_1599)
      | ~ v5_relat_1(B_1598,A_1599)
      | ~ v1_relat_1(B_1598) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_27726,plain,(
    ! [B_1582] :
      ( k2_relat_1('#skF_2') = B_1582
      | ~ v2_funct_2('#skF_2',B_1582)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_27483,c_27720])).

tff(c_27732,plain,(
    ! [B_1582] :
      ( B_1582 = '#skF_2'
      | ~ v2_funct_2('#skF_2',B_1582) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_27487,c_27726])).

tff(c_28235,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28232,c_27732])).

tff(c_28239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27702,c_28235])).

tff(c_28241,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_27674])).

tff(c_27476,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27436,c_27436,c_12])).

tff(c_28243,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28241,c_28241,c_27476])).

tff(c_27523,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_28535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28243,c_28241,c_27523])).

tff(c_28536,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_204,plain,(
    ! [A_41] : r1_tarski(k6_partfun1(A_41),k2_zfmisc_1(A_41,A_41)) ),
    inference(resolution,[status(thm)],[c_80,c_186])).

tff(c_28553,plain,(
    r1_tarski(k6_partfun1('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28536,c_204])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28693,plain,
    ( k6_partfun1('#skF_1') = '#skF_2'
    | ~ r1_tarski('#skF_2',k6_partfun1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28553,c_2])).

tff(c_28696,plain,(
    k6_partfun1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27477,c_28693])).

tff(c_28723,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_28696,c_111])).

tff(c_28732,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28723,c_27487])).

tff(c_28734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28539,c_28732])).

tff(c_28736,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_28538])).

tff(c_28853,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28736,c_27474])).

tff(c_29790,plain,(
    ! [A_1817,B_1818,C_1819,D_1820] :
      ( r2_relset_1(A_1817,B_1818,C_1819,C_1819)
      | ~ m1_subset_1(D_1820,k1_zfmisc_1(k2_zfmisc_1(A_1817,B_1818)))
      | ~ m1_subset_1(C_1819,k1_zfmisc_1(k2_zfmisc_1(A_1817,B_1818))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30510,plain,(
    ! [A_4139,B_4140,C_4141] :
      ( r2_relset_1(A_4139,B_4140,C_4141,C_4141)
      | ~ m1_subset_1(C_4141,k1_zfmisc_1(k2_zfmisc_1(A_4139,B_4140))) ) ),
    inference(resolution,[status(thm)],[c_28853,c_29790])).

tff(c_30526,plain,(
    ! [A_4139,B_4140] : r2_relset_1(A_4139,B_4140,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_28853,c_30510])).

tff(c_28760,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28736,c_108])).

tff(c_28755,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28736,c_320])).

tff(c_29431,plain,(
    ! [C_1768,A_1769,B_1770] :
      ( v2_funct_1(C_1768)
      | ~ v3_funct_2(C_1768,A_1769,B_1770)
      | ~ v1_funct_1(C_1768)
      | ~ m1_subset_1(C_1768,k1_zfmisc_1(k2_zfmisc_1(A_1769,B_1770))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_29438,plain,(
    ! [A_1769,B_1770] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_1769,B_1770)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28853,c_29431])).

tff(c_29451,plain,(
    ! [A_1769,B_1770] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_1769,B_1770) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28760,c_29438])).

tff(c_29454,plain,(
    ! [A_1769,B_1770] : ~ v3_funct_2('#skF_1',A_1769,B_1770) ),
    inference(splitLeft,[status(thm)],[c_29451])).

tff(c_28758,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28736,c_104])).

tff(c_29456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29454,c_28758])).

tff(c_29457,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_29451])).

tff(c_28754,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28736,c_27436])).

tff(c_28982,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28754,c_28754,c_378])).

tff(c_268,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_112])).

tff(c_27468,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27436,c_27436,c_268])).

tff(c_28747,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28736,c_28736,c_27468])).

tff(c_28913,plain,(
    ! [A_1706,B_1707,C_1708] :
      ( k1_relset_1(A_1706,B_1707,C_1708) = k1_relat_1(C_1708)
      | ~ m1_subset_1(C_1708,k1_zfmisc_1(k2_zfmisc_1(A_1706,B_1707))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28920,plain,(
    ! [A_1706,B_1707] : k1_relset_1(A_1706,B_1707,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28853,c_28913])).

tff(c_28932,plain,(
    ! [A_1706,B_1707] : k1_relset_1(A_1706,B_1707,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28747,c_28920])).

tff(c_58,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_116,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_29212,plain,(
    ! [C_1740,B_1741] :
      ( v1_funct_2(C_1740,'#skF_1',B_1741)
      | k1_relset_1('#skF_1',B_1741,C_1740) != '#skF_1'
      | ~ m1_subset_1(C_1740,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28754,c_28754,c_28754,c_28754,c_116])).

tff(c_29215,plain,(
    ! [B_1741] :
      ( v1_funct_2('#skF_1','#skF_1',B_1741)
      | k1_relset_1('#skF_1',B_1741,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_28853,c_29212])).

tff(c_29221,plain,(
    ! [B_1741] : v1_funct_2('#skF_1','#skF_1',B_1741) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28932,c_29215])).

tff(c_28881,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28736,c_28736,c_27476])).

tff(c_29934,plain,(
    ! [A_1836,B_1837] :
      ( k2_funct_2(A_1836,B_1837) = k2_funct_1(B_1837)
      | ~ m1_subset_1(B_1837,k1_zfmisc_1(k2_zfmisc_1(A_1836,A_1836)))
      | ~ v3_funct_2(B_1837,A_1836,A_1836)
      | ~ v1_funct_2(B_1837,A_1836,A_1836)
      | ~ v1_funct_1(B_1837) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_29946,plain,(
    ! [A_1836] :
      ( k2_funct_2(A_1836,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_1836,A_1836)
      | ~ v1_funct_2('#skF_1',A_1836,A_1836)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28853,c_29934])).

tff(c_31681,plain,(
    ! [A_4251] :
      ( k2_funct_2(A_4251,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_4251,A_4251)
      | ~ v1_funct_2('#skF_1',A_4251,A_4251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28760,c_29946])).

tff(c_31684,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_28758,c_31681])).

tff(c_31687,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29221,c_31684])).

tff(c_31694,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31687,c_70])).

tff(c_31698,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28760,c_29221,c_28758,c_28853,c_28881,c_28881,c_31694])).

tff(c_31754,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_31698,c_18])).

tff(c_251,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_231])).

tff(c_27466,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27436,c_27436,c_251])).

tff(c_29025,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28736,c_28736,c_27466])).

tff(c_31800,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_31754,c_29025])).

tff(c_31826,plain,
    ( k6_partfun1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31800,c_109])).

tff(c_31835,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28755,c_28760,c_29457,c_28982,c_28747,c_31826])).

tff(c_30633,plain,(
    ! [B_4156,D_4155,F_4158,C_4159,A_4157,E_4154] :
      ( k1_partfun1(A_4157,B_4156,C_4159,D_4155,E_4154,F_4158) = k5_relat_1(E_4154,F_4158)
      | ~ m1_subset_1(F_4158,k1_zfmisc_1(k2_zfmisc_1(C_4159,D_4155)))
      | ~ v1_funct_1(F_4158)
      | ~ m1_subset_1(E_4154,k1_zfmisc_1(k2_zfmisc_1(A_4157,B_4156)))
      | ~ v1_funct_1(E_4154) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_30642,plain,(
    ! [B_4156,D_4155,C_4159,A_4157,E_4154] :
      ( k1_partfun1(A_4157,B_4156,C_4159,D_4155,E_4154,'#skF_1') = k5_relat_1(E_4154,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_4154,k1_zfmisc_1(k2_zfmisc_1(A_4157,B_4156)))
      | ~ v1_funct_1(E_4154) ) ),
    inference(resolution,[status(thm)],[c_28853,c_30633])).

tff(c_33039,plain,(
    ! [B_4369,E_4370,A_4372,D_4371,C_4368] :
      ( k1_partfun1(A_4372,B_4369,C_4368,D_4371,E_4370,'#skF_1') = k5_relat_1(E_4370,'#skF_1')
      | ~ m1_subset_1(E_4370,k1_zfmisc_1(k2_zfmisc_1(A_4372,B_4369)))
      | ~ v1_funct_1(E_4370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28760,c_30642])).

tff(c_33052,plain,(
    ! [A_4372,B_4369,C_4368,D_4371] :
      ( k1_partfun1(A_4372,B_4369,C_4368,D_4371,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28853,c_33039])).

tff(c_33066,plain,(
    ! [A_4372,B_4369,C_4368,D_4371] : k1_partfun1(A_4372,B_4369,C_4368,D_4371,'#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28760,c_31835,c_33052])).

tff(c_28756,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28736,c_28736,c_185])).

tff(c_29113,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28982,c_28756])).

tff(c_31689,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31687,c_29113])).

tff(c_31806,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31800,c_31689])).

tff(c_33069,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33066,c_31806])).

tff(c_33072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30526,c_33069])).

tff(c_33073,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_35586,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35583,c_33073])).

tff(c_37561,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37428,c_35586])).

tff(c_37568,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_37561])).

tff(c_37574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33131,c_108,c_34543,c_35383,c_34215,c_37568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:19:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.38/11.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.49/11.58  
% 23.49/11.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.49/11.59  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 23.49/11.59  
% 23.49/11.59  %Foreground sorts:
% 23.49/11.59  
% 23.49/11.59  
% 23.49/11.59  %Background operators:
% 23.49/11.59  
% 23.49/11.59  
% 23.49/11.59  %Foreground operators:
% 23.49/11.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 23.49/11.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.49/11.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 23.49/11.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 23.49/11.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.49/11.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 23.49/11.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.49/11.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.49/11.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 23.49/11.59  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 23.49/11.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.49/11.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.49/11.59  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 23.49/11.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 23.49/11.59  tff('#skF_2', type, '#skF_2': $i).
% 23.49/11.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 23.49/11.59  tff('#skF_1', type, '#skF_1': $i).
% 23.49/11.59  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 23.49/11.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 23.49/11.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 23.49/11.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.49/11.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 23.49/11.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.49/11.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.49/11.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.49/11.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 23.49/11.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.49/11.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 23.49/11.59  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 23.49/11.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.49/11.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.49/11.59  
% 23.49/11.62  tff(f_218, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 23.49/11.62  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.49/11.62  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 23.49/11.62  tff(f_155, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 23.49/11.62  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 23.49/11.62  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 23.49/11.62  tff(f_135, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 23.49/11.62  tff(f_177, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 23.49/11.62  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 23.49/11.62  tff(f_175, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 23.49/11.62  tff(f_151, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 23.49/11.62  tff(f_165, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 23.49/11.62  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 23.49/11.62  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 23.49/11.62  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 23.49/11.62  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 23.49/11.62  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 23.49/11.62  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 23.49/11.62  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 23.49/11.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.49/11.62  tff(f_205, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 23.49/11.62  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 23.49/11.62  tff(c_102, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 23.49/11.62  tff(c_33109, plain, (![C_4377, A_4378, B_4379]: (v1_relat_1(C_4377) | ~m1_subset_1(C_4377, k1_zfmisc_1(k2_zfmisc_1(A_4378, B_4379))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 23.49/11.62  tff(c_33131, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_33109])).
% 23.49/11.62  tff(c_108, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 23.49/11.62  tff(c_104, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 23.49/11.62  tff(c_34517, plain, (![C_4569, A_4570, B_4571]: (v2_funct_1(C_4569) | ~v3_funct_2(C_4569, A_4570, B_4571) | ~v1_funct_1(C_4569) | ~m1_subset_1(C_4569, k1_zfmisc_1(k2_zfmisc_1(A_4570, B_4571))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.49/11.62  tff(c_34534, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_34517])).
% 23.49/11.62  tff(c_34543, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_104, c_34534])).
% 23.49/11.62  tff(c_80, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 23.49/11.62  tff(c_35329, plain, (![A_4642, B_4643, C_4644, D_4645]: (r2_relset_1(A_4642, B_4643, C_4644, C_4644) | ~m1_subset_1(D_4645, k1_zfmisc_1(k2_zfmisc_1(A_4642, B_4643))) | ~m1_subset_1(C_4644, k1_zfmisc_1(k2_zfmisc_1(A_4642, B_4643))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 23.49/11.62  tff(c_35355, plain, (![A_4646, C_4647]: (r2_relset_1(A_4646, A_4646, C_4647, C_4647) | ~m1_subset_1(C_4647, k1_zfmisc_1(k2_zfmisc_1(A_4646, A_4646))))), inference(resolution, [status(thm)], [c_80, c_35329])).
% 23.49/11.62  tff(c_35383, plain, (![A_41]: (r2_relset_1(A_41, A_41, k6_partfun1(A_41), k6_partfun1(A_41)))), inference(resolution, [status(thm)], [c_80, c_35355])).
% 23.49/11.62  tff(c_33366, plain, (![C_4406, B_4407, A_4408]: (v5_relat_1(C_4406, B_4407) | ~m1_subset_1(C_4406, k1_zfmisc_1(k2_zfmisc_1(A_4408, B_4407))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.49/11.62  tff(c_33390, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_102, c_33366])).
% 23.49/11.62  tff(c_33541, plain, (![B_4440, A_4441]: (k2_relat_1(B_4440)=A_4441 | ~v2_funct_2(B_4440, A_4441) | ~v5_relat_1(B_4440, A_4441) | ~v1_relat_1(B_4440))), inference(cnfTransformation, [status(thm)], [f_135])).
% 23.49/11.62  tff(c_33553, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_33390, c_33541])).
% 23.49/11.62  tff(c_33566, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33131, c_33553])).
% 23.49/11.62  tff(c_33582, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_33566])).
% 23.49/11.62  tff(c_34181, plain, (![C_4520, B_4521, A_4522]: (v2_funct_2(C_4520, B_4521) | ~v3_funct_2(C_4520, A_4522, B_4521) | ~v1_funct_1(C_4520) | ~m1_subset_1(C_4520, k1_zfmisc_1(k2_zfmisc_1(A_4522, B_4521))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.49/11.62  tff(c_34201, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_34181])).
% 23.49/11.62  tff(c_34212, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_104, c_34201])).
% 23.49/11.62  tff(c_34214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33582, c_34212])).
% 23.49/11.62  tff(c_34215, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_33566])).
% 23.49/11.62  tff(c_86, plain, (![A_50]: (k6_relat_1(A_50)=k6_partfun1(A_50))), inference(cnfTransformation, [status(thm)], [f_177])).
% 23.49/11.62  tff(c_32, plain, (![A_14]: (k5_relat_1(k2_funct_1(A_14), A_14)=k6_relat_1(k2_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 23.49/11.62  tff(c_110, plain, (![A_14]: (k5_relat_1(k2_funct_1(A_14), A_14)=k6_partfun1(k2_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_32])).
% 23.49/11.62  tff(c_106, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 23.49/11.62  tff(c_35543, plain, (![A_4664, B_4665]: (k2_funct_2(A_4664, B_4665)=k2_funct_1(B_4665) | ~m1_subset_1(B_4665, k1_zfmisc_1(k2_zfmisc_1(A_4664, A_4664))) | ~v3_funct_2(B_4665, A_4664, A_4664) | ~v1_funct_2(B_4665, A_4664, A_4664) | ~v1_funct_1(B_4665))), inference(cnfTransformation, [status(thm)], [f_175])).
% 23.49/11.62  tff(c_35569, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_35543])).
% 23.49/11.62  tff(c_35583, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_35569])).
% 23.49/11.62  tff(c_35420, plain, (![A_4653, B_4654]: (v1_funct_1(k2_funct_2(A_4653, B_4654)) | ~m1_subset_1(B_4654, k1_zfmisc_1(k2_zfmisc_1(A_4653, A_4653))) | ~v3_funct_2(B_4654, A_4653, A_4653) | ~v1_funct_2(B_4654, A_4653, A_4653) | ~v1_funct_1(B_4654))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.49/11.62  tff(c_35446, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_35420])).
% 23.49/11.62  tff(c_35460, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_35446])).
% 23.49/11.62  tff(c_35584, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_35583, c_35460])).
% 23.49/11.62  tff(c_70, plain, (![A_39, B_40]: (m1_subset_1(k2_funct_2(A_39, B_40), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))) | ~v3_funct_2(B_40, A_39, A_39) | ~v1_funct_2(B_40, A_39, A_39) | ~v1_funct_1(B_40))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.49/11.62  tff(c_36254, plain, (![F_4721, C_4722, D_4718, B_4719, E_4717, A_4720]: (k1_partfun1(A_4720, B_4719, C_4722, D_4718, E_4717, F_4721)=k5_relat_1(E_4717, F_4721) | ~m1_subset_1(F_4721, k1_zfmisc_1(k2_zfmisc_1(C_4722, D_4718))) | ~v1_funct_1(F_4721) | ~m1_subset_1(E_4717, k1_zfmisc_1(k2_zfmisc_1(A_4720, B_4719))) | ~v1_funct_1(E_4717))), inference(cnfTransformation, [status(thm)], [f_165])).
% 23.49/11.62  tff(c_36276, plain, (![A_4720, B_4719, E_4717]: (k1_partfun1(A_4720, B_4719, '#skF_1', '#skF_1', E_4717, '#skF_2')=k5_relat_1(E_4717, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_4717, k1_zfmisc_1(k2_zfmisc_1(A_4720, B_4719))) | ~v1_funct_1(E_4717))), inference(resolution, [status(thm)], [c_102, c_36254])).
% 23.49/11.62  tff(c_36313, plain, (![A_4723, B_4724, E_4725]: (k1_partfun1(A_4723, B_4724, '#skF_1', '#skF_1', E_4725, '#skF_2')=k5_relat_1(E_4725, '#skF_2') | ~m1_subset_1(E_4725, k1_zfmisc_1(k2_zfmisc_1(A_4723, B_4724))) | ~v1_funct_1(E_4725))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_36276])).
% 23.49/11.62  tff(c_37368, plain, (![A_4762, B_4763]: (k1_partfun1(A_4762, A_4762, '#skF_1', '#skF_1', k2_funct_2(A_4762, B_4763), '#skF_2')=k5_relat_1(k2_funct_2(A_4762, B_4763), '#skF_2') | ~v1_funct_1(k2_funct_2(A_4762, B_4763)) | ~m1_subset_1(B_4763, k1_zfmisc_1(k2_zfmisc_1(A_4762, A_4762))) | ~v3_funct_2(B_4763, A_4762, A_4762) | ~v1_funct_2(B_4763, A_4762, A_4762) | ~v1_funct_1(B_4763))), inference(resolution, [status(thm)], [c_70, c_36313])).
% 23.49/11.62  tff(c_37401, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_37368])).
% 23.49/11.62  tff(c_37428, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_35584, c_35583, c_35583, c_35583, c_37401])).
% 23.49/11.62  tff(c_298, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 23.49/11.62  tff(c_320, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_298])).
% 23.49/11.62  tff(c_1497, plain, (![C_241, A_242, B_243]: (v2_funct_1(C_241) | ~v3_funct_2(C_241, A_242, B_243) | ~v1_funct_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.49/11.62  tff(c_1514, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_1497])).
% 23.49/11.62  tff(c_1523, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_104, c_1514])).
% 23.49/11.62  tff(c_2285, plain, (![A_311, B_312, C_313, D_314]: (r2_relset_1(A_311, B_312, C_313, C_313) | ~m1_subset_1(D_314, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 23.49/11.62  tff(c_2311, plain, (![A_315, C_316]: (r2_relset_1(A_315, A_315, C_316, C_316) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_315, A_315))))), inference(resolution, [status(thm)], [c_80, c_2285])).
% 23.49/11.62  tff(c_2339, plain, (![A_41]: (r2_relset_1(A_41, A_41, k6_partfun1(A_41), k6_partfun1(A_41)))), inference(resolution, [status(thm)], [c_80, c_2311])).
% 23.49/11.62  tff(c_30, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.49/11.62  tff(c_111, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_30])).
% 23.49/11.62  tff(c_368, plain, (![A_85]: (v1_relat_1(k6_partfun1(A_85)))), inference(resolution, [status(thm)], [c_80, c_298])).
% 23.49/11.62  tff(c_24, plain, (![A_12]: (k2_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.49/11.62  tff(c_374, plain, (![A_85]: (k2_relat_1(k6_partfun1(A_85))!=k1_xboole_0 | k6_partfun1(A_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_368, c_24])).
% 23.49/11.62  tff(c_390, plain, (![A_88]: (k1_xboole_0!=A_88 | k6_partfun1(A_88)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_374])).
% 23.49/11.62  tff(c_100, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 23.49/11.62  tff(c_185, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_100])).
% 23.49/11.62  tff(c_401, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_390, c_185])).
% 23.49/11.62  tff(c_500, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_401])).
% 23.49/11.62  tff(c_1213, plain, (![A_199, B_200, C_201]: (k1_relset_1(A_199, B_200, C_201)=k1_relat_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 23.49/11.62  tff(c_1239, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_1213])).
% 23.49/11.62  tff(c_2093, plain, (![B_300, A_301, C_302]: (k1_xboole_0=B_300 | k1_relset_1(A_301, B_300, C_302)=A_301 | ~v1_funct_2(C_302, A_301, B_300) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_301, B_300))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 23.49/11.62  tff(c_2113, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_102, c_2093])).
% 23.49/11.62  tff(c_2125, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1239, c_2113])).
% 23.49/11.62  tff(c_2126, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_500, c_2125])).
% 23.49/11.62  tff(c_34, plain, (![A_14]: (k5_relat_1(A_14, k2_funct_1(A_14))=k6_relat_1(k1_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 23.49/11.62  tff(c_109, plain, (![A_14]: (k5_relat_1(A_14, k2_funct_1(A_14))=k6_partfun1(k1_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_34])).
% 23.49/11.62  tff(c_2501, plain, (![A_335, B_336]: (k2_funct_2(A_335, B_336)=k2_funct_1(B_336) | ~m1_subset_1(B_336, k1_zfmisc_1(k2_zfmisc_1(A_335, A_335))) | ~v3_funct_2(B_336, A_335, A_335) | ~v1_funct_2(B_336, A_335, A_335) | ~v1_funct_1(B_336))), inference(cnfTransformation, [status(thm)], [f_175])).
% 23.49/11.62  tff(c_2527, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_2501])).
% 23.49/11.62  tff(c_2541, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_2527])).
% 23.49/11.62  tff(c_2373, plain, (![A_322, B_323]: (v1_funct_1(k2_funct_2(A_322, B_323)) | ~m1_subset_1(B_323, k1_zfmisc_1(k2_zfmisc_1(A_322, A_322))) | ~v3_funct_2(B_323, A_322, A_322) | ~v1_funct_2(B_323, A_322, A_322) | ~v1_funct_1(B_323))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.49/11.62  tff(c_2399, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_2373])).
% 23.49/11.62  tff(c_2413, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_2399])).
% 23.49/11.62  tff(c_2542, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2541, c_2413])).
% 23.49/11.62  tff(c_2949, plain, (![A_387, B_388]: (m1_subset_1(k2_funct_2(A_387, B_388), k1_zfmisc_1(k2_zfmisc_1(A_387, A_387))) | ~m1_subset_1(B_388, k1_zfmisc_1(k2_zfmisc_1(A_387, A_387))) | ~v3_funct_2(B_388, A_387, A_387) | ~v1_funct_2(B_388, A_387, A_387) | ~v1_funct_1(B_388))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.49/11.62  tff(c_2999, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2541, c_2949])).
% 23.49/11.62  tff(c_3026, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_102, c_2999])).
% 23.49/11.62  tff(c_3249, plain, (![B_394, E_392, C_397, D_393, F_396, A_395]: (k1_partfun1(A_395, B_394, C_397, D_393, E_392, F_396)=k5_relat_1(E_392, F_396) | ~m1_subset_1(F_396, k1_zfmisc_1(k2_zfmisc_1(C_397, D_393))) | ~v1_funct_1(F_396) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(A_395, B_394))) | ~v1_funct_1(E_392))), inference(cnfTransformation, [status(thm)], [f_165])).
% 23.49/11.62  tff(c_3251, plain, (![A_395, B_394, E_392]: (k1_partfun1(A_395, B_394, '#skF_1', '#skF_1', E_392, k2_funct_1('#skF_2'))=k5_relat_1(E_392, k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(A_395, B_394))) | ~v1_funct_1(E_392))), inference(resolution, [status(thm)], [c_3026, c_3249])).
% 23.49/11.62  tff(c_13584, plain, (![A_783, B_784, E_785]: (k1_partfun1(A_783, B_784, '#skF_1', '#skF_1', E_785, k2_funct_1('#skF_2'))=k5_relat_1(E_785, k2_funct_1('#skF_2')) | ~m1_subset_1(E_785, k1_zfmisc_1(k2_zfmisc_1(A_783, B_784))) | ~v1_funct_1(E_785))), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_3251])).
% 23.49/11.62  tff(c_13655, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_13584])).
% 23.49/11.62  tff(c_13710, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_13655])).
% 23.49/11.62  tff(c_2543, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2541, c_185])).
% 23.49/11.62  tff(c_13711, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13710, c_2543])).
% 23.49/11.62  tff(c_13718, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_13711])).
% 23.49/11.62  tff(c_13724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_108, c_1523, c_2339, c_2126, c_13718])).
% 23.49/11.62  tff(c_13726, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_401])).
% 23.49/11.62  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.49/11.62  tff(c_13746, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13726, c_8])).
% 23.49/11.62  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.49/11.62  tff(c_13745, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13726, c_13726, c_12])).
% 23.49/11.62  tff(c_186, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~m1_subset_1(A_70, k1_zfmisc_1(B_71)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.49/11.62  tff(c_207, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_102, c_186])).
% 23.49/11.62  tff(c_231, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.49/11.62  tff(c_243, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_207, c_231])).
% 23.49/11.62  tff(c_456, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_243])).
% 23.49/11.62  tff(c_13811, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13745, c_456])).
% 23.49/11.62  tff(c_13816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13746, c_13811])).
% 23.49/11.62  tff(c_13817, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_243])).
% 23.49/11.62  tff(c_13825, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13817, c_102])).
% 23.49/11.62  tff(c_15691, plain, (![C_1035, A_1036, B_1037]: (v2_funct_1(C_1035) | ~v3_funct_2(C_1035, A_1036, B_1037) | ~v1_funct_1(C_1035) | ~m1_subset_1(C_1035, k1_zfmisc_1(k2_zfmisc_1(A_1036, B_1037))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.49/11.62  tff(c_15803, plain, (![C_1051]: (v2_funct_1(C_1051) | ~v3_funct_2(C_1051, '#skF_1', '#skF_1') | ~v1_funct_1(C_1051) | ~m1_subset_1(C_1051, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_13817, c_15691])).
% 23.49/11.62  tff(c_15809, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_13825, c_15803])).
% 23.49/11.62  tff(c_15821, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_104, c_15809])).
% 23.49/11.62  tff(c_16521, plain, (![A_1105, B_1106, C_1107, D_1108]: (r2_relset_1(A_1105, B_1106, C_1107, C_1107) | ~m1_subset_1(D_1108, k1_zfmisc_1(k2_zfmisc_1(A_1105, B_1106))) | ~m1_subset_1(C_1107, k1_zfmisc_1(k2_zfmisc_1(A_1105, B_1106))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 23.49/11.62  tff(c_16547, plain, (![A_1109, C_1110]: (r2_relset_1(A_1109, A_1109, C_1110, C_1110) | ~m1_subset_1(C_1110, k1_zfmisc_1(k2_zfmisc_1(A_1109, A_1109))))), inference(resolution, [status(thm)], [c_80, c_16521])).
% 23.49/11.62  tff(c_16575, plain, (![A_41]: (r2_relset_1(A_41, A_41, k6_partfun1(A_41), k6_partfun1(A_41)))), inference(resolution, [status(thm)], [c_80, c_16547])).
% 23.49/11.62  tff(c_15219, plain, (![A_975, B_976, C_977]: (k1_relset_1(A_975, B_976, C_977)=k1_relat_1(C_977) | ~m1_subset_1(C_977, k1_zfmisc_1(k2_zfmisc_1(A_975, B_976))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 23.49/11.62  tff(c_15278, plain, (![C_983]: (k1_relset_1('#skF_1', '#skF_1', C_983)=k1_relat_1(C_983) | ~m1_subset_1(C_983, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_13817, c_15219])).
% 23.49/11.62  tff(c_15295, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_13825, c_15278])).
% 23.49/11.62  tff(c_13883, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_401])).
% 23.49/11.62  tff(c_16176, plain, (![B_1086, A_1087, C_1088]: (k1_xboole_0=B_1086 | k1_relset_1(A_1087, B_1086, C_1088)=A_1087 | ~v1_funct_2(C_1088, A_1087, B_1086) | ~m1_subset_1(C_1088, k1_zfmisc_1(k2_zfmisc_1(A_1087, B_1086))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 23.49/11.62  tff(c_16182, plain, (![C_1088]: (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', C_1088)='#skF_1' | ~v1_funct_2(C_1088, '#skF_1', '#skF_1') | ~m1_subset_1(C_1088, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_13817, c_16176])).
% 23.49/11.62  tff(c_16235, plain, (![C_1091]: (k1_relset_1('#skF_1', '#skF_1', C_1091)='#skF_1' | ~v1_funct_2(C_1091, '#skF_1', '#skF_1') | ~m1_subset_1(C_1091, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_13883, c_16182])).
% 23.49/11.62  tff(c_16241, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_13825, c_16235])).
% 23.49/11.62  tff(c_16254, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_15295, c_16241])).
% 23.49/11.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.49/11.62  tff(c_430, plain, (![C_89, B_90, A_91]: (v5_relat_1(C_89, B_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.49/11.62  tff(c_454, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_102, c_430])).
% 23.49/11.62  tff(c_13983, plain, (![B_810, A_811]: (k2_relat_1(B_810)=A_811 | ~v2_funct_2(B_810, A_811) | ~v5_relat_1(B_810, A_811) | ~v1_relat_1(B_810))), inference(cnfTransformation, [status(thm)], [f_135])).
% 23.49/11.62  tff(c_13989, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_454, c_13983])).
% 23.49/11.62  tff(c_13998, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_13989])).
% 23.49/11.62  tff(c_14007, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_13998])).
% 23.49/11.62  tff(c_14905, plain, (![C_935, B_936, A_937]: (v2_funct_2(C_935, B_936) | ~v3_funct_2(C_935, A_937, B_936) | ~v1_funct_1(C_935) | ~m1_subset_1(C_935, k1_zfmisc_1(k2_zfmisc_1(A_937, B_936))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.49/11.62  tff(c_14932, plain, (![C_942]: (v2_funct_2(C_942, '#skF_1') | ~v3_funct_2(C_942, '#skF_1', '#skF_1') | ~v1_funct_1(C_942) | ~m1_subset_1(C_942, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_13817, c_14905])).
% 23.49/11.62  tff(c_14938, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_13825, c_14932])).
% 23.49/11.62  tff(c_14951, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_104, c_14938])).
% 23.49/11.62  tff(c_14953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14007, c_14951])).
% 23.49/11.62  tff(c_14954, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_13998])).
% 23.49/11.62  tff(c_94, plain, (![B_55, A_54]: (m1_subset_1(B_55, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_55), A_54))) | ~r1_tarski(k2_relat_1(B_55), A_54) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_205])).
% 23.49/11.62  tff(c_16269, plain, (![A_54]: (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_54))) | ~r1_tarski(k2_relat_1('#skF_2'), A_54) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_16254, c_94])).
% 23.49/11.62  tff(c_16278, plain, (![A_54]: (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_54))) | ~r1_tarski('#skF_1', A_54))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_108, c_14954, c_16269])).
% 23.49/11.62  tff(c_16772, plain, (![A_1130, B_1131]: (k2_funct_2(A_1130, B_1131)=k2_funct_1(B_1131) | ~m1_subset_1(B_1131, k1_zfmisc_1(k2_zfmisc_1(A_1130, A_1130))) | ~v3_funct_2(B_1131, A_1130, A_1130) | ~v1_funct_2(B_1131, A_1130, A_1130) | ~v1_funct_1(B_1131))), inference(cnfTransformation, [status(thm)], [f_175])).
% 23.49/11.62  tff(c_16776, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_16278, c_16772])).
% 23.49/11.62  tff(c_16805, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_108, c_106, c_104, c_16776])).
% 23.49/11.62  tff(c_16616, plain, (![A_1117, B_1118]: (v1_funct_1(k2_funct_2(A_1117, B_1118)) | ~m1_subset_1(B_1118, k1_zfmisc_1(k2_zfmisc_1(A_1117, A_1117))) | ~v3_funct_2(B_1118, A_1117, A_1117) | ~v1_funct_2(B_1118, A_1117, A_1117) | ~v1_funct_1(B_1118))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.49/11.62  tff(c_16620, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_16278, c_16616])).
% 23.49/11.62  tff(c_16649, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_108, c_106, c_104, c_16620])).
% 23.49/11.62  tff(c_16810, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16805, c_16649])).
% 23.49/11.62  tff(c_17167, plain, (![A_1174, B_1175]: (v3_funct_2(k2_funct_2(A_1174, B_1175), A_1174, A_1174) | ~m1_subset_1(B_1175, k1_zfmisc_1(k2_zfmisc_1(A_1174, A_1174))) | ~v3_funct_2(B_1175, A_1174, A_1174) | ~v1_funct_2(B_1175, A_1174, A_1174) | ~v1_funct_1(B_1175))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.49/11.62  tff(c_17170, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_16278, c_17167])).
% 23.49/11.62  tff(c_17192, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_108, c_106, c_104, c_16805, c_17170])).
% 23.49/11.62  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.49/11.62  tff(c_15822, plain, (![A_7]: (v2_funct_1(A_7) | ~v3_funct_2(A_7, '#skF_1', '#skF_1') | ~v1_funct_1(A_7) | ~r1_tarski(A_7, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_15803])).
% 23.49/11.62  tff(c_17199, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_17192, c_15822])).
% 23.49/11.62  tff(c_17202, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16810, c_17199])).
% 23.49/11.62  tff(c_17203, plain, (~r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_17202])).
% 23.49/11.62  tff(c_17282, plain, (![A_1179, B_1180]: (m1_subset_1(k2_funct_2(A_1179, B_1180), k1_zfmisc_1(k2_zfmisc_1(A_1179, A_1179))) | ~m1_subset_1(B_1180, k1_zfmisc_1(k2_zfmisc_1(A_1179, A_1179))) | ~v3_funct_2(B_1180, A_1179, A_1179) | ~v1_funct_2(B_1180, A_1179, A_1179) | ~v1_funct_1(B_1180))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.49/11.62  tff(c_17332, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16805, c_17282])).
% 23.49/11.62  tff(c_17362, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_13825, c_13817, c_13817, c_17332])).
% 23.49/11.62  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.49/11.62  tff(c_17405, plain, (r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_17362, c_18])).
% 23.49/11.62  tff(c_17433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17203, c_17405])).
% 23.49/11.62  tff(c_17435, plain, (r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_17202])).
% 23.49/11.62  tff(c_17786, plain, (![A_1192, D_1190, B_1191, F_1193, E_1189, C_1194]: (k1_partfun1(A_1192, B_1191, C_1194, D_1190, E_1189, F_1193)=k5_relat_1(E_1189, F_1193) | ~m1_subset_1(F_1193, k1_zfmisc_1(k2_zfmisc_1(C_1194, D_1190))) | ~v1_funct_1(F_1193) | ~m1_subset_1(E_1189, k1_zfmisc_1(k2_zfmisc_1(A_1192, B_1191))) | ~v1_funct_1(E_1189))), inference(cnfTransformation, [status(thm)], [f_165])).
% 23.49/11.62  tff(c_26908, plain, (![E_1553, C_1554, D_1552, B_1557, A_1556, A_1555]: (k1_partfun1(A_1556, B_1557, C_1554, D_1552, E_1553, A_1555)=k5_relat_1(E_1553, A_1555) | ~v1_funct_1(A_1555) | ~m1_subset_1(E_1553, k1_zfmisc_1(k2_zfmisc_1(A_1556, B_1557))) | ~v1_funct_1(E_1553) | ~r1_tarski(A_1555, k2_zfmisc_1(C_1554, D_1552)))), inference(resolution, [status(thm)], [c_20, c_17786])).
% 23.49/11.62  tff(c_26979, plain, (![C_1558, D_1559, E_1560, A_1561]: (k1_partfun1('#skF_1', '#skF_1', C_1558, D_1559, E_1560, A_1561)=k5_relat_1(E_1560, A_1561) | ~v1_funct_1(A_1561) | ~m1_subset_1(E_1560, k1_zfmisc_1('#skF_2')) | ~v1_funct_1(E_1560) | ~r1_tarski(A_1561, k2_zfmisc_1(C_1558, D_1559)))), inference(superposition, [status(thm), theory('equality')], [c_13817, c_26908])).
% 23.49/11.62  tff(c_27001, plain, (![C_1558, D_1559, A_1561]: (k1_partfun1('#skF_1', '#skF_1', C_1558, D_1559, '#skF_2', A_1561)=k5_relat_1('#skF_2', A_1561) | ~v1_funct_1(A_1561) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_1561, k2_zfmisc_1(C_1558, D_1559)))), inference(resolution, [status(thm)], [c_13825, c_26979])).
% 23.49/11.62  tff(c_27076, plain, (![C_1565, D_1566, A_1567]: (k1_partfun1('#skF_1', '#skF_1', C_1565, D_1566, '#skF_2', A_1567)=k5_relat_1('#skF_2', A_1567) | ~v1_funct_1(A_1567) | ~r1_tarski(A_1567, k2_zfmisc_1(C_1565, D_1566)))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_27001])).
% 23.49/11.62  tff(c_27251, plain, (![A_1572]: (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', A_1572)=k5_relat_1('#skF_2', A_1572) | ~v1_funct_1(A_1572) | ~r1_tarski(A_1572, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13817, c_27076])).
% 23.49/11.62  tff(c_27278, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_17435, c_27251])).
% 23.49/11.62  tff(c_27314, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16810, c_27278])).
% 23.49/11.62  tff(c_16811, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16805, c_185])).
% 23.49/11.62  tff(c_27320, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_27314, c_16811])).
% 23.49/11.62  tff(c_27327, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_27320])).
% 23.49/11.62  tff(c_27333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_108, c_15821, c_16575, c_16254, c_27327])).
% 23.49/11.62  tff(c_27335, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_401])).
% 23.49/11.62  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.49/11.62  tff(c_173, plain, (![A_66]: (m1_subset_1(k6_partfun1(A_66), k1_zfmisc_1(k2_zfmisc_1(A_66, A_66))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 23.49/11.62  tff(c_177, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_173])).
% 23.49/11.62  tff(c_202, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_177, c_186])).
% 23.49/11.62  tff(c_237, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_202, c_231])).
% 23.49/11.62  tff(c_246, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_237])).
% 23.49/11.62  tff(c_271, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_246, c_111])).
% 23.49/11.62  tff(c_27344, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27335, c_27335, c_271])).
% 23.49/11.62  tff(c_27352, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27335, c_27335, c_14])).
% 23.49/11.62  tff(c_27397, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27352, c_13817])).
% 23.49/11.62  tff(c_367, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_320, c_24])).
% 23.49/11.62  tff(c_428, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_367])).
% 23.49/11.62  tff(c_27339, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27335, c_428])).
% 23.49/11.62  tff(c_27422, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27397, c_27339])).
% 23.49/11.62  tff(c_27435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27344, c_27422])).
% 23.49/11.62  tff(c_27436, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_367])).
% 23.49/11.62  tff(c_28538, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), '#skF_2') | '#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27436, c_27436, c_401])).
% 23.49/11.62  tff(c_28539, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_28538])).
% 23.49/11.62  tff(c_27477, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_27436, c_8])).
% 23.49/11.62  tff(c_28, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.49/11.62  tff(c_112, plain, (![A_13]: (k1_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_28])).
% 23.49/11.62  tff(c_26, plain, (![A_12]: (k1_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.49/11.62  tff(c_371, plain, (![A_85]: (k1_relat_1(k6_partfun1(A_85))!=k1_xboole_0 | k6_partfun1(A_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_368, c_26])).
% 23.49/11.62  tff(c_378, plain, (![A_85]: (k1_xboole_0!=A_85 | k6_partfun1(A_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_371])).
% 23.49/11.62  tff(c_27660, plain, (![A_1595]: (A_1595!='#skF_2' | k6_partfun1(A_1595)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27436, c_27436, c_378])).
% 23.49/11.62  tff(c_27674, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), '#skF_2') | '#skF_2'!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_27660, c_185])).
% 23.49/11.62  tff(c_27702, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_27674])).
% 23.49/11.62  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.49/11.62  tff(c_27474, plain, (![A_6]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_27436, c_16])).
% 23.49/11.62  tff(c_28200, plain, (![C_1666, B_1667, A_1668]: (v2_funct_2(C_1666, B_1667) | ~v3_funct_2(C_1666, A_1668, B_1667) | ~v1_funct_1(C_1666) | ~m1_subset_1(C_1666, k1_zfmisc_1(k2_zfmisc_1(A_1668, B_1667))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.49/11.62  tff(c_28210, plain, (![B_1667, A_1668]: (v2_funct_2('#skF_2', B_1667) | ~v3_funct_2('#skF_2', A_1668, B_1667) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_27474, c_28200])).
% 23.49/11.62  tff(c_28228, plain, (![B_1669, A_1670]: (v2_funct_2('#skF_2', B_1669) | ~v3_funct_2('#skF_2', A_1670, B_1669))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_28210])).
% 23.49/11.62  tff(c_28232, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_104, c_28228])).
% 23.49/11.62  tff(c_27437, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_367])).
% 23.49/11.62  tff(c_27487, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27436, c_27437])).
% 23.49/11.62  tff(c_27438, plain, (![C_1581, B_1582, A_1583]: (v5_relat_1(C_1581, B_1582) | ~m1_subset_1(C_1581, k1_zfmisc_1(k2_zfmisc_1(A_1583, B_1582))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.49/11.62  tff(c_27461, plain, (![B_1582]: (v5_relat_1(k1_xboole_0, B_1582))), inference(resolution, [status(thm)], [c_16, c_27438])).
% 23.49/11.62  tff(c_27483, plain, (![B_1582]: (v5_relat_1('#skF_2', B_1582))), inference(demodulation, [status(thm), theory('equality')], [c_27436, c_27461])).
% 23.49/11.62  tff(c_27720, plain, (![B_1598, A_1599]: (k2_relat_1(B_1598)=A_1599 | ~v2_funct_2(B_1598, A_1599) | ~v5_relat_1(B_1598, A_1599) | ~v1_relat_1(B_1598))), inference(cnfTransformation, [status(thm)], [f_135])).
% 23.49/11.62  tff(c_27726, plain, (![B_1582]: (k2_relat_1('#skF_2')=B_1582 | ~v2_funct_2('#skF_2', B_1582) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_27483, c_27720])).
% 23.49/11.62  tff(c_27732, plain, (![B_1582]: (B_1582='#skF_2' | ~v2_funct_2('#skF_2', B_1582))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_27487, c_27726])).
% 23.49/11.62  tff(c_28235, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_28232, c_27732])).
% 23.49/11.62  tff(c_28239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27702, c_28235])).
% 23.49/11.62  tff(c_28241, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_27674])).
% 23.49/11.62  tff(c_27476, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27436, c_27436, c_12])).
% 23.49/11.62  tff(c_28243, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28241, c_28241, c_27476])).
% 23.49/11.62  tff(c_27523, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_243])).
% 23.49/11.62  tff(c_28535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_28243, c_28241, c_27523])).
% 23.49/11.62  tff(c_28536, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_243])).
% 23.49/11.62  tff(c_204, plain, (![A_41]: (r1_tarski(k6_partfun1(A_41), k2_zfmisc_1(A_41, A_41)))), inference(resolution, [status(thm)], [c_80, c_186])).
% 23.49/11.62  tff(c_28553, plain, (r1_tarski(k6_partfun1('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28536, c_204])).
% 23.49/11.62  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.49/11.62  tff(c_28693, plain, (k6_partfun1('#skF_1')='#skF_2' | ~r1_tarski('#skF_2', k6_partfun1('#skF_1'))), inference(resolution, [status(thm)], [c_28553, c_2])).
% 23.49/11.62  tff(c_28696, plain, (k6_partfun1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27477, c_28693])).
% 23.49/11.62  tff(c_28723, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_28696, c_111])).
% 23.49/11.62  tff(c_28732, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28723, c_27487])).
% 23.49/11.62  tff(c_28734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28539, c_28732])).
% 23.49/11.62  tff(c_28736, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_28538])).
% 23.49/11.62  tff(c_28853, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_28736, c_27474])).
% 23.49/11.62  tff(c_29790, plain, (![A_1817, B_1818, C_1819, D_1820]: (r2_relset_1(A_1817, B_1818, C_1819, C_1819) | ~m1_subset_1(D_1820, k1_zfmisc_1(k2_zfmisc_1(A_1817, B_1818))) | ~m1_subset_1(C_1819, k1_zfmisc_1(k2_zfmisc_1(A_1817, B_1818))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 23.49/11.62  tff(c_30510, plain, (![A_4139, B_4140, C_4141]: (r2_relset_1(A_4139, B_4140, C_4141, C_4141) | ~m1_subset_1(C_4141, k1_zfmisc_1(k2_zfmisc_1(A_4139, B_4140))))), inference(resolution, [status(thm)], [c_28853, c_29790])).
% 23.49/11.62  tff(c_30526, plain, (![A_4139, B_4140]: (r2_relset_1(A_4139, B_4140, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_28853, c_30510])).
% 23.49/11.62  tff(c_28760, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28736, c_108])).
% 23.49/11.62  tff(c_28755, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28736, c_320])).
% 23.49/11.62  tff(c_29431, plain, (![C_1768, A_1769, B_1770]: (v2_funct_1(C_1768) | ~v3_funct_2(C_1768, A_1769, B_1770) | ~v1_funct_1(C_1768) | ~m1_subset_1(C_1768, k1_zfmisc_1(k2_zfmisc_1(A_1769, B_1770))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.49/11.62  tff(c_29438, plain, (![A_1769, B_1770]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_1769, B_1770) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_28853, c_29431])).
% 23.49/11.62  tff(c_29451, plain, (![A_1769, B_1770]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_1769, B_1770))), inference(demodulation, [status(thm), theory('equality')], [c_28760, c_29438])).
% 23.49/11.62  tff(c_29454, plain, (![A_1769, B_1770]: (~v3_funct_2('#skF_1', A_1769, B_1770))), inference(splitLeft, [status(thm)], [c_29451])).
% 23.49/11.62  tff(c_28758, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28736, c_104])).
% 23.49/11.62  tff(c_29456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29454, c_28758])).
% 23.49/11.62  tff(c_29457, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_29451])).
% 23.49/11.62  tff(c_28754, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28736, c_27436])).
% 23.49/11.62  tff(c_28982, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28754, c_28754, c_378])).
% 23.49/11.62  tff(c_268, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_246, c_112])).
% 23.49/11.62  tff(c_27468, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27436, c_27436, c_268])).
% 23.49/11.62  tff(c_28747, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28736, c_28736, c_27468])).
% 23.49/11.62  tff(c_28913, plain, (![A_1706, B_1707, C_1708]: (k1_relset_1(A_1706, B_1707, C_1708)=k1_relat_1(C_1708) | ~m1_subset_1(C_1708, k1_zfmisc_1(k2_zfmisc_1(A_1706, B_1707))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 23.49/11.62  tff(c_28920, plain, (![A_1706, B_1707]: (k1_relset_1(A_1706, B_1707, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_28853, c_28913])).
% 23.49/11.62  tff(c_28932, plain, (![A_1706, B_1707]: (k1_relset_1(A_1706, B_1707, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28747, c_28920])).
% 23.49/11.62  tff(c_58, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 23.49/11.62  tff(c_116, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_58])).
% 23.49/11.62  tff(c_29212, plain, (![C_1740, B_1741]: (v1_funct_2(C_1740, '#skF_1', B_1741) | k1_relset_1('#skF_1', B_1741, C_1740)!='#skF_1' | ~m1_subset_1(C_1740, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28754, c_28754, c_28754, c_28754, c_116])).
% 23.49/11.62  tff(c_29215, plain, (![B_1741]: (v1_funct_2('#skF_1', '#skF_1', B_1741) | k1_relset_1('#skF_1', B_1741, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_28853, c_29212])).
% 23.49/11.62  tff(c_29221, plain, (![B_1741]: (v1_funct_2('#skF_1', '#skF_1', B_1741))), inference(demodulation, [status(thm), theory('equality')], [c_28932, c_29215])).
% 23.49/11.62  tff(c_28881, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28736, c_28736, c_27476])).
% 23.49/11.62  tff(c_29934, plain, (![A_1836, B_1837]: (k2_funct_2(A_1836, B_1837)=k2_funct_1(B_1837) | ~m1_subset_1(B_1837, k1_zfmisc_1(k2_zfmisc_1(A_1836, A_1836))) | ~v3_funct_2(B_1837, A_1836, A_1836) | ~v1_funct_2(B_1837, A_1836, A_1836) | ~v1_funct_1(B_1837))), inference(cnfTransformation, [status(thm)], [f_175])).
% 23.49/11.62  tff(c_29946, plain, (![A_1836]: (k2_funct_2(A_1836, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_1836, A_1836) | ~v1_funct_2('#skF_1', A_1836, A_1836) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_28853, c_29934])).
% 23.49/11.62  tff(c_31681, plain, (![A_4251]: (k2_funct_2(A_4251, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_4251, A_4251) | ~v1_funct_2('#skF_1', A_4251, A_4251))), inference(demodulation, [status(thm), theory('equality')], [c_28760, c_29946])).
% 23.49/11.62  tff(c_31684, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_28758, c_31681])).
% 23.49/11.62  tff(c_31687, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29221, c_31684])).
% 23.49/11.62  tff(c_31694, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31687, c_70])).
% 23.49/11.62  tff(c_31698, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28760, c_29221, c_28758, c_28853, c_28881, c_28881, c_31694])).
% 23.49/11.62  tff(c_31754, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_31698, c_18])).
% 23.49/11.62  tff(c_251, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_231])).
% 23.49/11.62  tff(c_27466, plain, (![A_3]: (A_3='#skF_2' | ~r1_tarski(A_3, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_27436, c_27436, c_251])).
% 23.49/11.62  tff(c_29025, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28736, c_28736, c_27466])).
% 23.49/11.62  tff(c_31800, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_31754, c_29025])).
% 23.49/11.62  tff(c_31826, plain, (k6_partfun1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31800, c_109])).
% 23.49/11.62  tff(c_31835, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28755, c_28760, c_29457, c_28982, c_28747, c_31826])).
% 23.49/11.62  tff(c_30633, plain, (![B_4156, D_4155, F_4158, C_4159, A_4157, E_4154]: (k1_partfun1(A_4157, B_4156, C_4159, D_4155, E_4154, F_4158)=k5_relat_1(E_4154, F_4158) | ~m1_subset_1(F_4158, k1_zfmisc_1(k2_zfmisc_1(C_4159, D_4155))) | ~v1_funct_1(F_4158) | ~m1_subset_1(E_4154, k1_zfmisc_1(k2_zfmisc_1(A_4157, B_4156))) | ~v1_funct_1(E_4154))), inference(cnfTransformation, [status(thm)], [f_165])).
% 23.49/11.62  tff(c_30642, plain, (![B_4156, D_4155, C_4159, A_4157, E_4154]: (k1_partfun1(A_4157, B_4156, C_4159, D_4155, E_4154, '#skF_1')=k5_relat_1(E_4154, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_4154, k1_zfmisc_1(k2_zfmisc_1(A_4157, B_4156))) | ~v1_funct_1(E_4154))), inference(resolution, [status(thm)], [c_28853, c_30633])).
% 23.49/11.62  tff(c_33039, plain, (![B_4369, E_4370, A_4372, D_4371, C_4368]: (k1_partfun1(A_4372, B_4369, C_4368, D_4371, E_4370, '#skF_1')=k5_relat_1(E_4370, '#skF_1') | ~m1_subset_1(E_4370, k1_zfmisc_1(k2_zfmisc_1(A_4372, B_4369))) | ~v1_funct_1(E_4370))), inference(demodulation, [status(thm), theory('equality')], [c_28760, c_30642])).
% 23.49/11.62  tff(c_33052, plain, (![A_4372, B_4369, C_4368, D_4371]: (k1_partfun1(A_4372, B_4369, C_4368, D_4371, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_28853, c_33039])).
% 23.49/11.62  tff(c_33066, plain, (![A_4372, B_4369, C_4368, D_4371]: (k1_partfun1(A_4372, B_4369, C_4368, D_4371, '#skF_1', '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28760, c_31835, c_33052])).
% 23.49/11.62  tff(c_28756, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28736, c_28736, c_185])).
% 23.49/11.62  tff(c_29113, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28982, c_28756])).
% 23.49/11.62  tff(c_31689, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31687, c_29113])).
% 23.49/11.62  tff(c_31806, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31800, c_31689])).
% 23.49/11.62  tff(c_33069, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33066, c_31806])).
% 23.49/11.62  tff(c_33072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30526, c_33069])).
% 23.49/11.62  tff(c_33073, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_100])).
% 23.49/11.62  tff(c_35586, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_35583, c_33073])).
% 23.49/11.62  tff(c_37561, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_37428, c_35586])).
% 23.49/11.62  tff(c_37568, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_110, c_37561])).
% 23.49/11.62  tff(c_37574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33131, c_108, c_34543, c_35383, c_34215, c_37568])).
% 23.49/11.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.49/11.62  
% 23.49/11.62  Inference rules
% 23.49/11.62  ----------------------
% 23.49/11.62  #Ref     : 3
% 23.49/11.62  #Sup     : 7741
% 23.49/11.62  #Fact    : 0
% 23.49/11.62  #Define  : 0
% 23.49/11.62  #Split   : 80
% 23.49/11.62  #Chain   : 0
% 23.49/11.62  #Close   : 0
% 23.49/11.62  
% 23.49/11.62  Ordering : KBO
% 23.49/11.62  
% 23.49/11.62  Simplification rules
% 23.49/11.62  ----------------------
% 23.49/11.62  #Subsume      : 1664
% 23.49/11.62  #Demod        : 12611
% 23.49/11.62  #Tautology    : 3066
% 23.49/11.62  #SimpNegUnit  : 119
% 23.49/11.62  #BackRed      : 226
% 23.49/11.62  
% 23.49/11.62  #Partial instantiations: 0
% 23.49/11.62  #Strategies tried      : 1
% 23.49/11.62  
% 23.49/11.62  Timing (in seconds)
% 23.49/11.62  ----------------------
% 23.49/11.63  Preprocessing        : 0.64
% 23.49/11.63  Parsing              : 0.34
% 23.49/11.63  CNF conversion       : 0.04
% 23.49/11.63  Main loop            : 10.12
% 23.49/11.63  Inferencing          : 2.99
% 23.49/11.63  Reduction            : 4.23
% 23.49/11.63  Demodulation         : 3.30
% 23.49/11.63  BG Simplification    : 0.18
% 23.49/11.63  Subsumption          : 2.10
% 23.49/11.63  Abstraction          : 0.27
% 23.49/11.63  MUC search           : 0.00
% 23.49/11.63  Cooper               : 0.00
% 23.49/11.63  Total                : 10.87
% 23.49/11.63  Index Insertion      : 0.00
% 23.49/11.63  Index Deletion       : 0.00
% 23.49/11.63  Index Matching       : 0.00
% 23.49/11.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------

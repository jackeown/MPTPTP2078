%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:03 EST 2020

% Result     : Theorem 7.40s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  264 (25601 expanded)
%              Number of leaves         :   48 (8046 expanded)
%              Depth                    :   24
%              Number of atoms          :  539 (55078 expanded)
%              Number of equality atoms :  156 (23887 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_171,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_158,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_146,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_5399,plain,(
    ! [C_560,A_561,B_562] :
      ( v1_relat_1(C_560)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(A_561,B_562))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5413,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_5399])).

tff(c_84,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_80,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_6166,plain,(
    ! [C_675,A_676,B_677] :
      ( v2_funct_1(C_675)
      | ~ v3_funct_2(C_675,A_676,B_677)
      | ~ v1_funct_1(C_675)
      | ~ m1_subset_1(C_675,k1_zfmisc_1(k2_zfmisc_1(A_676,B_677))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6179,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_6166])).

tff(c_6187,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_6179])).

tff(c_74,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_38,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_85,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_38])).

tff(c_5946,plain,(
    ! [A_640,B_641,D_642] :
      ( r2_relset_1(A_640,B_641,D_642,D_642)
      | ~ m1_subset_1(D_642,k1_zfmisc_1(k2_zfmisc_1(A_640,B_641))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5957,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_85,c_5946])).

tff(c_5444,plain,(
    ! [C_566,B_567,A_568] :
      ( v5_relat_1(C_566,B_567)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(k2_zfmisc_1(A_568,B_567))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5457,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_5444])).

tff(c_5553,plain,(
    ! [B_584,A_585] :
      ( k2_relat_1(B_584) = A_585
      | ~ v2_funct_2(B_584,A_585)
      | ~ v5_relat_1(B_584,A_585)
      | ~ v1_relat_1(B_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5562,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5457,c_5553])).

tff(c_5571,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5413,c_5562])).

tff(c_5577,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5571])).

tff(c_5911,plain,(
    ! [C_637,B_638,A_639] :
      ( v2_funct_2(C_637,B_638)
      | ~ v3_funct_2(C_637,A_639,B_638)
      | ~ v1_funct_1(C_637)
      | ~ m1_subset_1(C_637,k1_zfmisc_1(k2_zfmisc_1(A_639,B_638))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5924,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_5911])).

tff(c_5931,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_5924])).

tff(c_5933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5577,c_5931])).

tff(c_5934,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5571])).

tff(c_22,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_87,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22])).

tff(c_82,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_6517,plain,(
    ! [A_724,B_725] :
      ( k2_funct_2(A_724,B_725) = k2_funct_1(B_725)
      | ~ m1_subset_1(B_725,k1_zfmisc_1(k2_zfmisc_1(A_724,A_724)))
      | ~ v3_funct_2(B_725,A_724,A_724)
      | ~ v1_funct_2(B_725,A_724,A_724)
      | ~ v1_funct_1(B_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_6530,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_6517])).

tff(c_6536,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_6530])).

tff(c_6461,plain,(
    ! [A_717,B_718] :
      ( v1_funct_1(k2_funct_2(A_717,B_718))
      | ~ m1_subset_1(B_718,k1_zfmisc_1(k2_zfmisc_1(A_717,A_717)))
      | ~ v3_funct_2(B_718,A_717,A_717)
      | ~ v1_funct_2(B_718,A_717,A_717)
      | ~ v1_funct_1(B_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6474,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_6461])).

tff(c_6480,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_6474])).

tff(c_6555,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6536,c_6480])).

tff(c_62,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_funct_2(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v3_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6872,plain,(
    ! [C_746,F_745,E_743,D_748,A_747,B_744] :
      ( k1_partfun1(A_747,B_744,C_746,D_748,E_743,F_745) = k5_relat_1(E_743,F_745)
      | ~ m1_subset_1(F_745,k1_zfmisc_1(k2_zfmisc_1(C_746,D_748)))
      | ~ v1_funct_1(F_745)
      | ~ m1_subset_1(E_743,k1_zfmisc_1(k2_zfmisc_1(A_747,B_744)))
      | ~ v1_funct_1(E_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_6885,plain,(
    ! [A_747,B_744,E_743] :
      ( k1_partfun1(A_747,B_744,'#skF_1','#skF_1',E_743,'#skF_2') = k5_relat_1(E_743,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_743,k1_zfmisc_1(k2_zfmisc_1(A_747,B_744)))
      | ~ v1_funct_1(E_743) ) ),
    inference(resolution,[status(thm)],[c_78,c_6872])).

tff(c_6920,plain,(
    ! [A_749,B_750,E_751] :
      ( k1_partfun1(A_749,B_750,'#skF_1','#skF_1',E_751,'#skF_2') = k5_relat_1(E_751,'#skF_2')
      | ~ m1_subset_1(E_751,k1_zfmisc_1(k2_zfmisc_1(A_749,B_750)))
      | ~ v1_funct_1(E_751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6885])).

tff(c_7399,plain,(
    ! [A_764,B_765] :
      ( k1_partfun1(A_764,A_764,'#skF_1','#skF_1',k2_funct_2(A_764,B_765),'#skF_2') = k5_relat_1(k2_funct_2(A_764,B_765),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_764,B_765))
      | ~ m1_subset_1(B_765,k1_zfmisc_1(k2_zfmisc_1(A_764,A_764)))
      | ~ v3_funct_2(B_765,A_764,A_764)
      | ~ v1_funct_2(B_765,A_764,A_764)
      | ~ v1_funct_1(B_765) ) ),
    inference(resolution,[status(thm)],[c_62,c_6920])).

tff(c_7414,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_7399])).

tff(c_7427,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_6555,c_6536,c_6536,c_6536,c_7414])).

tff(c_225,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_239,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_225])).

tff(c_1008,plain,(
    ! [C_169,A_170,B_171] :
      ( v2_funct_1(C_169)
      | ~ v3_funct_2(C_169,A_170,B_171)
      | ~ v1_funct_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1021,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1008])).

tff(c_1029,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_1021])).

tff(c_782,plain,(
    ! [A_134,B_135,D_136] :
      ( r2_relset_1(A_134,B_135,D_136,D_136)
      | ~ m1_subset_1(D_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_793,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_85,c_782])).

tff(c_12,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_5] : k1_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12])).

tff(c_18,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,(
    ! [A_6] : v1_relat_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18])).

tff(c_155,plain,(
    ! [A_47] :
      ( k1_relat_1(A_47) != k1_xboole_0
      | k1_xboole_0 = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,(
    ! [A_6] :
      ( k1_relat_1(k6_partfun1(A_6)) != k1_xboole_0
      | k6_partfun1(A_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_89,c_155])).

tff(c_167,plain,(
    ! [A_6] :
      ( k1_xboole_0 != A_6
      | k6_partfun1(A_6) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_161])).

tff(c_76,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_193,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_251,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_193])).

tff(c_311,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_858,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_relset_1(A_147,B_148,C_149) = k1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_877,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_858])).

tff(c_1193,plain,(
    ! [B_195,A_196,C_197] :
      ( k1_xboole_0 = B_195
      | k1_relset_1(A_196,B_195,C_197) = A_196
      | ~ v1_funct_2(C_197,A_196,B_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1206,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_1193])).

tff(c_1214,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_877,c_1206])).

tff(c_1215,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_1214])).

tff(c_24,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_86,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_24])).

tff(c_1333,plain,(
    ! [A_215,B_216] :
      ( k2_funct_2(A_215,B_216) = k2_funct_1(B_216)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(k2_zfmisc_1(A_215,A_215)))
      | ~ v3_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1346,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1333])).

tff(c_1352,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1346])).

tff(c_1313,plain,(
    ! [A_213,B_214] :
      ( v1_funct_1(k2_funct_2(A_213,B_214))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k2_zfmisc_1(A_213,A_213)))
      | ~ v3_funct_2(B_214,A_213,A_213)
      | ~ v1_funct_2(B_214,A_213,A_213)
      | ~ v1_funct_1(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1326,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1313])).

tff(c_1332,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1326])).

tff(c_1353,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_1332])).

tff(c_1465,plain,(
    ! [A_235,B_236] :
      ( m1_subset_1(k2_funct_2(A_235,B_236),k1_zfmisc_1(k2_zfmisc_1(A_235,A_235)))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k2_zfmisc_1(A_235,A_235)))
      | ~ v3_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_1(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,B_3)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1537,plain,(
    ! [A_235,B_236] :
      ( r1_tarski(k2_funct_2(A_235,B_236),k2_zfmisc_1(A_235,A_235))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k2_zfmisc_1(A_235,A_235)))
      | ~ v3_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_1(B_236) ) ),
    inference(resolution,[status(thm)],[c_1465,c_4])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1689,plain,(
    ! [D_242,A_241,B_238,F_239,E_237,C_240] :
      ( k1_partfun1(A_241,B_238,C_240,D_242,E_237,F_239) = k5_relat_1(E_237,F_239)
      | ~ m1_subset_1(F_239,k1_zfmisc_1(k2_zfmisc_1(C_240,D_242)))
      | ~ v1_funct_1(F_239)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_241,B_238)))
      | ~ v1_funct_1(E_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2339,plain,(
    ! [A_268,E_266,D_264,A_267,B_269,C_265] :
      ( k1_partfun1(A_267,B_269,C_265,D_264,E_266,A_268) = k5_relat_1(E_266,A_268)
      | ~ v1_funct_1(A_268)
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_269)))
      | ~ v1_funct_1(E_266)
      | ~ r1_tarski(A_268,k2_zfmisc_1(C_265,D_264)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1689])).

tff(c_2354,plain,(
    ! [C_265,D_264,A_268] :
      ( k1_partfun1('#skF_1','#skF_1',C_265,D_264,'#skF_2',A_268) = k5_relat_1('#skF_2',A_268)
      | ~ v1_funct_1(A_268)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_268,k2_zfmisc_1(C_265,D_264)) ) ),
    inference(resolution,[status(thm)],[c_78,c_2339])).

tff(c_2488,plain,(
    ! [C_270,D_271,A_272] :
      ( k1_partfun1('#skF_1','#skF_1',C_270,D_271,'#skF_2',A_272) = k5_relat_1('#skF_2',A_272)
      | ~ v1_funct_1(A_272)
      | ~ r1_tarski(A_272,k2_zfmisc_1(C_270,D_271)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2354])).

tff(c_2685,plain,(
    ! [A_278,B_279] :
      ( k1_partfun1('#skF_1','#skF_1',A_278,A_278,'#skF_2',k2_funct_2(A_278,B_279)) = k5_relat_1('#skF_2',k2_funct_2(A_278,B_279))
      | ~ v1_funct_1(k2_funct_2(A_278,B_279))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(k2_zfmisc_1(A_278,A_278)))
      | ~ v3_funct_2(B_279,A_278,A_278)
      | ~ v1_funct_2(B_279,A_278,A_278)
      | ~ v1_funct_1(B_279) ) ),
    inference(resolution,[status(thm)],[c_1537,c_2488])).

tff(c_2702,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2685])).

tff(c_2718,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1353,c_1352,c_1352,c_1352,c_2702])).

tff(c_1354,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_193])).

tff(c_2760,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2718,c_1354])).

tff(c_2767,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_2760])).

tff(c_2773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_84,c_1029,c_793,c_1215,c_2767])).

tff(c_2775,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_relat_1(A_4) != k1_xboole_0
      | k1_xboole_0 = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_239,c_10])).

tff(c_252,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_2778,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_252])).

tff(c_3002,plain,(
    ! [A_298,B_299,C_300] :
      ( k1_relset_1(A_298,B_299,C_300) = k1_relat_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3021,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_3002])).

tff(c_54,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3330,plain,(
    ! [B_335,C_336] :
      ( k1_relset_1('#skF_1',B_335,C_336) = '#skF_1'
      | ~ v1_funct_2(C_336,'#skF_1',B_335)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_335))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_2775,c_2775,c_2775,c_54])).

tff(c_3345,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_3330])).

tff(c_3355,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3021,c_3345])).

tff(c_3357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2778,c_3355])).

tff(c_3358,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_99,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_105,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_16])).

tff(c_14,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_123,plain,(
    ! [A_45] : k2_relat_1(k6_partfun1(A_45)) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_132,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_123])).

tff(c_3365,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3358,c_3358,c_132])).

tff(c_8,plain,(
    ! [A_4] :
      ( k2_relat_1(A_4) != k1_xboole_0
      | k1_xboole_0 = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_246,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_239,c_8])).

tff(c_248,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_3360,plain,(
    k2_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3358,c_248])).

tff(c_3414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3365,c_3360])).

tff(c_3415,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_3497,plain,(
    ! [A_346] :
      ( A_346 != '#skF_2'
      | k6_partfun1(A_346) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_3415,c_167])).

tff(c_3506,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3497,c_193])).

tff(c_3552,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3506])).

tff(c_3416,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_3431,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_3416])).

tff(c_3532,plain,(
    ! [C_348,B_349,A_350] :
      ( v5_relat_1(C_348,B_349)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(A_350,B_349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3545,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_3532])).

tff(c_3663,plain,(
    ! [B_366,A_367] :
      ( k2_relat_1(B_366) = A_367
      | ~ v2_funct_2(B_366,A_367)
      | ~ v5_relat_1(B_366,A_367)
      | ~ v1_relat_1(B_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3672,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3545,c_3663])).

tff(c_3681,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_3431,c_3672])).

tff(c_3682,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3552,c_3681])).

tff(c_4041,plain,(
    ! [C_417,B_418,A_419] :
      ( v2_funct_2(C_417,B_418)
      | ~ v3_funct_2(C_417,A_419,B_418)
      | ~ v1_funct_1(C_417)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_419,B_418))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4054,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_4041])).

tff(c_4063,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_4054])).

tff(c_4065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3682,c_4063])).

tff(c_4067,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3506])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3424,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_2])).

tff(c_4072,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_3424])).

tff(c_4255,plain,(
    ! [A_430,B_431,D_432] :
      ( r2_relset_1(A_430,B_431,D_432,D_432)
      | ~ m1_subset_1(D_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4494,plain,(
    ! [A_462,B_463,A_464] :
      ( r2_relset_1(A_462,B_463,A_464,A_464)
      | ~ r1_tarski(A_464,k2_zfmisc_1(A_462,B_463)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4255])).

tff(c_4502,plain,(
    ! [A_462,B_463] : r2_relset_1(A_462,B_463,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4072,c_4494])).

tff(c_4084,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_84])).

tff(c_4080,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_239])).

tff(c_20,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_20])).

tff(c_118,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_88])).

tff(c_3422,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_118])).

tff(c_4077,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_3422])).

tff(c_3418,plain,(
    ! [A_6] :
      ( A_6 != '#skF_2'
      | k6_partfun1(A_6) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_3415,c_167])).

tff(c_4210,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_4067,c_3418])).

tff(c_139,plain,(
    ! [A_46] : k1_relat_1(k6_partfun1(A_46)) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12])).

tff(c_148,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_139])).

tff(c_3420,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_3415,c_148])).

tff(c_4074,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_4067,c_3420])).

tff(c_4407,plain,(
    ! [A_452,B_453,C_454] :
      ( k1_relset_1(A_452,B_453,C_454) = k1_relat_1(C_454)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4514,plain,(
    ! [A_468,B_469,A_470] :
      ( k1_relset_1(A_468,B_469,A_470) = k1_relat_1(A_470)
      | ~ r1_tarski(A_470,k2_zfmisc_1(A_468,B_469)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4407])).

tff(c_4521,plain,(
    ! [A_468,B_469] : k1_relset_1(A_468,B_469,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4072,c_4514])).

tff(c_4525,plain,(
    ! [A_468,B_469] : k1_relset_1(A_468,B_469,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4074,c_4521])).

tff(c_4079,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_3415])).

tff(c_50,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4625,plain,(
    ! [C_486,B_487] :
      ( v1_funct_2(C_486,'#skF_1',B_487)
      | k1_relset_1('#skF_1',B_487,C_486) != '#skF_1'
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_487))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4079,c_4079,c_4079,c_4079,c_50])).

tff(c_4681,plain,(
    ! [A_496,B_497] :
      ( v1_funct_2(A_496,'#skF_1',B_497)
      | k1_relset_1('#skF_1',B_497,A_496) != '#skF_1'
      | ~ r1_tarski(A_496,k2_zfmisc_1('#skF_1',B_497)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4625])).

tff(c_4689,plain,(
    ! [B_497] :
      ( v1_funct_2('#skF_1','#skF_1',B_497)
      | k1_relset_1('#skF_1',B_497,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_4072,c_4681])).

tff(c_4695,plain,(
    ! [B_497] : v1_funct_2('#skF_1','#skF_1',B_497) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4525,c_4689])).

tff(c_4082,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_80])).

tff(c_217,plain,(
    ! [A_54] : m1_subset_1(k6_partfun1(A_54),k1_zfmisc_1(k2_zfmisc_1(A_54,A_54))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_38])).

tff(c_223,plain,(
    ! [A_6] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_6,A_6)))
      | k1_xboole_0 != A_6 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_217])).

tff(c_4376,plain,(
    ! [A_6] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_6,A_6)))
      | A_6 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4079,c_4079,c_223])).

tff(c_4816,plain,(
    ! [A_522,B_523] :
      ( k2_funct_2(A_522,B_523) = k2_funct_1(B_523)
      | ~ m1_subset_1(B_523,k1_zfmisc_1(k2_zfmisc_1(A_522,A_522)))
      | ~ v3_funct_2(B_523,A_522,A_522)
      | ~ v1_funct_2(B_523,A_522,A_522)
      | ~ v1_funct_1(B_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4819,plain,(
    ! [A_6] :
      ( k2_funct_2(A_6,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_6,A_6)
      | ~ v1_funct_2('#skF_1',A_6,A_6)
      | ~ v1_funct_1('#skF_1')
      | A_6 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_4376,c_4816])).

tff(c_4840,plain,(
    ! [A_525] :
      ( k2_funct_2(A_525,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_525,A_525)
      | ~ v1_funct_2('#skF_1',A_525,A_525)
      | A_525 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4084,c_4819])).

tff(c_4843,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4082,c_4840])).

tff(c_4846,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4695,c_4843])).

tff(c_4874,plain,(
    ! [A_529,B_530] :
      ( v1_funct_2(k2_funct_2(A_529,B_530),A_529,A_529)
      | ~ m1_subset_1(B_530,k1_zfmisc_1(k2_zfmisc_1(A_529,A_529)))
      | ~ v3_funct_2(B_530,A_529,A_529)
      | ~ v1_funct_2(B_530,A_529,A_529)
      | ~ v1_funct_1(B_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4876,plain,(
    ! [A_6] :
      ( v1_funct_2(k2_funct_2(A_6,'#skF_1'),A_6,A_6)
      | ~ v3_funct_2('#skF_1',A_6,A_6)
      | ~ v1_funct_2('#skF_1',A_6,A_6)
      | ~ v1_funct_1('#skF_1')
      | A_6 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_4376,c_4874])).

tff(c_4888,plain,(
    ! [A_531] :
      ( v1_funct_2(k2_funct_2(A_531,'#skF_1'),A_531,A_531)
      | ~ v3_funct_2('#skF_1',A_531,A_531)
      | ~ v1_funct_2('#skF_1',A_531,A_531)
      | A_531 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4084,c_4876])).

tff(c_4891,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4846,c_4888])).

tff(c_4894,plain,(
    v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4695,c_4082,c_4891])).

tff(c_4377,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4079,c_4079,c_223])).

tff(c_4916,plain,(
    ! [A_536,B_537] :
      ( m1_subset_1(k2_funct_2(A_536,B_537),k1_zfmisc_1(k2_zfmisc_1(A_536,A_536)))
      | ~ m1_subset_1(B_537,k1_zfmisc_1(k2_zfmisc_1(A_536,A_536)))
      | ~ v3_funct_2(B_537,A_536,A_536)
      | ~ v1_funct_2(B_537,A_536,A_536)
      | ~ v1_funct_1(B_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4970,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4846,c_4916])).

tff(c_4990,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4084,c_4695,c_4082,c_4377,c_4970])).

tff(c_4589,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1('#skF_1',B_26,C_27) = '#skF_1'
      | ~ v1_funct_2(C_27,'#skF_1',B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_26))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4079,c_4079,c_4079,c_4079,c_54])).

tff(c_5015,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4990,c_4589])).

tff(c_5065,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4894,c_5015])).

tff(c_5078,plain,(
    r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4990,c_4])).

tff(c_4422,plain,(
    ! [A_452,B_453,A_2] :
      ( k1_relset_1(A_452,B_453,A_2) = k1_relat_1(A_2)
      | ~ r1_tarski(A_2,k2_zfmisc_1(A_452,B_453)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4407])).

tff(c_5123,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_5078,c_4422])).

tff(c_5163,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5065,c_5123])).

tff(c_26,plain,(
    ! [C_10,A_8,B_9] :
      ( v1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5077,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4990,c_26])).

tff(c_3419,plain,(
    ! [A_4] :
      ( k1_relat_1(A_4) != '#skF_2'
      | A_4 = '#skF_2'
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_3415,c_10])).

tff(c_4302,plain,(
    ! [A_4] :
      ( k1_relat_1(A_4) != '#skF_1'
      | A_4 = '#skF_1'
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_4067,c_3419])).

tff(c_5085,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5077,c_4302])).

tff(c_5215,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5163,c_5085])).

tff(c_5258,plain,
    ( k6_partfun1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5215,c_86])).

tff(c_5264,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4080,c_4084,c_4077,c_4210,c_4074,c_5258])).

tff(c_4800,plain,(
    ! [A_520,B_521] :
      ( v1_funct_1(k2_funct_2(A_520,B_521))
      | ~ m1_subset_1(B_521,k1_zfmisc_1(k2_zfmisc_1(A_520,A_520)))
      | ~ v3_funct_2(B_521,A_520,A_520)
      | ~ v1_funct_2(B_521,A_520,A_520)
      | ~ v1_funct_1(B_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4803,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_2(A_6,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_6,A_6)
      | ~ v1_funct_2('#skF_1',A_6,A_6)
      | ~ v1_funct_1('#skF_1')
      | A_6 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_4376,c_4800])).

tff(c_4833,plain,(
    ! [A_524] :
      ( v1_funct_1(k2_funct_2(A_524,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_524,A_524)
      | ~ v1_funct_2('#skF_1',A_524,A_524)
      | A_524 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4084,c_4803])).

tff(c_4835,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4082,c_4833])).

tff(c_4838,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4695,c_4835])).

tff(c_4847,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4846,c_4838])).

tff(c_5171,plain,(
    ! [F_540,D_543,E_538,C_541,B_539,A_542] :
      ( k1_partfun1(A_542,B_539,C_541,D_543,E_538,F_540) = k5_relat_1(E_538,F_540)
      | ~ m1_subset_1(F_540,k1_zfmisc_1(k2_zfmisc_1(C_541,D_543)))
      | ~ v1_funct_1(F_540)
      | ~ m1_subset_1(E_538,k1_zfmisc_1(k2_zfmisc_1(A_542,B_539)))
      | ~ v1_funct_1(E_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5173,plain,(
    ! [A_542,B_539,E_538] :
      ( k1_partfun1(A_542,B_539,'#skF_1','#skF_1',E_538,k2_funct_1('#skF_1')) = k5_relat_1(E_538,k2_funct_1('#skF_1'))
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_538,k1_zfmisc_1(k2_zfmisc_1(A_542,B_539)))
      | ~ v1_funct_1(E_538) ) ),
    inference(resolution,[status(thm)],[c_4990,c_5171])).

tff(c_5185,plain,(
    ! [A_542,B_539,E_538] :
      ( k1_partfun1(A_542,B_539,'#skF_1','#skF_1',E_538,k2_funct_1('#skF_1')) = k5_relat_1(E_538,k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_538,k1_zfmisc_1(k2_zfmisc_1(A_542,B_539)))
      | ~ v1_funct_1(E_538) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4847,c_5173])).

tff(c_5336,plain,(
    ! [A_550,B_551,E_552] :
      ( k1_partfun1(A_550,B_551,'#skF_1','#skF_1',E_552,'#skF_1') = k5_relat_1(E_552,'#skF_1')
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(A_550,B_551)))
      | ~ v1_funct_1(E_552) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5215,c_5215,c_5185])).

tff(c_5342,plain,(
    ! [A_6] :
      ( k1_partfun1(A_6,A_6,'#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1')
      | A_6 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_4376,c_5336])).

tff(c_5356,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4084,c_5264,c_5342])).

tff(c_4078,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_4067,c_193])).

tff(c_4268,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4210,c_4078])).

tff(c_4848,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4846,c_4268])).

tff(c_5232,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5215,c_4848])).

tff(c_5357,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5356,c_5232])).

tff(c_5360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4502,c_5357])).

tff(c_5361,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_6556,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6536,c_5361])).

tff(c_7447,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7427,c_6556])).

tff(c_7552,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_7447])).

tff(c_7558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5413,c_84,c_6187,c_5957,c_5934,c_7552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:05:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.40/2.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.56  
% 7.40/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.56  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.40/2.56  
% 7.40/2.56  %Foreground sorts:
% 7.40/2.56  
% 7.40/2.56  
% 7.40/2.56  %Background operators:
% 7.40/2.56  
% 7.40/2.56  
% 7.40/2.56  %Foreground operators:
% 7.40/2.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.40/2.56  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.40/2.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.40/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.40/2.56  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.40/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.40/2.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.40/2.56  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.40/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.40/2.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.40/2.56  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.40/2.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.40/2.56  tff('#skF_2', type, '#skF_2': $i).
% 7.40/2.56  tff('#skF_1', type, '#skF_1': $i).
% 7.40/2.56  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.40/2.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.40/2.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.40/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.40/2.56  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.40/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.40/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.40/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.40/2.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.40/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.40/2.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.40/2.56  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.40/2.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.40/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.40/2.56  
% 7.66/2.59  tff(f_171, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 7.66/2.59  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.66/2.59  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.66/2.59  tff(f_158, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.66/2.59  tff(f_82, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.66/2.59  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.66/2.59  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.66/2.59  tff(f_120, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.66/2.59  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.66/2.59  tff(f_156, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.66/2.59  tff(f_136, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 7.66/2.59  tff(f_146, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.66/2.59  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.66/2.59  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.66/2.59  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.66/2.59  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.66/2.59  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.66/2.59  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.66/2.59  tff(f_44, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 7.66/2.59  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.66/2.59  tff(c_78, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.66/2.59  tff(c_5399, plain, (![C_560, A_561, B_562]: (v1_relat_1(C_560) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(A_561, B_562))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.66/2.59  tff(c_5413, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_5399])).
% 7.66/2.59  tff(c_84, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.66/2.59  tff(c_80, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.66/2.59  tff(c_6166, plain, (![C_675, A_676, B_677]: (v2_funct_1(C_675) | ~v3_funct_2(C_675, A_676, B_677) | ~v1_funct_1(C_675) | ~m1_subset_1(C_675, k1_zfmisc_1(k2_zfmisc_1(A_676, B_677))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.66/2.59  tff(c_6179, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_6166])).
% 7.66/2.59  tff(c_6187, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_6179])).
% 7.66/2.59  tff(c_74, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.66/2.59  tff(c_38, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.66/2.59  tff(c_85, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_38])).
% 7.66/2.59  tff(c_5946, plain, (![A_640, B_641, D_642]: (r2_relset_1(A_640, B_641, D_642, D_642) | ~m1_subset_1(D_642, k1_zfmisc_1(k2_zfmisc_1(A_640, B_641))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.66/2.59  tff(c_5957, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_85, c_5946])).
% 7.66/2.59  tff(c_5444, plain, (![C_566, B_567, A_568]: (v5_relat_1(C_566, B_567) | ~m1_subset_1(C_566, k1_zfmisc_1(k2_zfmisc_1(A_568, B_567))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.66/2.59  tff(c_5457, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_5444])).
% 7.66/2.59  tff(c_5553, plain, (![B_584, A_585]: (k2_relat_1(B_584)=A_585 | ~v2_funct_2(B_584, A_585) | ~v5_relat_1(B_584, A_585) | ~v1_relat_1(B_584))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.66/2.59  tff(c_5562, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_5457, c_5553])).
% 7.66/2.59  tff(c_5571, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5413, c_5562])).
% 7.66/2.59  tff(c_5577, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_5571])).
% 7.66/2.59  tff(c_5911, plain, (![C_637, B_638, A_639]: (v2_funct_2(C_637, B_638) | ~v3_funct_2(C_637, A_639, B_638) | ~v1_funct_1(C_637) | ~m1_subset_1(C_637, k1_zfmisc_1(k2_zfmisc_1(A_639, B_638))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.66/2.59  tff(c_5924, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_5911])).
% 7.66/2.59  tff(c_5931, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_5924])).
% 7.66/2.59  tff(c_5933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5577, c_5931])).
% 7.66/2.59  tff(c_5934, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_5571])).
% 7.66/2.59  tff(c_22, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.66/2.59  tff(c_87, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22])).
% 7.66/2.59  tff(c_82, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.66/2.59  tff(c_6517, plain, (![A_724, B_725]: (k2_funct_2(A_724, B_725)=k2_funct_1(B_725) | ~m1_subset_1(B_725, k1_zfmisc_1(k2_zfmisc_1(A_724, A_724))) | ~v3_funct_2(B_725, A_724, A_724) | ~v1_funct_2(B_725, A_724, A_724) | ~v1_funct_1(B_725))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.66/2.59  tff(c_6530, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_6517])).
% 7.66/2.59  tff(c_6536, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_6530])).
% 7.66/2.59  tff(c_6461, plain, (![A_717, B_718]: (v1_funct_1(k2_funct_2(A_717, B_718)) | ~m1_subset_1(B_718, k1_zfmisc_1(k2_zfmisc_1(A_717, A_717))) | ~v3_funct_2(B_718, A_717, A_717) | ~v1_funct_2(B_718, A_717, A_717) | ~v1_funct_1(B_718))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.66/2.59  tff(c_6474, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_6461])).
% 7.66/2.59  tff(c_6480, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_6474])).
% 7.66/2.59  tff(c_6555, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6536, c_6480])).
% 7.66/2.59  tff(c_62, plain, (![A_30, B_31]: (m1_subset_1(k2_funct_2(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v3_funct_2(B_31, A_30, A_30) | ~v1_funct_2(B_31, A_30, A_30) | ~v1_funct_1(B_31))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.66/2.59  tff(c_6872, plain, (![C_746, F_745, E_743, D_748, A_747, B_744]: (k1_partfun1(A_747, B_744, C_746, D_748, E_743, F_745)=k5_relat_1(E_743, F_745) | ~m1_subset_1(F_745, k1_zfmisc_1(k2_zfmisc_1(C_746, D_748))) | ~v1_funct_1(F_745) | ~m1_subset_1(E_743, k1_zfmisc_1(k2_zfmisc_1(A_747, B_744))) | ~v1_funct_1(E_743))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.66/2.59  tff(c_6885, plain, (![A_747, B_744, E_743]: (k1_partfun1(A_747, B_744, '#skF_1', '#skF_1', E_743, '#skF_2')=k5_relat_1(E_743, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_743, k1_zfmisc_1(k2_zfmisc_1(A_747, B_744))) | ~v1_funct_1(E_743))), inference(resolution, [status(thm)], [c_78, c_6872])).
% 7.66/2.59  tff(c_6920, plain, (![A_749, B_750, E_751]: (k1_partfun1(A_749, B_750, '#skF_1', '#skF_1', E_751, '#skF_2')=k5_relat_1(E_751, '#skF_2') | ~m1_subset_1(E_751, k1_zfmisc_1(k2_zfmisc_1(A_749, B_750))) | ~v1_funct_1(E_751))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6885])).
% 7.66/2.59  tff(c_7399, plain, (![A_764, B_765]: (k1_partfun1(A_764, A_764, '#skF_1', '#skF_1', k2_funct_2(A_764, B_765), '#skF_2')=k5_relat_1(k2_funct_2(A_764, B_765), '#skF_2') | ~v1_funct_1(k2_funct_2(A_764, B_765)) | ~m1_subset_1(B_765, k1_zfmisc_1(k2_zfmisc_1(A_764, A_764))) | ~v3_funct_2(B_765, A_764, A_764) | ~v1_funct_2(B_765, A_764, A_764) | ~v1_funct_1(B_765))), inference(resolution, [status(thm)], [c_62, c_6920])).
% 7.66/2.59  tff(c_7414, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_7399])).
% 7.66/2.59  tff(c_7427, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_6555, c_6536, c_6536, c_6536, c_7414])).
% 7.66/2.59  tff(c_225, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.66/2.59  tff(c_239, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_225])).
% 7.66/2.59  tff(c_1008, plain, (![C_169, A_170, B_171]: (v2_funct_1(C_169) | ~v3_funct_2(C_169, A_170, B_171) | ~v1_funct_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.66/2.59  tff(c_1021, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_1008])).
% 7.66/2.59  tff(c_1029, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_1021])).
% 7.66/2.59  tff(c_782, plain, (![A_134, B_135, D_136]: (r2_relset_1(A_134, B_135, D_136, D_136) | ~m1_subset_1(D_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.66/2.59  tff(c_793, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_85, c_782])).
% 7.66/2.59  tff(c_12, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.66/2.59  tff(c_91, plain, (![A_5]: (k1_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12])).
% 7.66/2.59  tff(c_18, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.66/2.59  tff(c_89, plain, (![A_6]: (v1_relat_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18])).
% 7.66/2.59  tff(c_155, plain, (![A_47]: (k1_relat_1(A_47)!=k1_xboole_0 | k1_xboole_0=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.66/2.59  tff(c_161, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))!=k1_xboole_0 | k6_partfun1(A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_89, c_155])).
% 7.66/2.59  tff(c_167, plain, (![A_6]: (k1_xboole_0!=A_6 | k6_partfun1(A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_161])).
% 7.66/2.59  tff(c_76, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.66/2.59  tff(c_193, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_76])).
% 7.66/2.59  tff(c_251, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_167, c_193])).
% 7.66/2.59  tff(c_311, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_251])).
% 7.66/2.59  tff(c_858, plain, (![A_147, B_148, C_149]: (k1_relset_1(A_147, B_148, C_149)=k1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.66/2.59  tff(c_877, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_858])).
% 7.66/2.59  tff(c_1193, plain, (![B_195, A_196, C_197]: (k1_xboole_0=B_195 | k1_relset_1(A_196, B_195, C_197)=A_196 | ~v1_funct_2(C_197, A_196, B_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.66/2.59  tff(c_1206, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_1193])).
% 7.66/2.59  tff(c_1214, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_877, c_1206])).
% 7.66/2.59  tff(c_1215, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_311, c_1214])).
% 7.66/2.59  tff(c_24, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.66/2.59  tff(c_86, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_24])).
% 7.66/2.59  tff(c_1333, plain, (![A_215, B_216]: (k2_funct_2(A_215, B_216)=k2_funct_1(B_216) | ~m1_subset_1(B_216, k1_zfmisc_1(k2_zfmisc_1(A_215, A_215))) | ~v3_funct_2(B_216, A_215, A_215) | ~v1_funct_2(B_216, A_215, A_215) | ~v1_funct_1(B_216))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.66/2.59  tff(c_1346, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_1333])).
% 7.66/2.59  tff(c_1352, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1346])).
% 7.66/2.59  tff(c_1313, plain, (![A_213, B_214]: (v1_funct_1(k2_funct_2(A_213, B_214)) | ~m1_subset_1(B_214, k1_zfmisc_1(k2_zfmisc_1(A_213, A_213))) | ~v3_funct_2(B_214, A_213, A_213) | ~v1_funct_2(B_214, A_213, A_213) | ~v1_funct_1(B_214))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.66/2.59  tff(c_1326, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_1313])).
% 7.66/2.59  tff(c_1332, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1326])).
% 7.66/2.59  tff(c_1353, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_1332])).
% 7.66/2.59  tff(c_1465, plain, (![A_235, B_236]: (m1_subset_1(k2_funct_2(A_235, B_236), k1_zfmisc_1(k2_zfmisc_1(A_235, A_235))) | ~m1_subset_1(B_236, k1_zfmisc_1(k2_zfmisc_1(A_235, A_235))) | ~v3_funct_2(B_236, A_235, A_235) | ~v1_funct_2(B_236, A_235, A_235) | ~v1_funct_1(B_236))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.66/2.59  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, B_3) | ~m1_subset_1(A_2, k1_zfmisc_1(B_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.66/2.59  tff(c_1537, plain, (![A_235, B_236]: (r1_tarski(k2_funct_2(A_235, B_236), k2_zfmisc_1(A_235, A_235)) | ~m1_subset_1(B_236, k1_zfmisc_1(k2_zfmisc_1(A_235, A_235))) | ~v3_funct_2(B_236, A_235, A_235) | ~v1_funct_2(B_236, A_235, A_235) | ~v1_funct_1(B_236))), inference(resolution, [status(thm)], [c_1465, c_4])).
% 7.66/2.59  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.66/2.59  tff(c_1689, plain, (![D_242, A_241, B_238, F_239, E_237, C_240]: (k1_partfun1(A_241, B_238, C_240, D_242, E_237, F_239)=k5_relat_1(E_237, F_239) | ~m1_subset_1(F_239, k1_zfmisc_1(k2_zfmisc_1(C_240, D_242))) | ~v1_funct_1(F_239) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_241, B_238))) | ~v1_funct_1(E_237))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.66/2.59  tff(c_2339, plain, (![A_268, E_266, D_264, A_267, B_269, C_265]: (k1_partfun1(A_267, B_269, C_265, D_264, E_266, A_268)=k5_relat_1(E_266, A_268) | ~v1_funct_1(A_268) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_269))) | ~v1_funct_1(E_266) | ~r1_tarski(A_268, k2_zfmisc_1(C_265, D_264)))), inference(resolution, [status(thm)], [c_6, c_1689])).
% 7.66/2.59  tff(c_2354, plain, (![C_265, D_264, A_268]: (k1_partfun1('#skF_1', '#skF_1', C_265, D_264, '#skF_2', A_268)=k5_relat_1('#skF_2', A_268) | ~v1_funct_1(A_268) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_268, k2_zfmisc_1(C_265, D_264)))), inference(resolution, [status(thm)], [c_78, c_2339])).
% 7.66/2.59  tff(c_2488, plain, (![C_270, D_271, A_272]: (k1_partfun1('#skF_1', '#skF_1', C_270, D_271, '#skF_2', A_272)=k5_relat_1('#skF_2', A_272) | ~v1_funct_1(A_272) | ~r1_tarski(A_272, k2_zfmisc_1(C_270, D_271)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2354])).
% 7.66/2.59  tff(c_2685, plain, (![A_278, B_279]: (k1_partfun1('#skF_1', '#skF_1', A_278, A_278, '#skF_2', k2_funct_2(A_278, B_279))=k5_relat_1('#skF_2', k2_funct_2(A_278, B_279)) | ~v1_funct_1(k2_funct_2(A_278, B_279)) | ~m1_subset_1(B_279, k1_zfmisc_1(k2_zfmisc_1(A_278, A_278))) | ~v3_funct_2(B_279, A_278, A_278) | ~v1_funct_2(B_279, A_278, A_278) | ~v1_funct_1(B_279))), inference(resolution, [status(thm)], [c_1537, c_2488])).
% 7.66/2.59  tff(c_2702, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_2685])).
% 7.66/2.59  tff(c_2718, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1353, c_1352, c_1352, c_1352, c_2702])).
% 7.66/2.59  tff(c_1354, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_193])).
% 7.66/2.59  tff(c_2760, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2718, c_1354])).
% 7.66/2.59  tff(c_2767, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_86, c_2760])).
% 7.66/2.59  tff(c_2773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_84, c_1029, c_793, c_1215, c_2767])).
% 7.66/2.59  tff(c_2775, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_251])).
% 7.66/2.59  tff(c_10, plain, (![A_4]: (k1_relat_1(A_4)!=k1_xboole_0 | k1_xboole_0=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.66/2.59  tff(c_247, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_239, c_10])).
% 7.66/2.59  tff(c_252, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_247])).
% 7.66/2.59  tff(c_2778, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2775, c_252])).
% 7.66/2.59  tff(c_3002, plain, (![A_298, B_299, C_300]: (k1_relset_1(A_298, B_299, C_300)=k1_relat_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.66/2.59  tff(c_3021, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_3002])).
% 7.66/2.59  tff(c_54, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.66/2.59  tff(c_3330, plain, (![B_335, C_336]: (k1_relset_1('#skF_1', B_335, C_336)='#skF_1' | ~v1_funct_2(C_336, '#skF_1', B_335) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_335))))), inference(demodulation, [status(thm), theory('equality')], [c_2775, c_2775, c_2775, c_2775, c_54])).
% 7.66/2.59  tff(c_3345, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_3330])).
% 7.66/2.59  tff(c_3355, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3021, c_3345])).
% 7.66/2.59  tff(c_3357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2778, c_3355])).
% 7.66/2.59  tff(c_3358, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_247])).
% 7.66/2.59  tff(c_99, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.66/2.59  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.66/2.59  tff(c_105, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99, c_16])).
% 7.66/2.59  tff(c_14, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.66/2.59  tff(c_123, plain, (![A_45]: (k2_relat_1(k6_partfun1(A_45))=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_14])).
% 7.66/2.59  tff(c_132, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_105, c_123])).
% 7.66/2.59  tff(c_3365, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3358, c_3358, c_132])).
% 7.66/2.59  tff(c_8, plain, (![A_4]: (k2_relat_1(A_4)!=k1_xboole_0 | k1_xboole_0=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.66/2.59  tff(c_246, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_239, c_8])).
% 7.66/2.59  tff(c_248, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_246])).
% 7.66/2.59  tff(c_3360, plain, (k2_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3358, c_248])).
% 7.66/2.59  tff(c_3414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3365, c_3360])).
% 7.66/2.59  tff(c_3415, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_246])).
% 7.66/2.59  tff(c_3497, plain, (![A_346]: (A_346!='#skF_2' | k6_partfun1(A_346)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_3415, c_167])).
% 7.66/2.59  tff(c_3506, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), '#skF_2') | '#skF_2'!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3497, c_193])).
% 7.66/2.59  tff(c_3552, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_3506])).
% 7.66/2.59  tff(c_3416, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_246])).
% 7.66/2.59  tff(c_3431, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_3416])).
% 7.66/2.59  tff(c_3532, plain, (![C_348, B_349, A_350]: (v5_relat_1(C_348, B_349) | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(A_350, B_349))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.66/2.59  tff(c_3545, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_3532])).
% 7.66/2.59  tff(c_3663, plain, (![B_366, A_367]: (k2_relat_1(B_366)=A_367 | ~v2_funct_2(B_366, A_367) | ~v5_relat_1(B_366, A_367) | ~v1_relat_1(B_366))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.66/2.59  tff(c_3672, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3545, c_3663])).
% 7.66/2.59  tff(c_3681, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_3431, c_3672])).
% 7.66/2.59  tff(c_3682, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3552, c_3681])).
% 7.66/2.59  tff(c_4041, plain, (![C_417, B_418, A_419]: (v2_funct_2(C_417, B_418) | ~v3_funct_2(C_417, A_419, B_418) | ~v1_funct_1(C_417) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_419, B_418))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.66/2.59  tff(c_4054, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_4041])).
% 7.66/2.59  tff(c_4063, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_4054])).
% 7.66/2.59  tff(c_4065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3682, c_4063])).
% 7.66/2.59  tff(c_4067, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_3506])).
% 7.66/2.59  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.66/2.59  tff(c_3424, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_2])).
% 7.66/2.59  tff(c_4072, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_3424])).
% 7.66/2.59  tff(c_4255, plain, (![A_430, B_431, D_432]: (r2_relset_1(A_430, B_431, D_432, D_432) | ~m1_subset_1(D_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.66/2.59  tff(c_4494, plain, (![A_462, B_463, A_464]: (r2_relset_1(A_462, B_463, A_464, A_464) | ~r1_tarski(A_464, k2_zfmisc_1(A_462, B_463)))), inference(resolution, [status(thm)], [c_6, c_4255])).
% 7.66/2.59  tff(c_4502, plain, (![A_462, B_463]: (r2_relset_1(A_462, B_463, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_4072, c_4494])).
% 7.66/2.59  tff(c_4084, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_84])).
% 7.66/2.59  tff(c_4080, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_239])).
% 7.66/2.59  tff(c_20, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.66/2.59  tff(c_88, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_20])).
% 7.66/2.59  tff(c_118, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_105, c_88])).
% 7.66/2.59  tff(c_3422, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_118])).
% 7.66/2.59  tff(c_4077, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_3422])).
% 7.66/2.59  tff(c_3418, plain, (![A_6]: (A_6!='#skF_2' | k6_partfun1(A_6)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_3415, c_167])).
% 7.66/2.59  tff(c_4210, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_4067, c_3418])).
% 7.66/2.59  tff(c_139, plain, (![A_46]: (k1_relat_1(k6_partfun1(A_46))=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12])).
% 7.66/2.59  tff(c_148, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_105, c_139])).
% 7.66/2.59  tff(c_3420, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_3415, c_148])).
% 7.66/2.59  tff(c_4074, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_4067, c_3420])).
% 7.66/2.59  tff(c_4407, plain, (![A_452, B_453, C_454]: (k1_relset_1(A_452, B_453, C_454)=k1_relat_1(C_454) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.66/2.59  tff(c_4514, plain, (![A_468, B_469, A_470]: (k1_relset_1(A_468, B_469, A_470)=k1_relat_1(A_470) | ~r1_tarski(A_470, k2_zfmisc_1(A_468, B_469)))), inference(resolution, [status(thm)], [c_6, c_4407])).
% 7.66/2.59  tff(c_4521, plain, (![A_468, B_469]: (k1_relset_1(A_468, B_469, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_4072, c_4514])).
% 7.66/2.59  tff(c_4525, plain, (![A_468, B_469]: (k1_relset_1(A_468, B_469, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4074, c_4521])).
% 7.66/2.59  tff(c_4079, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_3415])).
% 7.66/2.59  tff(c_50, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.66/2.59  tff(c_4625, plain, (![C_486, B_487]: (v1_funct_2(C_486, '#skF_1', B_487) | k1_relset_1('#skF_1', B_487, C_486)!='#skF_1' | ~m1_subset_1(C_486, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_487))))), inference(demodulation, [status(thm), theory('equality')], [c_4079, c_4079, c_4079, c_4079, c_50])).
% 7.66/2.59  tff(c_4681, plain, (![A_496, B_497]: (v1_funct_2(A_496, '#skF_1', B_497) | k1_relset_1('#skF_1', B_497, A_496)!='#skF_1' | ~r1_tarski(A_496, k2_zfmisc_1('#skF_1', B_497)))), inference(resolution, [status(thm)], [c_6, c_4625])).
% 7.66/2.59  tff(c_4689, plain, (![B_497]: (v1_funct_2('#skF_1', '#skF_1', B_497) | k1_relset_1('#skF_1', B_497, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_4072, c_4681])).
% 7.66/2.59  tff(c_4695, plain, (![B_497]: (v1_funct_2('#skF_1', '#skF_1', B_497))), inference(demodulation, [status(thm), theory('equality')], [c_4525, c_4689])).
% 7.66/2.59  tff(c_4082, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_80])).
% 7.66/2.59  tff(c_217, plain, (![A_54]: (m1_subset_1(k6_partfun1(A_54), k1_zfmisc_1(k2_zfmisc_1(A_54, A_54))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_38])).
% 7.66/2.59  tff(c_223, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_6, A_6))) | k1_xboole_0!=A_6)), inference(superposition, [status(thm), theory('equality')], [c_167, c_217])).
% 7.66/2.59  tff(c_4376, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_6, A_6))) | A_6!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4079, c_4079, c_223])).
% 7.66/2.59  tff(c_4816, plain, (![A_522, B_523]: (k2_funct_2(A_522, B_523)=k2_funct_1(B_523) | ~m1_subset_1(B_523, k1_zfmisc_1(k2_zfmisc_1(A_522, A_522))) | ~v3_funct_2(B_523, A_522, A_522) | ~v1_funct_2(B_523, A_522, A_522) | ~v1_funct_1(B_523))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.66/2.59  tff(c_4819, plain, (![A_6]: (k2_funct_2(A_6, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_6, A_6) | ~v1_funct_2('#skF_1', A_6, A_6) | ~v1_funct_1('#skF_1') | A_6!='#skF_1')), inference(resolution, [status(thm)], [c_4376, c_4816])).
% 7.66/2.59  tff(c_4840, plain, (![A_525]: (k2_funct_2(A_525, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_525, A_525) | ~v1_funct_2('#skF_1', A_525, A_525) | A_525!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4084, c_4819])).
% 7.66/2.59  tff(c_4843, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4082, c_4840])).
% 7.66/2.59  tff(c_4846, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4695, c_4843])).
% 7.66/2.59  tff(c_4874, plain, (![A_529, B_530]: (v1_funct_2(k2_funct_2(A_529, B_530), A_529, A_529) | ~m1_subset_1(B_530, k1_zfmisc_1(k2_zfmisc_1(A_529, A_529))) | ~v3_funct_2(B_530, A_529, A_529) | ~v1_funct_2(B_530, A_529, A_529) | ~v1_funct_1(B_530))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.66/2.59  tff(c_4876, plain, (![A_6]: (v1_funct_2(k2_funct_2(A_6, '#skF_1'), A_6, A_6) | ~v3_funct_2('#skF_1', A_6, A_6) | ~v1_funct_2('#skF_1', A_6, A_6) | ~v1_funct_1('#skF_1') | A_6!='#skF_1')), inference(resolution, [status(thm)], [c_4376, c_4874])).
% 7.66/2.59  tff(c_4888, plain, (![A_531]: (v1_funct_2(k2_funct_2(A_531, '#skF_1'), A_531, A_531) | ~v3_funct_2('#skF_1', A_531, A_531) | ~v1_funct_2('#skF_1', A_531, A_531) | A_531!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4084, c_4876])).
% 7.66/2.59  tff(c_4891, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4846, c_4888])).
% 7.66/2.59  tff(c_4894, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4695, c_4082, c_4891])).
% 7.66/2.59  tff(c_4377, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4079, c_4079, c_223])).
% 7.66/2.59  tff(c_4916, plain, (![A_536, B_537]: (m1_subset_1(k2_funct_2(A_536, B_537), k1_zfmisc_1(k2_zfmisc_1(A_536, A_536))) | ~m1_subset_1(B_537, k1_zfmisc_1(k2_zfmisc_1(A_536, A_536))) | ~v3_funct_2(B_537, A_536, A_536) | ~v1_funct_2(B_537, A_536, A_536) | ~v1_funct_1(B_537))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.66/2.59  tff(c_4970, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4846, c_4916])).
% 7.66/2.59  tff(c_4990, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4084, c_4695, c_4082, c_4377, c_4970])).
% 7.66/2.59  tff(c_4589, plain, (![B_26, C_27]: (k1_relset_1('#skF_1', B_26, C_27)='#skF_1' | ~v1_funct_2(C_27, '#skF_1', B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_26))))), inference(demodulation, [status(thm), theory('equality')], [c_4079, c_4079, c_4079, c_4079, c_54])).
% 7.66/2.59  tff(c_5015, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4990, c_4589])).
% 7.66/2.59  tff(c_5065, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4894, c_5015])).
% 7.66/2.59  tff(c_5078, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_4990, c_4])).
% 7.66/2.59  tff(c_4422, plain, (![A_452, B_453, A_2]: (k1_relset_1(A_452, B_453, A_2)=k1_relat_1(A_2) | ~r1_tarski(A_2, k2_zfmisc_1(A_452, B_453)))), inference(resolution, [status(thm)], [c_6, c_4407])).
% 7.66/2.59  tff(c_5123, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_5078, c_4422])).
% 7.66/2.59  tff(c_5163, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5065, c_5123])).
% 7.66/2.59  tff(c_26, plain, (![C_10, A_8, B_9]: (v1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.66/2.59  tff(c_5077, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_4990, c_26])).
% 7.66/2.59  tff(c_3419, plain, (![A_4]: (k1_relat_1(A_4)!='#skF_2' | A_4='#skF_2' | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_3415, c_10])).
% 7.66/2.59  tff(c_4302, plain, (![A_4]: (k1_relat_1(A_4)!='#skF_1' | A_4='#skF_1' | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_4067, c_3419])).
% 7.66/2.59  tff(c_5085, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_5077, c_4302])).
% 7.66/2.59  tff(c_5215, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5163, c_5085])).
% 7.66/2.59  tff(c_5258, plain, (k6_partfun1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5215, c_86])).
% 7.66/2.59  tff(c_5264, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4080, c_4084, c_4077, c_4210, c_4074, c_5258])).
% 7.66/2.59  tff(c_4800, plain, (![A_520, B_521]: (v1_funct_1(k2_funct_2(A_520, B_521)) | ~m1_subset_1(B_521, k1_zfmisc_1(k2_zfmisc_1(A_520, A_520))) | ~v3_funct_2(B_521, A_520, A_520) | ~v1_funct_2(B_521, A_520, A_520) | ~v1_funct_1(B_521))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.66/2.59  tff(c_4803, plain, (![A_6]: (v1_funct_1(k2_funct_2(A_6, '#skF_1')) | ~v3_funct_2('#skF_1', A_6, A_6) | ~v1_funct_2('#skF_1', A_6, A_6) | ~v1_funct_1('#skF_1') | A_6!='#skF_1')), inference(resolution, [status(thm)], [c_4376, c_4800])).
% 7.66/2.59  tff(c_4833, plain, (![A_524]: (v1_funct_1(k2_funct_2(A_524, '#skF_1')) | ~v3_funct_2('#skF_1', A_524, A_524) | ~v1_funct_2('#skF_1', A_524, A_524) | A_524!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4084, c_4803])).
% 7.66/2.59  tff(c_4835, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4082, c_4833])).
% 7.66/2.59  tff(c_4838, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4695, c_4835])).
% 7.66/2.59  tff(c_4847, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4846, c_4838])).
% 7.66/2.59  tff(c_5171, plain, (![F_540, D_543, E_538, C_541, B_539, A_542]: (k1_partfun1(A_542, B_539, C_541, D_543, E_538, F_540)=k5_relat_1(E_538, F_540) | ~m1_subset_1(F_540, k1_zfmisc_1(k2_zfmisc_1(C_541, D_543))) | ~v1_funct_1(F_540) | ~m1_subset_1(E_538, k1_zfmisc_1(k2_zfmisc_1(A_542, B_539))) | ~v1_funct_1(E_538))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.66/2.59  tff(c_5173, plain, (![A_542, B_539, E_538]: (k1_partfun1(A_542, B_539, '#skF_1', '#skF_1', E_538, k2_funct_1('#skF_1'))=k5_relat_1(E_538, k2_funct_1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~m1_subset_1(E_538, k1_zfmisc_1(k2_zfmisc_1(A_542, B_539))) | ~v1_funct_1(E_538))), inference(resolution, [status(thm)], [c_4990, c_5171])).
% 7.66/2.59  tff(c_5185, plain, (![A_542, B_539, E_538]: (k1_partfun1(A_542, B_539, '#skF_1', '#skF_1', E_538, k2_funct_1('#skF_1'))=k5_relat_1(E_538, k2_funct_1('#skF_1')) | ~m1_subset_1(E_538, k1_zfmisc_1(k2_zfmisc_1(A_542, B_539))) | ~v1_funct_1(E_538))), inference(demodulation, [status(thm), theory('equality')], [c_4847, c_5173])).
% 7.66/2.59  tff(c_5336, plain, (![A_550, B_551, E_552]: (k1_partfun1(A_550, B_551, '#skF_1', '#skF_1', E_552, '#skF_1')=k5_relat_1(E_552, '#skF_1') | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(A_550, B_551))) | ~v1_funct_1(E_552))), inference(demodulation, [status(thm), theory('equality')], [c_5215, c_5215, c_5185])).
% 7.66/2.59  tff(c_5342, plain, (![A_6]: (k1_partfun1(A_6, A_6, '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1') | A_6!='#skF_1')), inference(resolution, [status(thm)], [c_4376, c_5336])).
% 7.66/2.59  tff(c_5356, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4084, c_5264, c_5342])).
% 7.66/2.59  tff(c_4078, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_4067, c_193])).
% 7.66/2.59  tff(c_4268, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4210, c_4078])).
% 7.66/2.59  tff(c_4848, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4846, c_4268])).
% 7.66/2.59  tff(c_5232, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5215, c_4848])).
% 7.66/2.59  tff(c_5357, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5356, c_5232])).
% 7.66/2.59  tff(c_5360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4502, c_5357])).
% 7.66/2.59  tff(c_5361, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_76])).
% 7.66/2.59  tff(c_6556, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6536, c_5361])).
% 7.66/2.59  tff(c_7447, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7427, c_6556])).
% 7.66/2.59  tff(c_7552, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_87, c_7447])).
% 7.66/2.59  tff(c_7558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5413, c_84, c_6187, c_5957, c_5934, c_7552])).
% 7.66/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/2.59  
% 7.66/2.59  Inference rules
% 7.66/2.59  ----------------------
% 7.66/2.59  #Ref     : 0
% 7.66/2.59  #Sup     : 1488
% 7.66/2.59  #Fact    : 0
% 7.66/2.59  #Define  : 0
% 7.66/2.59  #Split   : 21
% 7.66/2.59  #Chain   : 0
% 7.66/2.59  #Close   : 0
% 7.66/2.59  
% 7.66/2.59  Ordering : KBO
% 7.66/2.59  
% 7.66/2.59  Simplification rules
% 7.66/2.59  ----------------------
% 7.66/2.59  #Subsume      : 146
% 7.66/2.59  #Demod        : 1717
% 7.66/2.59  #Tautology    : 809
% 7.66/2.59  #SimpNegUnit  : 38
% 7.66/2.59  #BackRed      : 114
% 7.66/2.59  
% 7.66/2.59  #Partial instantiations: 0
% 7.66/2.59  #Strategies tried      : 1
% 7.66/2.59  
% 7.66/2.59  Timing (in seconds)
% 7.66/2.59  ----------------------
% 7.66/2.59  Preprocessing        : 0.37
% 7.66/2.59  Parsing              : 0.19
% 7.66/2.59  CNF conversion       : 0.02
% 7.66/2.59  Main loop            : 1.40
% 7.66/2.59  Inferencing          : 0.49
% 7.66/2.59  Reduction            : 0.52
% 7.66/2.59  Demodulation         : 0.38
% 7.66/2.59  BG Simplification    : 0.05
% 7.66/2.59  Subsumption          : 0.23
% 7.66/2.59  Abstraction          : 0.06
% 7.66/2.59  MUC search           : 0.00
% 7.66/2.59  Cooper               : 0.00
% 7.66/2.59  Total                : 1.84
% 7.66/2.59  Index Insertion      : 0.00
% 7.66/2.59  Index Deletion       : 0.00
% 7.66/2.59  Index Matching       : 0.00
% 7.66/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

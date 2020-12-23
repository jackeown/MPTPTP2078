%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:02 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 860 expanded)
%              Number of leaves         :   49 ( 317 expanded)
%              Depth                    :   18
%              Number of atoms          :  457 (2380 expanded)
%              Number of equality atoms :  127 ( 360 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_195,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_144,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_166,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_182,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_164,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( ( k2_relat_1(A) = k1_xboole_0
              & k2_relat_1(B) = k1_xboole_0 )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4317,plain,(
    ! [C_660,A_661,B_662] :
      ( v1_relat_1(C_660)
      | ~ m1_subset_1(C_660,k1_zfmisc_1(k2_zfmisc_1(A_661,B_662))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4329,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4317])).

tff(c_82,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_78,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4845,plain,(
    ! [C_753,A_754,B_755] :
      ( v2_funct_1(C_753)
      | ~ v3_funct_2(C_753,A_754,B_755)
      | ~ v1_funct_1(C_753)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(k2_zfmisc_1(A_754,B_755))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4851,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4845])).

tff(c_4859,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_4851])).

tff(c_60,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5002,plain,(
    ! [A_781,B_782,C_783,D_784] :
      ( r2_relset_1(A_781,B_782,C_783,C_783)
      | ~ m1_subset_1(D_784,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782)))
      | ~ m1_subset_1(C_783,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5012,plain,(
    ! [A_785,C_786] :
      ( r2_relset_1(A_785,A_785,C_786,C_786)
      | ~ m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_785,A_785))) ) ),
    inference(resolution,[status(thm)],[c_60,c_5002])).

tff(c_5020,plain,(
    ! [A_36] : r2_relset_1(A_36,A_36,k6_partfun1(A_36),k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_60,c_5012])).

tff(c_4373,plain,(
    ! [C_669,B_670,A_671] :
      ( v5_relat_1(C_669,B_670)
      | ~ m1_subset_1(C_669,k1_zfmisc_1(k2_zfmisc_1(A_671,B_670))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4385,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_4373])).

tff(c_4453,plain,(
    ! [B_687,A_688] :
      ( k2_relat_1(B_687) = A_688
      | ~ v2_funct_2(B_687,A_688)
      | ~ v5_relat_1(B_687,A_688)
      | ~ v1_relat_1(B_687) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4462,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4385,c_4453])).

tff(c_4471,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4329,c_4462])).

tff(c_4503,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4471])).

tff(c_4676,plain,(
    ! [C_726,B_727,A_728] :
      ( v2_funct_2(C_726,B_727)
      | ~ v3_funct_2(C_726,A_728,B_727)
      | ~ v1_funct_1(C_726)
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(A_728,B_727))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4682,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4676])).

tff(c_4690,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_4682])).

tff(c_4692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4503,c_4690])).

tff(c_4693,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4471])).

tff(c_66,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_20,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_relat_1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_84,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_partfun1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_20])).

tff(c_80,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4730,plain,(
    ! [A_733,B_734,C_735] :
      ( k2_relset_1(A_733,B_734,C_735) = k2_relat_1(C_735)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(k2_zfmisc_1(A_733,B_734))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4736,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4730])).

tff(c_4743,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_4736])).

tff(c_5092,plain,(
    ! [C_803,A_804,B_805] :
      ( v1_funct_1(k2_funct_1(C_803))
      | k2_relset_1(A_804,B_805,C_803) != B_805
      | ~ v2_funct_1(C_803)
      | ~ m1_subset_1(C_803,k1_zfmisc_1(k2_zfmisc_1(A_804,B_805)))
      | ~ v1_funct_2(C_803,A_804,B_805)
      | ~ v1_funct_1(C_803) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_5098,plain,
    ( v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_5092])).

tff(c_5107,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_4859,c_4743,c_5098])).

tff(c_68,plain,(
    ! [C_48,B_47,A_46] :
      ( m1_subset_1(k2_funct_1(C_48),k1_zfmisc_1(k2_zfmisc_1(B_47,A_46)))
      | k2_relset_1(A_46,B_47,C_48) != B_47
      | ~ v2_funct_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_2(C_48,A_46,B_47)
      | ~ v1_funct_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_5241,plain,(
    ! [F_823,E_825,B_822,A_821,C_826,D_824] :
      ( k1_partfun1(A_821,B_822,C_826,D_824,E_825,F_823) = k5_relat_1(E_825,F_823)
      | ~ m1_subset_1(F_823,k1_zfmisc_1(k2_zfmisc_1(C_826,D_824)))
      | ~ v1_funct_1(F_823)
      | ~ m1_subset_1(E_825,k1_zfmisc_1(k2_zfmisc_1(A_821,B_822)))
      | ~ v1_funct_1(E_825) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_5247,plain,(
    ! [A_821,B_822,E_825] :
      ( k1_partfun1(A_821,B_822,'#skF_1','#skF_1',E_825,'#skF_2') = k5_relat_1(E_825,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_825,k1_zfmisc_1(k2_zfmisc_1(A_821,B_822)))
      | ~ v1_funct_1(E_825) ) ),
    inference(resolution,[status(thm)],[c_76,c_5241])).

tff(c_5257,plain,(
    ! [A_827,B_828,E_829] :
      ( k1_partfun1(A_827,B_828,'#skF_1','#skF_1',E_829,'#skF_2') = k5_relat_1(E_829,'#skF_2')
      | ~ m1_subset_1(E_829,k1_zfmisc_1(k2_zfmisc_1(A_827,B_828)))
      | ~ v1_funct_1(E_829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5247])).

tff(c_5317,plain,(
    ! [B_840,A_841,C_842] :
      ( k1_partfun1(B_840,A_841,'#skF_1','#skF_1',k2_funct_1(C_842),'#skF_2') = k5_relat_1(k2_funct_1(C_842),'#skF_2')
      | ~ v1_funct_1(k2_funct_1(C_842))
      | k2_relset_1(A_841,B_840,C_842) != B_840
      | ~ v2_funct_1(C_842)
      | ~ m1_subset_1(C_842,k1_zfmisc_1(k2_zfmisc_1(A_841,B_840)))
      | ~ v1_funct_2(C_842,A_841,B_840)
      | ~ v1_funct_1(C_842) ) ),
    inference(resolution,[status(thm)],[c_68,c_5257])).

tff(c_5326,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_5317])).

tff(c_5336,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_4859,c_4743,c_5107,c_5326])).

tff(c_5038,plain,(
    ! [A_792,B_793] :
      ( k2_funct_2(A_792,B_793) = k2_funct_1(B_793)
      | ~ m1_subset_1(B_793,k1_zfmisc_1(k2_zfmisc_1(A_792,A_792)))
      | ~ v3_funct_2(B_793,A_792,A_792)
      | ~ v1_funct_2(B_793,A_792,A_792)
      | ~ v1_funct_1(B_793) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_5044,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_5038])).

tff(c_5052,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_5044])).

tff(c_3957,plain,(
    ! [A_600,B_601,C_602,D_603] :
      ( r2_relset_1(A_600,B_601,C_602,C_602)
      | ~ m1_subset_1(D_603,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601)))
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3967,plain,(
    ! [A_604,C_605] :
      ( r2_relset_1(A_604,A_604,C_605,C_605)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(A_604,A_604))) ) ),
    inference(resolution,[status(thm)],[c_60,c_3957])).

tff(c_3976,plain,(
    ! [A_36] : r2_relset_1(A_36,A_36,k6_partfun1(A_36),k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_60,c_3967])).

tff(c_113,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_125,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_113])).

tff(c_3687,plain,(
    ! [C_566,A_567,B_568] :
      ( v2_funct_1(C_566)
      | ~ v3_funct_2(C_566,A_567,B_568)
      | ~ v1_funct_1(C_566)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(k2_zfmisc_1(A_567,B_568))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3697,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_3687])).

tff(c_3702,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_3697])).

tff(c_668,plain,(
    ! [C_152,A_153,B_154] :
      ( v2_funct_1(C_152)
      | ~ v3_funct_2(C_152,A_153,B_154)
      | ~ v1_funct_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_674,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_668])).

tff(c_682,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_674])).

tff(c_790,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( r2_relset_1(A_177,B_178,C_179,C_179)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_800,plain,(
    ! [A_181,C_182] :
      ( r2_relset_1(A_181,A_181,C_182,C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_181,A_181))) ) ),
    inference(resolution,[status(thm)],[c_60,c_790])).

tff(c_808,plain,(
    ! [A_36] : r2_relset_1(A_36,A_36,k6_partfun1(A_36),k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_60,c_800])).

tff(c_127,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_139,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_127])).

tff(c_228,plain,(
    ! [B_83,A_84] :
      ( k2_relat_1(B_83) = A_84
      | ~ v2_funct_2(B_83,A_84)
      | ~ v5_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_237,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_139,c_228])).

tff(c_246,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_237])).

tff(c_253,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_494,plain,(
    ! [C_127,B_128,A_129] :
      ( v2_funct_2(C_127,B_128)
      | ~ v3_funct_2(C_127,A_129,B_128)
      | ~ v1_funct_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_500,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_494])).

tff(c_508,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_500])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_508])).

tff(c_511,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_10,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) = k1_xboole_0
      | k1_relat_1(A_8) != k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_147,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_10])).

tff(c_168,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_8,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) = k1_xboole_0
      | k2_relat_1(A_8) != k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_148,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_8])).

tff(c_185,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_148])).

tff(c_513,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_185])).

tff(c_546,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_558,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_546])).

tff(c_826,plain,(
    ! [B_188,A_189,C_190] :
      ( k1_xboole_0 = B_188
      | k1_relset_1(A_189,B_188,C_190) = A_189
      | ~ v1_funct_2(C_190,A_189,B_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_832,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_826])).

tff(c_841,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_558,c_832])).

tff(c_842,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_513,c_841])).

tff(c_22,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_partfun1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_22])).

tff(c_571,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_relset_1(A_138,B_139,C_140) = k2_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_577,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_571])).

tff(c_584,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_577])).

tff(c_961,plain,(
    ! [C_214,A_215,B_216] :
      ( v1_funct_1(k2_funct_1(C_214))
      | k2_relset_1(A_215,B_216,C_214) != B_216
      | ~ v2_funct_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_2(C_214,A_215,B_216)
      | ~ v1_funct_1(C_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_967,plain,
    ( v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_961])).

tff(c_976,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_682,c_584,c_967])).

tff(c_1116,plain,(
    ! [F_236,E_238,A_234,D_237,C_239,B_235] :
      ( k1_partfun1(A_234,B_235,C_239,D_237,E_238,F_236) = k5_relat_1(E_238,F_236)
      | ~ m1_subset_1(F_236,k1_zfmisc_1(k2_zfmisc_1(C_239,D_237)))
      | ~ v1_funct_1(F_236)
      | ~ m1_subset_1(E_238,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2405,plain,(
    ! [B_397,A_396,C_393,B_392,A_395,E_394] :
      ( k1_partfun1(A_396,B_397,B_392,A_395,E_394,k2_funct_1(C_393)) = k5_relat_1(E_394,k2_funct_1(C_393))
      | ~ v1_funct_1(k2_funct_1(C_393))
      | ~ m1_subset_1(E_394,k1_zfmisc_1(k2_zfmisc_1(A_396,B_397)))
      | ~ v1_funct_1(E_394)
      | k2_relset_1(A_395,B_392,C_393) != B_392
      | ~ v2_funct_1(C_393)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_395,B_392)))
      | ~ v1_funct_2(C_393,A_395,B_392)
      | ~ v1_funct_1(C_393) ) ),
    inference(resolution,[status(thm)],[c_68,c_1116])).

tff(c_2411,plain,(
    ! [B_392,A_395,C_393] :
      ( k1_partfun1('#skF_1','#skF_1',B_392,A_395,'#skF_2',k2_funct_1(C_393)) = k5_relat_1('#skF_2',k2_funct_1(C_393))
      | ~ v1_funct_1(k2_funct_1(C_393))
      | ~ v1_funct_1('#skF_2')
      | k2_relset_1(A_395,B_392,C_393) != B_392
      | ~ v2_funct_1(C_393)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_395,B_392)))
      | ~ v1_funct_2(C_393,A_395,B_392)
      | ~ v1_funct_1(C_393) ) ),
    inference(resolution,[status(thm)],[c_76,c_2405])).

tff(c_2421,plain,(
    ! [B_398,A_399,C_400] :
      ( k1_partfun1('#skF_1','#skF_1',B_398,A_399,'#skF_2',k2_funct_1(C_400)) = k5_relat_1('#skF_2',k2_funct_1(C_400))
      | ~ v1_funct_1(k2_funct_1(C_400))
      | k2_relset_1(A_399,B_398,C_400) != B_398
      | ~ v2_funct_1(C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_399,B_398)))
      | ~ v1_funct_2(C_400,A_399,B_398)
      | ~ v1_funct_1(C_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2411])).

tff(c_2430,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_2421])).

tff(c_2440,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_682,c_584,c_976,c_2430])).

tff(c_930,plain,(
    ! [A_210,B_211] :
      ( k2_funct_2(A_210,B_211) = k2_funct_1(B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_zfmisc_1(A_210,A_210)))
      | ~ v3_funct_2(B_211,A_210,A_210)
      | ~ v1_funct_2(B_211,A_210,A_210)
      | ~ v1_funct_1(B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_936,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_930])).

tff(c_944,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_936])).

tff(c_74,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_100,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_946,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_100])).

tff(c_2443,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2440,c_946])).

tff(c_2450,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_2443])).

tff(c_2453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_82,c_682,c_808,c_842,c_2450])).

tff(c_2454,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_2988,plain,(
    ! [B_475,A_476] :
      ( k2_relat_1(B_475) = A_476
      | ~ v2_funct_2(B_475,A_476)
      | ~ v5_relat_1(B_475,A_476)
      | ~ v1_relat_1(B_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3000,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_139,c_2988])).

tff(c_3012,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_2454,c_3000])).

tff(c_3013,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3012])).

tff(c_3309,plain,(
    ! [C_517,B_518,A_519] :
      ( v2_funct_2(C_517,B_518)
      | ~ v3_funct_2(C_517,A_519,B_518)
      | ~ v1_funct_1(C_517)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(A_519,B_518))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3315,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_3309])).

tff(c_3323,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_3315])).

tff(c_3325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3013,c_3323])).

tff(c_3326,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3012])).

tff(c_3338,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3326,c_2454])).

tff(c_2455,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_3337,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3326,c_2455])).

tff(c_16,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( B_7 = A_5
      | k2_relat_1(B_7) != k1_xboole_0
      | k2_relat_1(A_5) != k1_xboole_0
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3457,plain,(
    ! [B_535,A_536] :
      ( B_535 = A_536
      | k2_relat_1(B_535) != '#skF_1'
      | k2_relat_1(A_536) != '#skF_1'
      | ~ v1_relat_1(B_535)
      | ~ v1_relat_1(A_536) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3326,c_3326,c_6])).

tff(c_3463,plain,(
    ! [A_536] :
      ( A_536 = '#skF_2'
      | k2_relat_1('#skF_2') != '#skF_1'
      | k2_relat_1(A_536) != '#skF_1'
      | ~ v1_relat_1(A_536) ) ),
    inference(resolution,[status(thm)],[c_125,c_3457])).

tff(c_3479,plain,(
    ! [A_539] :
      ( A_539 = '#skF_2'
      | k2_relat_1(A_539) != '#skF_1'
      | ~ v1_relat_1(A_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3338,c_3463])).

tff(c_3549,plain,(
    ! [A_547] :
      ( k2_funct_1(A_547) = '#skF_2'
      | k2_relat_1(k2_funct_1(A_547)) != '#skF_1'
      | ~ v1_funct_1(A_547)
      | ~ v1_relat_1(A_547) ) ),
    inference(resolution,[status(thm)],[c_14,c_3479])).

tff(c_3552,plain,(
    ! [A_10] :
      ( k2_funct_1(A_10) = '#skF_2'
      | k1_relat_1(A_10) != '#skF_1'
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3549])).

tff(c_3705,plain,
    ( k2_funct_1('#skF_2') = '#skF_2'
    | k1_relat_1('#skF_2') != '#skF_1'
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3702,c_3552])).

tff(c_3708,plain,(
    k2_funct_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_82,c_3337,c_3705])).

tff(c_3718,plain,
    ( k6_partfun1(k2_relat_1('#skF_2')) = k5_relat_1('#skF_2','#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3708,c_84])).

tff(c_3747,plain,(
    k5_relat_1('#skF_2','#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_82,c_3702,c_3338,c_3718])).

tff(c_4253,plain,(
    ! [F_645,C_648,B_644,E_647,D_646,A_643] :
      ( k1_partfun1(A_643,B_644,C_648,D_646,E_647,F_645) = k5_relat_1(E_647,F_645)
      | ~ m1_subset_1(F_645,k1_zfmisc_1(k2_zfmisc_1(C_648,D_646)))
      | ~ v1_funct_1(F_645)
      | ~ m1_subset_1(E_647,k1_zfmisc_1(k2_zfmisc_1(A_643,B_644)))
      | ~ v1_funct_1(E_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4262,plain,(
    ! [A_643,B_644,E_647] :
      ( k1_partfun1(A_643,B_644,'#skF_1','#skF_1',E_647,'#skF_2') = k5_relat_1(E_647,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_647,k1_zfmisc_1(k2_zfmisc_1(A_643,B_644)))
      | ~ v1_funct_1(E_647) ) ),
    inference(resolution,[status(thm)],[c_76,c_4253])).

tff(c_4279,plain,(
    ! [A_653,B_654,E_655] :
      ( k1_partfun1(A_653,B_654,'#skF_1','#skF_1',E_655,'#skF_2') = k5_relat_1(E_655,'#skF_2')
      | ~ m1_subset_1(E_655,k1_zfmisc_1(k2_zfmisc_1(A_653,B_654)))
      | ~ v1_funct_1(E_655) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4262])).

tff(c_4292,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_2') = k5_relat_1('#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4279])).

tff(c_4298,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3747,c_4292])).

tff(c_4000,plain,(
    ! [A_617,B_618] :
      ( k2_funct_2(A_617,B_618) = k2_funct_1(B_618)
      | ~ m1_subset_1(B_618,k1_zfmisc_1(k2_zfmisc_1(A_617,A_617)))
      | ~ v3_funct_2(B_618,A_617,A_617)
      | ~ v1_funct_2(B_618,A_617,A_617)
      | ~ v1_funct_1(B_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_4010,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4000])).

tff(c_4015,plain,(
    k2_funct_2('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_3708,c_4010])).

tff(c_4016,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4015,c_100])).

tff(c_4299,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4298,c_4016])).

tff(c_4302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3976,c_4299])).

tff(c_4303,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_5054,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5052,c_4303])).

tff(c_5339,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5336,c_5054])).

tff(c_5346,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_5339])).

tff(c_5349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4329,c_82,c_4859,c_5020,c_4693,c_5346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.58/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.67  
% 7.58/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.68  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.58/2.68  
% 7.58/2.68  %Foreground sorts:
% 7.58/2.68  
% 7.58/2.68  
% 7.58/2.68  %Background operators:
% 7.58/2.68  
% 7.58/2.68  
% 7.58/2.68  %Foreground operators:
% 7.58/2.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.58/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.58/2.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.58/2.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.58/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.58/2.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.58/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.58/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.58/2.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.58/2.68  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.58/2.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.58/2.68  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.58/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.58/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.58/2.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.58/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.58/2.68  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.58/2.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.58/2.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.58/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.58/2.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.58/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.58/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.58/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.58/2.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.58/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.58/2.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.58/2.68  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.58/2.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.58/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.58/2.68  
% 7.93/2.70  tff(f_195, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 7.93/2.70  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.93/2.70  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.93/2.70  tff(f_144, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.93/2.70  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 7.93/2.70  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.93/2.70  tff(f_140, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.93/2.70  tff(f_166, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.93/2.70  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.93/2.70  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.93/2.70  tff(f_182, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.93/2.70  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.93/2.70  tff(f_164, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.93/2.70  tff(f_50, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 7.93/2.70  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.93/2.70  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.93/2.70  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.93/2.70  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.93/2.70  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k2_relat_1(A) = k1_xboole_0) & (k2_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t197_relat_1)).
% 7.93/2.70  tff(c_76, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.93/2.70  tff(c_4317, plain, (![C_660, A_661, B_662]: (v1_relat_1(C_660) | ~m1_subset_1(C_660, k1_zfmisc_1(k2_zfmisc_1(A_661, B_662))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.93/2.70  tff(c_4329, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4317])).
% 7.93/2.70  tff(c_82, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.93/2.70  tff(c_78, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.93/2.70  tff(c_4845, plain, (![C_753, A_754, B_755]: (v2_funct_1(C_753) | ~v3_funct_2(C_753, A_754, B_755) | ~v1_funct_1(C_753) | ~m1_subset_1(C_753, k1_zfmisc_1(k2_zfmisc_1(A_754, B_755))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.93/2.70  tff(c_4851, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4845])).
% 7.93/2.70  tff(c_4859, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_4851])).
% 7.93/2.70  tff(c_60, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.93/2.70  tff(c_5002, plain, (![A_781, B_782, C_783, D_784]: (r2_relset_1(A_781, B_782, C_783, C_783) | ~m1_subset_1(D_784, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))) | ~m1_subset_1(C_783, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.93/2.70  tff(c_5012, plain, (![A_785, C_786]: (r2_relset_1(A_785, A_785, C_786, C_786) | ~m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_785, A_785))))), inference(resolution, [status(thm)], [c_60, c_5002])).
% 7.93/2.70  tff(c_5020, plain, (![A_36]: (r2_relset_1(A_36, A_36, k6_partfun1(A_36), k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_60, c_5012])).
% 7.93/2.70  tff(c_4373, plain, (![C_669, B_670, A_671]: (v5_relat_1(C_669, B_670) | ~m1_subset_1(C_669, k1_zfmisc_1(k2_zfmisc_1(A_671, B_670))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.93/2.70  tff(c_4385, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_4373])).
% 7.93/2.70  tff(c_4453, plain, (![B_687, A_688]: (k2_relat_1(B_687)=A_688 | ~v2_funct_2(B_687, A_688) | ~v5_relat_1(B_687, A_688) | ~v1_relat_1(B_687))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.93/2.70  tff(c_4462, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4385, c_4453])).
% 7.93/2.70  tff(c_4471, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4329, c_4462])).
% 7.93/2.70  tff(c_4503, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_4471])).
% 7.93/2.70  tff(c_4676, plain, (![C_726, B_727, A_728]: (v2_funct_2(C_726, B_727) | ~v3_funct_2(C_726, A_728, B_727) | ~v1_funct_1(C_726) | ~m1_subset_1(C_726, k1_zfmisc_1(k2_zfmisc_1(A_728, B_727))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.93/2.70  tff(c_4682, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4676])).
% 7.93/2.70  tff(c_4690, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_4682])).
% 7.93/2.70  tff(c_4692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4503, c_4690])).
% 7.93/2.70  tff(c_4693, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_4471])).
% 7.93/2.70  tff(c_66, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.93/2.70  tff(c_20, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_relat_1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.93/2.70  tff(c_84, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_partfun1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_20])).
% 7.93/2.70  tff(c_80, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.93/2.70  tff(c_4730, plain, (![A_733, B_734, C_735]: (k2_relset_1(A_733, B_734, C_735)=k2_relat_1(C_735) | ~m1_subset_1(C_735, k1_zfmisc_1(k2_zfmisc_1(A_733, B_734))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.93/2.70  tff(c_4736, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4730])).
% 7.93/2.71  tff(c_4743, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_4736])).
% 7.93/2.71  tff(c_5092, plain, (![C_803, A_804, B_805]: (v1_funct_1(k2_funct_1(C_803)) | k2_relset_1(A_804, B_805, C_803)!=B_805 | ~v2_funct_1(C_803) | ~m1_subset_1(C_803, k1_zfmisc_1(k2_zfmisc_1(A_804, B_805))) | ~v1_funct_2(C_803, A_804, B_805) | ~v1_funct_1(C_803))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.93/2.71  tff(c_5098, plain, (v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_5092])).
% 7.93/2.71  tff(c_5107, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_4859, c_4743, c_5098])).
% 7.93/2.71  tff(c_68, plain, (![C_48, B_47, A_46]: (m1_subset_1(k2_funct_1(C_48), k1_zfmisc_1(k2_zfmisc_1(B_47, A_46))) | k2_relset_1(A_46, B_47, C_48)!=B_47 | ~v2_funct_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_2(C_48, A_46, B_47) | ~v1_funct_1(C_48))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.93/2.71  tff(c_5241, plain, (![F_823, E_825, B_822, A_821, C_826, D_824]: (k1_partfun1(A_821, B_822, C_826, D_824, E_825, F_823)=k5_relat_1(E_825, F_823) | ~m1_subset_1(F_823, k1_zfmisc_1(k2_zfmisc_1(C_826, D_824))) | ~v1_funct_1(F_823) | ~m1_subset_1(E_825, k1_zfmisc_1(k2_zfmisc_1(A_821, B_822))) | ~v1_funct_1(E_825))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.93/2.71  tff(c_5247, plain, (![A_821, B_822, E_825]: (k1_partfun1(A_821, B_822, '#skF_1', '#skF_1', E_825, '#skF_2')=k5_relat_1(E_825, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_825, k1_zfmisc_1(k2_zfmisc_1(A_821, B_822))) | ~v1_funct_1(E_825))), inference(resolution, [status(thm)], [c_76, c_5241])).
% 7.93/2.71  tff(c_5257, plain, (![A_827, B_828, E_829]: (k1_partfun1(A_827, B_828, '#skF_1', '#skF_1', E_829, '#skF_2')=k5_relat_1(E_829, '#skF_2') | ~m1_subset_1(E_829, k1_zfmisc_1(k2_zfmisc_1(A_827, B_828))) | ~v1_funct_1(E_829))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_5247])).
% 7.93/2.71  tff(c_5317, plain, (![B_840, A_841, C_842]: (k1_partfun1(B_840, A_841, '#skF_1', '#skF_1', k2_funct_1(C_842), '#skF_2')=k5_relat_1(k2_funct_1(C_842), '#skF_2') | ~v1_funct_1(k2_funct_1(C_842)) | k2_relset_1(A_841, B_840, C_842)!=B_840 | ~v2_funct_1(C_842) | ~m1_subset_1(C_842, k1_zfmisc_1(k2_zfmisc_1(A_841, B_840))) | ~v1_funct_2(C_842, A_841, B_840) | ~v1_funct_1(C_842))), inference(resolution, [status(thm)], [c_68, c_5257])).
% 7.93/2.71  tff(c_5326, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_5317])).
% 7.93/2.71  tff(c_5336, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_4859, c_4743, c_5107, c_5326])).
% 7.93/2.71  tff(c_5038, plain, (![A_792, B_793]: (k2_funct_2(A_792, B_793)=k2_funct_1(B_793) | ~m1_subset_1(B_793, k1_zfmisc_1(k2_zfmisc_1(A_792, A_792))) | ~v3_funct_2(B_793, A_792, A_792) | ~v1_funct_2(B_793, A_792, A_792) | ~v1_funct_1(B_793))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.93/2.71  tff(c_5044, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_5038])).
% 7.93/2.71  tff(c_5052, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_5044])).
% 7.93/2.71  tff(c_3957, plain, (![A_600, B_601, C_602, D_603]: (r2_relset_1(A_600, B_601, C_602, C_602) | ~m1_subset_1(D_603, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.93/2.71  tff(c_3967, plain, (![A_604, C_605]: (r2_relset_1(A_604, A_604, C_605, C_605) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(A_604, A_604))))), inference(resolution, [status(thm)], [c_60, c_3957])).
% 7.93/2.71  tff(c_3976, plain, (![A_36]: (r2_relset_1(A_36, A_36, k6_partfun1(A_36), k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_60, c_3967])).
% 7.93/2.71  tff(c_113, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.93/2.71  tff(c_125, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_113])).
% 7.93/2.71  tff(c_3687, plain, (![C_566, A_567, B_568]: (v2_funct_1(C_566) | ~v3_funct_2(C_566, A_567, B_568) | ~v1_funct_1(C_566) | ~m1_subset_1(C_566, k1_zfmisc_1(k2_zfmisc_1(A_567, B_568))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.93/2.71  tff(c_3697, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_3687])).
% 7.93/2.71  tff(c_3702, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_3697])).
% 7.93/2.71  tff(c_668, plain, (![C_152, A_153, B_154]: (v2_funct_1(C_152) | ~v3_funct_2(C_152, A_153, B_154) | ~v1_funct_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.93/2.71  tff(c_674, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_668])).
% 7.93/2.71  tff(c_682, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_674])).
% 7.93/2.71  tff(c_790, plain, (![A_177, B_178, C_179, D_180]: (r2_relset_1(A_177, B_178, C_179, C_179) | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.93/2.71  tff(c_800, plain, (![A_181, C_182]: (r2_relset_1(A_181, A_181, C_182, C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_181, A_181))))), inference(resolution, [status(thm)], [c_60, c_790])).
% 7.93/2.71  tff(c_808, plain, (![A_36]: (r2_relset_1(A_36, A_36, k6_partfun1(A_36), k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_60, c_800])).
% 7.93/2.71  tff(c_127, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.93/2.71  tff(c_139, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_127])).
% 7.93/2.71  tff(c_228, plain, (![B_83, A_84]: (k2_relat_1(B_83)=A_84 | ~v2_funct_2(B_83, A_84) | ~v5_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.93/2.71  tff(c_237, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_139, c_228])).
% 7.93/2.71  tff(c_246, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_237])).
% 7.93/2.71  tff(c_253, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_246])).
% 7.93/2.71  tff(c_494, plain, (![C_127, B_128, A_129]: (v2_funct_2(C_127, B_128) | ~v3_funct_2(C_127, A_129, B_128) | ~v1_funct_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.93/2.71  tff(c_500, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_494])).
% 7.93/2.71  tff(c_508, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_500])).
% 7.93/2.71  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_508])).
% 7.93/2.71  tff(c_511, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_246])).
% 7.93/2.71  tff(c_10, plain, (![A_8]: (k2_relat_1(A_8)=k1_xboole_0 | k1_relat_1(A_8)!=k1_xboole_0 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.93/2.71  tff(c_147, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_10])).
% 7.93/2.71  tff(c_168, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_147])).
% 7.93/2.71  tff(c_8, plain, (![A_8]: (k1_relat_1(A_8)=k1_xboole_0 | k2_relat_1(A_8)!=k1_xboole_0 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.93/2.71  tff(c_148, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k2_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_8])).
% 7.93/2.71  tff(c_185, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_168, c_148])).
% 7.93/2.71  tff(c_513, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_185])).
% 7.93/2.71  tff(c_546, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.93/2.71  tff(c_558, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_546])).
% 7.93/2.71  tff(c_826, plain, (![B_188, A_189, C_190]: (k1_xboole_0=B_188 | k1_relset_1(A_189, B_188, C_190)=A_189 | ~v1_funct_2(C_190, A_189, B_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.93/2.71  tff(c_832, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_826])).
% 7.93/2.71  tff(c_841, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_558, c_832])).
% 7.93/2.71  tff(c_842, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_513, c_841])).
% 7.93/2.71  tff(c_22, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.93/2.71  tff(c_83, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_partfun1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_22])).
% 7.93/2.71  tff(c_571, plain, (![A_138, B_139, C_140]: (k2_relset_1(A_138, B_139, C_140)=k2_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.93/2.71  tff(c_577, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_571])).
% 7.93/2.71  tff(c_584, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_577])).
% 7.93/2.71  tff(c_961, plain, (![C_214, A_215, B_216]: (v1_funct_1(k2_funct_1(C_214)) | k2_relset_1(A_215, B_216, C_214)!=B_216 | ~v2_funct_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_2(C_214, A_215, B_216) | ~v1_funct_1(C_214))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.93/2.71  tff(c_967, plain, (v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_961])).
% 7.93/2.71  tff(c_976, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_682, c_584, c_967])).
% 7.93/2.71  tff(c_1116, plain, (![F_236, E_238, A_234, D_237, C_239, B_235]: (k1_partfun1(A_234, B_235, C_239, D_237, E_238, F_236)=k5_relat_1(E_238, F_236) | ~m1_subset_1(F_236, k1_zfmisc_1(k2_zfmisc_1(C_239, D_237))) | ~v1_funct_1(F_236) | ~m1_subset_1(E_238, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(E_238))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.93/2.71  tff(c_2405, plain, (![B_397, A_396, C_393, B_392, A_395, E_394]: (k1_partfun1(A_396, B_397, B_392, A_395, E_394, k2_funct_1(C_393))=k5_relat_1(E_394, k2_funct_1(C_393)) | ~v1_funct_1(k2_funct_1(C_393)) | ~m1_subset_1(E_394, k1_zfmisc_1(k2_zfmisc_1(A_396, B_397))) | ~v1_funct_1(E_394) | k2_relset_1(A_395, B_392, C_393)!=B_392 | ~v2_funct_1(C_393) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_395, B_392))) | ~v1_funct_2(C_393, A_395, B_392) | ~v1_funct_1(C_393))), inference(resolution, [status(thm)], [c_68, c_1116])).
% 7.93/2.71  tff(c_2411, plain, (![B_392, A_395, C_393]: (k1_partfun1('#skF_1', '#skF_1', B_392, A_395, '#skF_2', k2_funct_1(C_393))=k5_relat_1('#skF_2', k2_funct_1(C_393)) | ~v1_funct_1(k2_funct_1(C_393)) | ~v1_funct_1('#skF_2') | k2_relset_1(A_395, B_392, C_393)!=B_392 | ~v2_funct_1(C_393) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_395, B_392))) | ~v1_funct_2(C_393, A_395, B_392) | ~v1_funct_1(C_393))), inference(resolution, [status(thm)], [c_76, c_2405])).
% 7.93/2.71  tff(c_2421, plain, (![B_398, A_399, C_400]: (k1_partfun1('#skF_1', '#skF_1', B_398, A_399, '#skF_2', k2_funct_1(C_400))=k5_relat_1('#skF_2', k2_funct_1(C_400)) | ~v1_funct_1(k2_funct_1(C_400)) | k2_relset_1(A_399, B_398, C_400)!=B_398 | ~v2_funct_1(C_400) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_399, B_398))) | ~v1_funct_2(C_400, A_399, B_398) | ~v1_funct_1(C_400))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2411])).
% 7.93/2.71  tff(c_2430, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_2421])).
% 7.93/2.71  tff(c_2440, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_682, c_584, c_976, c_2430])).
% 7.93/2.71  tff(c_930, plain, (![A_210, B_211]: (k2_funct_2(A_210, B_211)=k2_funct_1(B_211) | ~m1_subset_1(B_211, k1_zfmisc_1(k2_zfmisc_1(A_210, A_210))) | ~v3_funct_2(B_211, A_210, A_210) | ~v1_funct_2(B_211, A_210, A_210) | ~v1_funct_1(B_211))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.93/2.71  tff(c_936, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_930])).
% 7.93/2.71  tff(c_944, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_936])).
% 7.93/2.71  tff(c_74, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.93/2.71  tff(c_100, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_74])).
% 7.93/2.71  tff(c_946, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_944, c_100])).
% 7.93/2.71  tff(c_2443, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2440, c_946])).
% 7.93/2.71  tff(c_2450, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_83, c_2443])).
% 7.93/2.71  tff(c_2453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_82, c_682, c_808, c_842, c_2450])).
% 7.93/2.71  tff(c_2454, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_147])).
% 7.93/2.71  tff(c_2988, plain, (![B_475, A_476]: (k2_relat_1(B_475)=A_476 | ~v2_funct_2(B_475, A_476) | ~v5_relat_1(B_475, A_476) | ~v1_relat_1(B_475))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.93/2.71  tff(c_3000, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_139, c_2988])).
% 7.93/2.71  tff(c_3012, plain, (k1_xboole_0='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_2454, c_3000])).
% 7.93/2.71  tff(c_3013, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_3012])).
% 7.93/2.71  tff(c_3309, plain, (![C_517, B_518, A_519]: (v2_funct_2(C_517, B_518) | ~v3_funct_2(C_517, A_519, B_518) | ~v1_funct_1(C_517) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(A_519, B_518))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.93/2.71  tff(c_3315, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_3309])).
% 7.93/2.71  tff(c_3323, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_3315])).
% 7.93/2.71  tff(c_3325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3013, c_3323])).
% 7.93/2.71  tff(c_3326, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3012])).
% 7.93/2.71  tff(c_3338, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3326, c_2454])).
% 7.93/2.71  tff(c_2455, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_147])).
% 7.93/2.71  tff(c_3337, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3326, c_2455])).
% 7.93/2.71  tff(c_16, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.93/2.71  tff(c_14, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.93/2.71  tff(c_6, plain, (![B_7, A_5]: (B_7=A_5 | k2_relat_1(B_7)!=k1_xboole_0 | k2_relat_1(A_5)!=k1_xboole_0 | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.93/2.71  tff(c_3457, plain, (![B_535, A_536]: (B_535=A_536 | k2_relat_1(B_535)!='#skF_1' | k2_relat_1(A_536)!='#skF_1' | ~v1_relat_1(B_535) | ~v1_relat_1(A_536))), inference(demodulation, [status(thm), theory('equality')], [c_3326, c_3326, c_6])).
% 7.93/2.71  tff(c_3463, plain, (![A_536]: (A_536='#skF_2' | k2_relat_1('#skF_2')!='#skF_1' | k2_relat_1(A_536)!='#skF_1' | ~v1_relat_1(A_536))), inference(resolution, [status(thm)], [c_125, c_3457])).
% 7.93/2.71  tff(c_3479, plain, (![A_539]: (A_539='#skF_2' | k2_relat_1(A_539)!='#skF_1' | ~v1_relat_1(A_539))), inference(demodulation, [status(thm), theory('equality')], [c_3338, c_3463])).
% 7.93/2.71  tff(c_3549, plain, (![A_547]: (k2_funct_1(A_547)='#skF_2' | k2_relat_1(k2_funct_1(A_547))!='#skF_1' | ~v1_funct_1(A_547) | ~v1_relat_1(A_547))), inference(resolution, [status(thm)], [c_14, c_3479])).
% 7.93/2.71  tff(c_3552, plain, (![A_10]: (k2_funct_1(A_10)='#skF_2' | k1_relat_1(A_10)!='#skF_1' | ~v1_funct_1(A_10) | ~v1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3549])).
% 7.93/2.71  tff(c_3705, plain, (k2_funct_1('#skF_2')='#skF_2' | k1_relat_1('#skF_2')!='#skF_1' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3702, c_3552])).
% 7.93/2.71  tff(c_3708, plain, (k2_funct_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_82, c_3337, c_3705])).
% 7.93/2.71  tff(c_3718, plain, (k6_partfun1(k2_relat_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3708, c_84])).
% 7.93/2.71  tff(c_3747, plain, (k5_relat_1('#skF_2', '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_82, c_3702, c_3338, c_3718])).
% 7.93/2.71  tff(c_4253, plain, (![F_645, C_648, B_644, E_647, D_646, A_643]: (k1_partfun1(A_643, B_644, C_648, D_646, E_647, F_645)=k5_relat_1(E_647, F_645) | ~m1_subset_1(F_645, k1_zfmisc_1(k2_zfmisc_1(C_648, D_646))) | ~v1_funct_1(F_645) | ~m1_subset_1(E_647, k1_zfmisc_1(k2_zfmisc_1(A_643, B_644))) | ~v1_funct_1(E_647))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.93/2.71  tff(c_4262, plain, (![A_643, B_644, E_647]: (k1_partfun1(A_643, B_644, '#skF_1', '#skF_1', E_647, '#skF_2')=k5_relat_1(E_647, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_647, k1_zfmisc_1(k2_zfmisc_1(A_643, B_644))) | ~v1_funct_1(E_647))), inference(resolution, [status(thm)], [c_76, c_4253])).
% 7.93/2.71  tff(c_4279, plain, (![A_653, B_654, E_655]: (k1_partfun1(A_653, B_654, '#skF_1', '#skF_1', E_655, '#skF_2')=k5_relat_1(E_655, '#skF_2') | ~m1_subset_1(E_655, k1_zfmisc_1(k2_zfmisc_1(A_653, B_654))) | ~v1_funct_1(E_655))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4262])).
% 7.93/2.71  tff(c_4292, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_2')=k5_relat_1('#skF_2', '#skF_2') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4279])).
% 7.93/2.71  tff(c_4298, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3747, c_4292])).
% 7.93/2.71  tff(c_4000, plain, (![A_617, B_618]: (k2_funct_2(A_617, B_618)=k2_funct_1(B_618) | ~m1_subset_1(B_618, k1_zfmisc_1(k2_zfmisc_1(A_617, A_617))) | ~v3_funct_2(B_618, A_617, A_617) | ~v1_funct_2(B_618, A_617, A_617) | ~v1_funct_1(B_618))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.93/2.71  tff(c_4010, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4000])).
% 7.93/2.71  tff(c_4015, plain, (k2_funct_2('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_3708, c_4010])).
% 7.93/2.71  tff(c_4016, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4015, c_100])).
% 7.93/2.71  tff(c_4299, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4298, c_4016])).
% 7.93/2.71  tff(c_4302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3976, c_4299])).
% 7.93/2.71  tff(c_4303, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_74])).
% 7.93/2.71  tff(c_5054, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5052, c_4303])).
% 7.93/2.71  tff(c_5339, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5336, c_5054])).
% 7.93/2.71  tff(c_5346, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_5339])).
% 7.93/2.71  tff(c_5349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4329, c_82, c_4859, c_5020, c_4693, c_5346])).
% 7.93/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/2.71  
% 7.93/2.71  Inference rules
% 7.93/2.71  ----------------------
% 7.93/2.71  #Ref     : 0
% 7.93/2.71  #Sup     : 1141
% 7.93/2.71  #Fact    : 0
% 7.93/2.71  #Define  : 0
% 7.93/2.71  #Split   : 28
% 7.93/2.71  #Chain   : 0
% 7.93/2.71  #Close   : 0
% 7.93/2.71  
% 7.93/2.71  Ordering : KBO
% 7.93/2.71  
% 7.93/2.71  Simplification rules
% 7.93/2.71  ----------------------
% 7.93/2.71  #Subsume      : 229
% 7.93/2.71  #Demod        : 888
% 7.93/2.71  #Tautology    : 392
% 7.93/2.71  #SimpNegUnit  : 36
% 7.93/2.71  #BackRed      : 49
% 7.93/2.71  
% 7.93/2.71  #Partial instantiations: 0
% 7.93/2.71  #Strategies tried      : 1
% 7.93/2.71  
% 7.93/2.71  Timing (in seconds)
% 7.93/2.71  ----------------------
% 7.93/2.71  Preprocessing        : 0.37
% 7.93/2.71  Parsing              : 0.19
% 7.93/2.71  CNF conversion       : 0.02
% 7.93/2.71  Main loop            : 1.51
% 7.93/2.71  Inferencing          : 0.52
% 7.93/2.71  Reduction            : 0.45
% 7.93/2.71  Demodulation         : 0.31
% 7.93/2.71  BG Simplification    : 0.05
% 7.93/2.71  Subsumption          : 0.36
% 7.93/2.71  Abstraction          : 0.06
% 7.93/2.71  MUC search           : 0.00
% 7.93/2.71  Cooper               : 0.00
% 7.93/2.71  Total                : 1.93
% 7.93/2.71  Index Insertion      : 0.00
% 7.93/2.71  Index Deletion       : 0.00
% 7.93/2.71  Index Matching       : 0.00
% 7.93/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------

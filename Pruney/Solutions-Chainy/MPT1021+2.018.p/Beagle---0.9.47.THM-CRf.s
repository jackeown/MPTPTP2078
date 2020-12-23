%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:02 EST 2020

% Result     : Theorem 8.61s
% Output     : CNFRefutation 8.94s
% Verified   : 
% Statistics : Number of formulae       :  302 (20370 expanded)
%              Number of leaves         :   48 (6513 expanded)
%              Depth                    :   27
%              Number of atoms          :  619 (48390 expanded)
%              Number of equality atoms :  154 (12178 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_174,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_139,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_161,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_135,axiom,(
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

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_8216,plain,(
    ! [C_879,A_880,B_881] :
      ( v1_relat_1(C_879)
      | ~ m1_subset_1(C_879,k1_zfmisc_1(k2_zfmisc_1(A_880,B_881))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8233,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_8216])).

tff(c_80,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_8903,plain,(
    ! [C_977,A_978,B_979] :
      ( v2_funct_1(C_977)
      | ~ v3_funct_2(C_977,A_978,B_979)
      | ~ v1_funct_1(C_977)
      | ~ m1_subset_1(C_977,k1_zfmisc_1(k2_zfmisc_1(A_978,B_979))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8913,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_8903])).

tff(c_8922,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_8913])).

tff(c_64,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_9206,plain,(
    ! [A_1002,B_1003,C_1004,D_1005] :
      ( r2_relset_1(A_1002,B_1003,C_1004,C_1004)
      | ~ m1_subset_1(D_1005,k1_zfmisc_1(k2_zfmisc_1(A_1002,B_1003)))
      | ~ m1_subset_1(C_1004,k1_zfmisc_1(k2_zfmisc_1(A_1002,B_1003))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9542,plain,(
    ! [A_1034,B_1035,C_1036] :
      ( r2_relset_1(A_1034,B_1035,C_1036,C_1036)
      | ~ m1_subset_1(C_1036,k1_zfmisc_1(k2_zfmisc_1(A_1034,B_1035))) ) ),
    inference(resolution,[status(thm)],[c_2,c_9206])).

tff(c_9553,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_64,c_9542])).

tff(c_8321,plain,(
    ! [C_896,B_897,A_898] :
      ( v5_relat_1(C_896,B_897)
      | ~ m1_subset_1(C_896,k1_zfmisc_1(k2_zfmisc_1(A_898,B_897))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8338,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_8321])).

tff(c_8404,plain,(
    ! [B_918,A_919] :
      ( k2_relat_1(B_918) = A_919
      | ~ v2_funct_2(B_918,A_919)
      | ~ v5_relat_1(B_918,A_919)
      | ~ v1_relat_1(B_918) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8413,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8338,c_8404])).

tff(c_8422,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8233,c_8413])).

tff(c_8429,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8422])).

tff(c_8718,plain,(
    ! [C_954,B_955,A_956] :
      ( v2_funct_2(C_954,B_955)
      | ~ v3_funct_2(C_954,A_956,B_955)
      | ~ v1_funct_1(C_954)
      | ~ m1_subset_1(C_954,k1_zfmisc_1(k2_zfmisc_1(A_956,B_955))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8728,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_8718])).

tff(c_8737,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_8728])).

tff(c_8739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8429,c_8737])).

tff(c_8740,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8422])).

tff(c_70,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_18,plain,(
    ! [A_10] :
      ( k5_relat_1(k2_funct_1(A_10),A_10) = k6_relat_1(k2_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_82,plain,(
    ! [A_10] :
      ( k5_relat_1(k2_funct_1(A_10),A_10) = k6_partfun1(k2_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18])).

tff(c_78,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_9514,plain,(
    ! [A_1032,B_1033] :
      ( k2_funct_2(A_1032,B_1033) = k2_funct_1(B_1033)
      | ~ m1_subset_1(B_1033,k1_zfmisc_1(k2_zfmisc_1(A_1032,A_1032)))
      | ~ v3_funct_2(B_1033,A_1032,A_1032)
      | ~ v1_funct_2(B_1033,A_1032,A_1032)
      | ~ v1_funct_1(B_1033) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_9524,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_9514])).

tff(c_9533,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_9524])).

tff(c_9458,plain,(
    ! [A_1029,B_1030] :
      ( v1_funct_1(k2_funct_2(A_1029,B_1030))
      | ~ m1_subset_1(B_1030,k1_zfmisc_1(k2_zfmisc_1(A_1029,A_1029)))
      | ~ v3_funct_2(B_1030,A_1029,A_1029)
      | ~ v1_funct_2(B_1030,A_1029,A_1029)
      | ~ v1_funct_1(B_1030) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_9468,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_9458])).

tff(c_9477,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_9468])).

tff(c_9535,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9533,c_9477])).

tff(c_54,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_funct_2(A_32,B_33),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v3_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_9909,plain,(
    ! [D_1070,F_1067,B_1071,E_1069,C_1068,A_1066] :
      ( k1_partfun1(A_1066,B_1071,C_1068,D_1070,E_1069,F_1067) = k5_relat_1(E_1069,F_1067)
      | ~ m1_subset_1(F_1067,k1_zfmisc_1(k2_zfmisc_1(C_1068,D_1070)))
      | ~ v1_funct_1(F_1067)
      | ~ m1_subset_1(E_1069,k1_zfmisc_1(k2_zfmisc_1(A_1066,B_1071)))
      | ~ v1_funct_1(E_1069) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_9920,plain,(
    ! [A_1066,B_1071,E_1069] :
      ( k1_partfun1(A_1066,B_1071,'#skF_1','#skF_1',E_1069,'#skF_2') = k5_relat_1(E_1069,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_1069,k1_zfmisc_1(k2_zfmisc_1(A_1066,B_1071)))
      | ~ v1_funct_1(E_1069) ) ),
    inference(resolution,[status(thm)],[c_74,c_9909])).

tff(c_9946,plain,(
    ! [A_1072,B_1073,E_1074] :
      ( k1_partfun1(A_1072,B_1073,'#skF_1','#skF_1',E_1074,'#skF_2') = k5_relat_1(E_1074,'#skF_2')
      | ~ m1_subset_1(E_1074,k1_zfmisc_1(k2_zfmisc_1(A_1072,B_1073)))
      | ~ v1_funct_1(E_1074) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9920])).

tff(c_10393,plain,(
    ! [A_1090,B_1091] :
      ( k1_partfun1(A_1090,A_1090,'#skF_1','#skF_1',k2_funct_2(A_1090,B_1091),'#skF_2') = k5_relat_1(k2_funct_2(A_1090,B_1091),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_1090,B_1091))
      | ~ m1_subset_1(B_1091,k1_zfmisc_1(k2_zfmisc_1(A_1090,A_1090)))
      | ~ v3_funct_2(B_1091,A_1090,A_1090)
      | ~ v1_funct_2(B_1091,A_1090,A_1090)
      | ~ v1_funct_1(B_1091) ) ),
    inference(resolution,[status(thm)],[c_54,c_9946])).

tff(c_10408,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_10393])).

tff(c_10426,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_9535,c_9533,c_9533,c_9533,c_10408])).

tff(c_6976,plain,(
    ! [A_712,B_713,C_714,D_715] :
      ( r2_relset_1(A_712,B_713,C_714,C_714)
      | ~ m1_subset_1(D_715,k1_zfmisc_1(k2_zfmisc_1(A_712,B_713)))
      | ~ m1_subset_1(C_714,k1_zfmisc_1(k2_zfmisc_1(A_712,B_713))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7187,plain,(
    ! [A_740,C_741] :
      ( r2_relset_1(A_740,A_740,C_741,C_741)
      | ~ m1_subset_1(C_741,k1_zfmisc_1(k2_zfmisc_1(A_740,A_740))) ) ),
    inference(resolution,[status(thm)],[c_64,c_6976])).

tff(c_7197,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_64,c_7187])).

tff(c_121,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_121])).

tff(c_801,plain,(
    ! [C_157,A_158,B_159] :
      ( v2_funct_1(C_157)
      | ~ v3_funct_2(C_157,A_158,B_159)
      | ~ v1_funct_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_811,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_801])).

tff(c_820,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_811])).

tff(c_1229,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( r2_relset_1(A_194,B_195,C_196,C_196)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1442,plain,(
    ! [A_215,C_216] :
      ( r2_relset_1(A_215,A_215,C_216,C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_215,A_215))) ) ),
    inference(resolution,[status(thm)],[c_64,c_1229])).

tff(c_1453,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_64,c_1442])).

tff(c_227,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_244,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_227])).

tff(c_307,plain,(
    ! [B_92,A_93] :
      ( k2_relat_1(B_92) = A_93
      | ~ v2_funct_2(B_92,A_93)
      | ~ v5_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_316,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_244,c_307])).

tff(c_325,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_316])).

tff(c_332,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_632,plain,(
    ! [C_132,B_133,A_134] :
      ( v2_funct_2(C_132,B_133)
      | ~ v3_funct_2(C_132,A_134,B_133)
      | ~ v1_funct_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_642,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_632])).

tff(c_651,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_642])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_651])).

tff(c_654,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_14,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_147,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_138,c_14])).

tff(c_168,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_656,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_168])).

tff(c_702,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_719,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_702])).

tff(c_1128,plain,(
    ! [B_185,A_186,C_187] :
      ( k1_xboole_0 = B_185
      | k1_relset_1(A_186,B_185,C_187) = A_186
      | ~ v1_funct_2(C_187,A_186,B_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1138,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_1128])).

tff(c_1148,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_719,c_1138])).

tff(c_1149,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_656,c_1148])).

tff(c_20,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_relat_1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_81,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_partfun1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_20])).

tff(c_1407,plain,(
    ! [A_213,B_214] :
      ( k2_funct_2(A_213,B_214) = k2_funct_1(B_214)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k2_zfmisc_1(A_213,A_213)))
      | ~ v3_funct_2(B_214,A_213,A_213)
      | ~ v1_funct_2(B_214,A_213,A_213)
      | ~ v1_funct_1(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1417,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1407])).

tff(c_1426,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1417])).

tff(c_1318,plain,(
    ! [A_207,B_208] :
      ( v1_funct_1(k2_funct_2(A_207,B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_zfmisc_1(A_207,A_207)))
      | ~ v3_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1328,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1318])).

tff(c_1337,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1328])).

tff(c_1428,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1426,c_1337])).

tff(c_1662,plain,(
    ! [A_239,B_240] :
      ( m1_subset_1(k2_funct_2(A_239,B_240),k1_zfmisc_1(k2_zfmisc_1(A_239,A_239)))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(k2_zfmisc_1(A_239,A_239)))
      | ~ v3_funct_2(B_240,A_239,A_239)
      | ~ v1_funct_2(B_240,A_239,A_239)
      | ~ v1_funct_1(B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1718,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_1662])).

tff(c_1739,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_1718])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,B_3)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1815,plain,(
    r1_tarski(k2_funct_1('#skF_2'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1739,c_4])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1816,plain,(
    ! [A_244,B_249,D_248,E_247,C_246,F_245] :
      ( k1_partfun1(A_244,B_249,C_246,D_248,E_247,F_245) = k5_relat_1(E_247,F_245)
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1(C_246,D_248)))
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_244,B_249)))
      | ~ v1_funct_1(E_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4400,plain,(
    ! [A_386,B_385,A_384,E_387,C_388,D_389] :
      ( k1_partfun1(A_384,B_385,C_388,D_389,E_387,A_386) = k5_relat_1(E_387,A_386)
      | ~ v1_funct_1(A_386)
      | ~ m1_subset_1(E_387,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385)))
      | ~ v1_funct_1(E_387)
      | ~ r1_tarski(A_386,k2_zfmisc_1(C_388,D_389)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1816])).

tff(c_4419,plain,(
    ! [C_388,D_389,A_386] :
      ( k1_partfun1('#skF_1','#skF_1',C_388,D_389,'#skF_2',A_386) = k5_relat_1('#skF_2',A_386)
      | ~ v1_funct_1(A_386)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_386,k2_zfmisc_1(C_388,D_389)) ) ),
    inference(resolution,[status(thm)],[c_74,c_4400])).

tff(c_4468,plain,(
    ! [C_396,D_397,A_398] :
      ( k1_partfun1('#skF_1','#skF_1',C_396,D_397,'#skF_2',A_398) = k5_relat_1('#skF_2',A_398)
      | ~ v1_funct_1(A_398)
      | ~ r1_tarski(A_398,k2_zfmisc_1(C_396,D_397)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4419])).

tff(c_4486,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1815,c_4468])).

tff(c_4516,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_4486])).

tff(c_72,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_98,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_1429,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1426,c_98])).

tff(c_4523,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4516,c_1429])).

tff(c_4530,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_4523])).

tff(c_4533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_80,c_820,c_1453,c_1149,c_4530])).

tff(c_4534,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_4542,plain,(
    ! [A_1] : m1_subset_1('#skF_2',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_2])).

tff(c_4976,plain,(
    ! [C_489,B_490,A_491] :
      ( v2_funct_2(C_489,B_490)
      | ~ v3_funct_2(C_489,A_491,B_490)
      | ~ v1_funct_1(C_489)
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(A_491,B_490))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4980,plain,(
    ! [B_490,A_491] :
      ( v2_funct_2('#skF_2',B_490)
      | ~ v3_funct_2('#skF_2',A_491,B_490)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4542,c_4976])).

tff(c_4993,plain,(
    ! [B_492,A_493] :
      ( v2_funct_2('#skF_2',B_492)
      | ~ v3_funct_2('#skF_2',A_493,B_492) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4980])).

tff(c_4997,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_4993])).

tff(c_4535,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_4548,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_4535])).

tff(c_101,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_101])).

tff(c_4538,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_113])).

tff(c_4555,plain,(
    ! [B_400,A_401] :
      ( v5_relat_1(B_400,A_401)
      | ~ r1_tarski(k2_relat_1(B_400),A_401)
      | ~ v1_relat_1(B_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4558,plain,(
    ! [A_401] :
      ( v5_relat_1('#skF_2',A_401)
      | ~ r1_tarski('#skF_2',A_401)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4548,c_4555])).

tff(c_4560,plain,(
    ! [A_401] : v5_relat_1('#skF_2',A_401) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_4538,c_4558])).

tff(c_4722,plain,(
    ! [B_438,A_439] :
      ( k2_relat_1(B_438) = A_439
      | ~ v2_funct_2(B_438,A_439)
      | ~ v5_relat_1(B_438,A_439)
      | ~ v1_relat_1(B_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4728,plain,(
    ! [A_401] :
      ( k2_relat_1('#skF_2') = A_401
      | ~ v2_funct_2('#skF_2',A_401)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4560,c_4722])).

tff(c_4734,plain,(
    ! [A_401] :
      ( A_401 = '#skF_2'
      | ~ v2_funct_2('#skF_2',A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_4548,c_4728])).

tff(c_5001,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4997,c_4734])).

tff(c_16,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_146,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_138,c_16])).

tff(c_167,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_4536,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_167])).

tff(c_5018,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_5001,c_4536])).

tff(c_4767,plain,(
    ! [A_449,B_450,C_451] :
      ( k1_relset_1(A_449,B_450,C_451) = k1_relat_1(C_451)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4779,plain,(
    ! [A_449,B_450] : k1_relset_1(A_449,B_450,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4542,c_4767])).

tff(c_5006,plain,(
    ! [A_449,B_450] : k1_relset_1(A_449,B_450,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_5001,c_4779])).

tff(c_5141,plain,(
    ! [A_501] : m1_subset_1('#skF_1',k1_zfmisc_1(A_501)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_4542])).

tff(c_5021,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_4534])).

tff(c_46,plain,(
    ! [B_28,C_29] :
      ( k1_relset_1(k1_xboole_0,B_28,C_29) = k1_xboole_0
      | ~ v1_funct_2(C_29,k1_xboole_0,B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5128,plain,(
    ! [B_28,C_29] :
      ( k1_relset_1('#skF_1',B_28,C_29) = '#skF_1'
      | ~ v1_funct_2(C_29,'#skF_1',B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_28))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5021,c_5021,c_5021,c_5021,c_46])).

tff(c_5179,plain,(
    ! [B_28] :
      ( k1_relset_1('#skF_1',B_28,'#skF_1') = '#skF_1'
      | ~ v1_funct_2('#skF_1','#skF_1',B_28) ) ),
    inference(resolution,[status(thm)],[c_5141,c_5128])).

tff(c_5366,plain,(
    ! [B_28] :
      ( k1_relat_1('#skF_1') = '#skF_1'
      | ~ v1_funct_2('#skF_1','#skF_1',B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5006,c_5179])).

tff(c_5367,plain,(
    ! [B_28] : ~ v1_funct_2('#skF_1','#skF_1',B_28) ),
    inference(negUnitSimplification,[status(thm)],[c_5018,c_5366])).

tff(c_5025,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_78])).

tff(c_5369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5367,c_5025])).

tff(c_5370,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_5377,plain,(
    ! [A_1] : m1_subset_1('#skF_2',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5370,c_2])).

tff(c_6820,plain,(
    ! [C_702,B_703,A_704] :
      ( v2_funct_2(C_702,B_703)
      | ~ v3_funct_2(C_702,A_704,B_703)
      | ~ v1_funct_1(C_702)
      | ~ m1_subset_1(C_702,k1_zfmisc_1(k2_zfmisc_1(A_704,B_703))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6824,plain,(
    ! [B_703,A_704] :
      ( v2_funct_2('#skF_2',B_703)
      | ~ v3_funct_2('#skF_2',A_704,B_703)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_5377,c_6820])).

tff(c_6837,plain,(
    ! [B_705,A_706] :
      ( v2_funct_2('#skF_2',B_705)
      | ~ v3_funct_2('#skF_2',A_706,B_705) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6824])).

tff(c_6841,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_6837])).

tff(c_5371,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_5383,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5370,c_5371])).

tff(c_5594,plain,(
    ! [A_579,B_580,C_581] :
      ( k1_relset_1(A_579,B_580,C_581) = k1_relat_1(C_581)
      | ~ m1_subset_1(C_581,k1_zfmisc_1(k2_zfmisc_1(A_579,B_580))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5598,plain,(
    ! [A_579,B_580] : k1_relset_1(A_579,B_580,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5377,c_5594])).

tff(c_5607,plain,(
    ! [A_579,B_580] : k1_relset_1(A_579,B_580,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5383,c_5598])).

tff(c_48,plain,(
    ! [B_28,A_27,C_29] :
      ( k1_xboole_0 = B_28
      | k1_relset_1(A_27,B_28,C_29) = A_27
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6164,plain,(
    ! [B_639,A_640,C_641] :
      ( B_639 = '#skF_2'
      | k1_relset_1(A_640,B_639,C_641) = A_640
      | ~ v1_funct_2(C_641,A_640,B_639)
      | ~ m1_subset_1(C_641,k1_zfmisc_1(k2_zfmisc_1(A_640,B_639))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5370,c_48])).

tff(c_6168,plain,(
    ! [B_639,A_640] :
      ( B_639 = '#skF_2'
      | k1_relset_1(A_640,B_639,'#skF_2') = A_640
      | ~ v1_funct_2('#skF_2',A_640,B_639) ) ),
    inference(resolution,[status(thm)],[c_5377,c_6164])).

tff(c_6384,plain,(
    ! [B_656,A_657] :
      ( B_656 = '#skF_2'
      | A_657 = '#skF_2'
      | ~ v1_funct_2('#skF_2',A_657,B_656) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5607,c_6168])).

tff(c_6398,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_78,c_6384])).

tff(c_6426,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6398,c_6398,c_5383])).

tff(c_5824,plain,(
    ! [C_609,B_610,A_611] :
      ( v2_funct_2(C_609,B_610)
      | ~ v3_funct_2(C_609,A_611,B_610)
      | ~ v1_funct_1(C_609)
      | ~ m1_subset_1(C_609,k1_zfmisc_1(k2_zfmisc_1(A_611,B_610))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5828,plain,(
    ! [B_610,A_611] :
      ( v2_funct_2('#skF_2',B_610)
      | ~ v3_funct_2('#skF_2',A_611,B_610)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_5377,c_5824])).

tff(c_5952,plain,(
    ! [B_621,A_622] :
      ( v2_funct_2('#skF_2',B_621)
      | ~ v3_funct_2('#skF_2',A_622,B_621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5828])).

tff(c_5956,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_5952])).

tff(c_5438,plain,(
    ! [C_543,B_544,A_545] :
      ( v5_relat_1(C_543,B_544)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_545,B_544))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5450,plain,(
    ! [B_544] : v5_relat_1('#skF_2',B_544) ),
    inference(resolution,[status(thm)],[c_5377,c_5438])).

tff(c_5558,plain,(
    ! [B_574,A_575] :
      ( k2_relat_1(B_574) = A_575
      | ~ v2_funct_2(B_574,A_575)
      | ~ v5_relat_1(B_574,A_575)
      | ~ v1_relat_1(B_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5564,plain,(
    ! [B_544] :
      ( k2_relat_1('#skF_2') = B_544
      | ~ v2_funct_2('#skF_2',B_544)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_5450,c_5558])).

tff(c_5570,plain,(
    ! [B_544] :
      ( k2_relat_1('#skF_2') = B_544
      | ~ v2_funct_2('#skF_2',B_544) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_5564])).

tff(c_5960,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5956,c_5570])).

tff(c_5502,plain,(
    ! [B_558,A_559] :
      ( r1_tarski(k2_relat_1(B_558),A_559)
      | ~ v5_relat_1(B_558,A_559)
      | ~ v1_relat_1(B_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_137,plain,(
    ! [A_2,A_58,B_59] :
      ( v1_relat_1(A_2)
      | ~ r1_tarski(A_2,k2_zfmisc_1(A_58,B_59)) ) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_5543,plain,(
    ! [B_571,A_572,B_573] :
      ( v1_relat_1(k2_relat_1(B_571))
      | ~ v5_relat_1(B_571,k2_zfmisc_1(A_572,B_573))
      | ~ v1_relat_1(B_571) ) ),
    inference(resolution,[status(thm)],[c_5502,c_137])).

tff(c_5551,plain,
    ( v1_relat_1(k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5450,c_5543])).

tff(c_5557,plain,(
    v1_relat_1(k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_5551])).

tff(c_5374,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != '#skF_2'
      | A_9 = '#skF_2'
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5370,c_5370,c_16])).

tff(c_5578,plain,
    ( k1_relat_1(k2_relat_1('#skF_2')) != '#skF_2'
    | k2_relat_1('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5557,c_5374])).

tff(c_5617,plain,(
    k1_relat_1(k2_relat_1('#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5578])).

tff(c_5974,plain,(
    k1_relat_1('#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5960,c_5617])).

tff(c_6406,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6398,c_5974])).

tff(c_6554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6426,c_6406])).

tff(c_6555,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5578])).

tff(c_6557,plain,(
    ! [B_544] :
      ( B_544 = '#skF_2'
      | ~ v2_funct_2('#skF_2',B_544) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6555,c_5570])).

tff(c_6845,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6841,c_6557])).

tff(c_6875,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_80])).

tff(c_6872,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_138])).

tff(c_6645,plain,(
    ! [C_669,A_670,B_671] :
      ( v2_funct_1(C_669)
      | ~ v3_funct_2(C_669,A_670,B_671)
      | ~ v1_funct_1(C_669)
      | ~ m1_subset_1(C_669,k1_zfmisc_1(k2_zfmisc_1(A_670,B_671))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6649,plain,(
    ! [A_670,B_671] :
      ( v2_funct_1('#skF_2')
      | ~ v3_funct_2('#skF_2',A_670,B_671)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_5377,c_6645])).

tff(c_6659,plain,(
    ! [A_670,B_671] :
      ( v2_funct_1('#skF_2')
      | ~ v3_funct_2('#skF_2',A_670,B_671) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6649])).

tff(c_6662,plain,(
    ! [A_670,B_671] : ~ v3_funct_2('#skF_2',A_670,B_671) ),
    inference(splitLeft,[status(thm)],[c_6659])).

tff(c_6664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6662,c_76])).

tff(c_6665,plain,(
    v2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6659])).

tff(c_6853,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_6665])).

tff(c_6869,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_6845,c_5383])).

tff(c_6857,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_6845,c_6555])).

tff(c_42,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,k1_xboole_0,B_28)
      | k1_relset_1(k1_xboole_0,B_28,C_29) != k1_xboole_0
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6790,plain,(
    ! [C_695,B_696] :
      ( v1_funct_2(C_695,'#skF_2',B_696)
      | k1_relset_1('#skF_2',B_696,C_695) != '#skF_2'
      | ~ m1_subset_1(C_695,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_696))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5370,c_5370,c_5370,c_5370,c_42])).

tff(c_6794,plain,(
    ! [B_696] :
      ( v1_funct_2('#skF_2','#skF_2',B_696)
      | k1_relset_1('#skF_2',B_696,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_5377,c_6790])).

tff(c_6805,plain,(
    ! [B_696] : v1_funct_2('#skF_2','#skF_2',B_696) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5607,c_6794])).

tff(c_6849,plain,(
    ! [B_696] : v1_funct_2('#skF_1','#skF_1',B_696) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_6845,c_6805])).

tff(c_6873,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_76])).

tff(c_6867,plain,(
    ! [A_1] : m1_subset_1('#skF_1',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_5377])).

tff(c_7100,plain,(
    ! [A_730,B_731] :
      ( k2_funct_2(A_730,B_731) = k2_funct_1(B_731)
      | ~ m1_subset_1(B_731,k1_zfmisc_1(k2_zfmisc_1(A_730,A_730)))
      | ~ v3_funct_2(B_731,A_730,A_730)
      | ~ v1_funct_2(B_731,A_730,A_730)
      | ~ v1_funct_1(B_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_7104,plain,(
    ! [A_730] :
      ( k2_funct_2(A_730,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_730,A_730)
      | ~ v1_funct_2('#skF_1',A_730,A_730)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6867,c_7100])).

tff(c_7457,plain,(
    ! [A_792] :
      ( k2_funct_2(A_792,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_792,A_792)
      | ~ v1_funct_2('#skF_1',A_792,A_792) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6875,c_7104])).

tff(c_7460,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_6873,c_7457])).

tff(c_7463,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6849,c_7460])).

tff(c_7469,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7463,c_54])).

tff(c_7473,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6875,c_6849,c_6873,c_6867,c_7469])).

tff(c_22,plain,(
    ! [C_13,A_11,B_12] :
      ( v1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7548,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_7473,c_22])).

tff(c_6861,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != '#skF_1'
      | A_9 = '#skF_1'
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_6845,c_5374])).

tff(c_7556,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7548,c_6861])).

tff(c_7606,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7556])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_7544,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_7473,c_28])).

tff(c_7549,plain,(
    r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_7473,c_4])).

tff(c_6733,plain,(
    ! [B_684,C_685] :
      ( k1_relset_1('#skF_2',B_684,C_685) = '#skF_2'
      | ~ v1_funct_2(C_685,'#skF_2',B_684)
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_684))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5370,c_5370,c_5370,c_5370,c_46])).

tff(c_6750,plain,(
    ! [B_684,A_2] :
      ( k1_relset_1('#skF_2',B_684,A_2) = '#skF_2'
      | ~ v1_funct_2(A_2,'#skF_2',B_684)
      | ~ r1_tarski(A_2,k2_zfmisc_1('#skF_2',B_684)) ) ),
    inference(resolution,[status(thm)],[c_6,c_6733])).

tff(c_7678,plain,(
    ! [B_801,A_802] :
      ( k1_relset_1('#skF_1',B_801,A_802) = '#skF_1'
      | ~ v1_funct_2(A_802,'#skF_1',B_801)
      | ~ r1_tarski(A_802,k2_zfmisc_1('#skF_1',B_801)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_6845,c_6845,c_6845,c_6750])).

tff(c_7681,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_7549,c_7678])).

tff(c_7695,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7544,c_7681])).

tff(c_7696,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_7606,c_7695])).

tff(c_7199,plain,(
    ! [A_742,B_743] :
      ( v1_funct_2(k2_funct_2(A_742,B_743),A_742,A_742)
      | ~ m1_subset_1(B_743,k1_zfmisc_1(k2_zfmisc_1(A_742,A_742)))
      | ~ v3_funct_2(B_743,A_742,A_742)
      | ~ v1_funct_2(B_743,A_742,A_742)
      | ~ v1_funct_1(B_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_7202,plain,(
    ! [A_742] :
      ( v1_funct_2(k2_funct_2(A_742,'#skF_1'),A_742,A_742)
      | ~ v3_funct_2('#skF_1',A_742,A_742)
      | ~ v1_funct_2('#skF_1',A_742,A_742)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6867,c_7199])).

tff(c_7732,plain,(
    ! [A_808] :
      ( v1_funct_2(k2_funct_2(A_808,'#skF_1'),A_808,A_808)
      | ~ v3_funct_2('#skF_1',A_808,A_808)
      | ~ v1_funct_2('#skF_1',A_808,A_808) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6875,c_7202])).

tff(c_7735,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7463,c_7732])).

tff(c_7737,plain,(
    v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6849,c_6873,c_7735])).

tff(c_7739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7696,c_7737])).

tff(c_7740,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7556])).

tff(c_5375,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != '#skF_2'
      | A_9 = '#skF_2'
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5370,c_5370,c_14])).

tff(c_6860,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != '#skF_1'
      | A_9 = '#skF_1'
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_6845,c_5375])).

tff(c_7557,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7548,c_6860])).

tff(c_7603,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7557])).

tff(c_7742,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7740,c_7603])).

tff(c_7755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6857,c_7742])).

tff(c_7756,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7557])).

tff(c_7778,plain,
    ( k6_partfun1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7756,c_81])).

tff(c_7785,plain,(
    k5_relat_1('#skF_1','#skF_1') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6872,c_6875,c_6853,c_6869,c_7778])).

tff(c_7081,plain,(
    ! [A_728,B_729] :
      ( v1_funct_1(k2_funct_2(A_728,B_729))
      | ~ m1_subset_1(B_729,k1_zfmisc_1(k2_zfmisc_1(A_728,A_728)))
      | ~ v3_funct_2(B_729,A_728,A_728)
      | ~ v1_funct_2(B_729,A_728,A_728)
      | ~ v1_funct_1(B_729) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_7085,plain,(
    ! [A_728] :
      ( v1_funct_1(k2_funct_2(A_728,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_728,A_728)
      | ~ v1_funct_2('#skF_1',A_728,A_728)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6867,c_7081])).

tff(c_7368,plain,(
    ! [A_771] :
      ( v1_funct_1(k2_funct_2(A_771,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_771,A_771)
      | ~ v1_funct_2('#skF_1',A_771,A_771) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6875,c_7085])).

tff(c_7370,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_6873,c_7368])).

tff(c_7373,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6849,c_7370])).

tff(c_7464,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7463,c_7373])).

tff(c_66,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40) = k5_relat_1(E_39,F_40)
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_7476,plain,(
    ! [A_35,B_36,E_39] :
      ( k1_partfun1(A_35,B_36,'#skF_1','#skF_1',E_39,k2_funct_1('#skF_1')) = k5_relat_1(E_39,k2_funct_1('#skF_1'))
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(resolution,[status(thm)],[c_7473,c_66])).

tff(c_7520,plain,(
    ! [A_35,B_36,E_39] :
      ( k1_partfun1(A_35,B_36,'#skF_1','#skF_1',E_39,k2_funct_1('#skF_1')) = k5_relat_1(E_39,k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7464,c_7476])).

tff(c_8167,plain,(
    ! [A_868,B_869,E_870] :
      ( k1_partfun1(A_868,B_869,'#skF_1','#skF_1',E_870,'#skF_1') = k5_relat_1(E_870,'#skF_1')
      | ~ m1_subset_1(E_870,k1_zfmisc_1(k2_zfmisc_1(A_868,B_869)))
      | ~ v1_funct_1(E_870) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_7756,c_7520])).

tff(c_8174,plain,(
    ! [A_868,B_869] :
      ( k1_partfun1(A_868,B_869,'#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6867,c_8167])).

tff(c_8185,plain,(
    ! [A_868,B_869] : k1_partfun1(A_868,B_869,'#skF_1','#skF_1','#skF_1','#skF_1') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6875,c_7785,c_8174])).

tff(c_6871,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_6845,c_98])).

tff(c_7465,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7463,c_6871])).

tff(c_7762,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_7465])).

tff(c_8188,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8185,c_7762])).

tff(c_8191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7197,c_8188])).

tff(c_8192,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_9536,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9533,c_8192])).

tff(c_10500,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10426,c_9536])).

tff(c_10507,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10500])).

tff(c_10510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8233,c_80,c_8922,c_9553,c_8740,c_10507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:53:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.61/3.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.61/3.16  
% 8.61/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.61/3.16  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.61/3.16  
% 8.61/3.16  %Foreground sorts:
% 8.61/3.16  
% 8.61/3.16  
% 8.61/3.16  %Background operators:
% 8.61/3.16  
% 8.61/3.16  
% 8.61/3.16  %Foreground operators:
% 8.61/3.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.61/3.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.61/3.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.61/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.61/3.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.61/3.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.61/3.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.61/3.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.61/3.16  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 8.61/3.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.61/3.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.61/3.16  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.61/3.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.61/3.17  tff('#skF_2', type, '#skF_2': $i).
% 8.61/3.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.61/3.17  tff('#skF_1', type, '#skF_1': $i).
% 8.61/3.17  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.61/3.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.61/3.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.61/3.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.61/3.17  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.61/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.61/3.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.61/3.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.61/3.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.61/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.61/3.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.61/3.17  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.61/3.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.61/3.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.61/3.17  
% 8.94/3.20  tff(f_174, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 8.94/3.20  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.94/3.20  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 8.94/3.20  tff(f_139, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.94/3.20  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.94/3.20  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 8.94/3.20  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.94/3.20  tff(f_119, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.94/3.20  tff(f_161, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.94/3.20  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 8.94/3.20  tff(f_159, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 8.94/3.20  tff(f_135, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 8.94/3.20  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.94/3.20  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 8.94/3.20  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.94/3.20  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.94/3.20  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.94/3.20  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.94/3.20  tff(c_74, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.94/3.20  tff(c_8216, plain, (![C_879, A_880, B_881]: (v1_relat_1(C_879) | ~m1_subset_1(C_879, k1_zfmisc_1(k2_zfmisc_1(A_880, B_881))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.94/3.20  tff(c_8233, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_8216])).
% 8.94/3.20  tff(c_80, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.94/3.20  tff(c_76, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.94/3.20  tff(c_8903, plain, (![C_977, A_978, B_979]: (v2_funct_1(C_977) | ~v3_funct_2(C_977, A_978, B_979) | ~v1_funct_1(C_977) | ~m1_subset_1(C_977, k1_zfmisc_1(k2_zfmisc_1(A_978, B_979))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.94/3.20  tff(c_8913, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_8903])).
% 8.94/3.20  tff(c_8922, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_8913])).
% 8.94/3.20  tff(c_64, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.94/3.20  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.94/3.20  tff(c_9206, plain, (![A_1002, B_1003, C_1004, D_1005]: (r2_relset_1(A_1002, B_1003, C_1004, C_1004) | ~m1_subset_1(D_1005, k1_zfmisc_1(k2_zfmisc_1(A_1002, B_1003))) | ~m1_subset_1(C_1004, k1_zfmisc_1(k2_zfmisc_1(A_1002, B_1003))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.94/3.20  tff(c_9542, plain, (![A_1034, B_1035, C_1036]: (r2_relset_1(A_1034, B_1035, C_1036, C_1036) | ~m1_subset_1(C_1036, k1_zfmisc_1(k2_zfmisc_1(A_1034, B_1035))))), inference(resolution, [status(thm)], [c_2, c_9206])).
% 8.94/3.20  tff(c_9553, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_64, c_9542])).
% 8.94/3.20  tff(c_8321, plain, (![C_896, B_897, A_898]: (v5_relat_1(C_896, B_897) | ~m1_subset_1(C_896, k1_zfmisc_1(k2_zfmisc_1(A_898, B_897))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.94/3.20  tff(c_8338, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_8321])).
% 8.94/3.20  tff(c_8404, plain, (![B_918, A_919]: (k2_relat_1(B_918)=A_919 | ~v2_funct_2(B_918, A_919) | ~v5_relat_1(B_918, A_919) | ~v1_relat_1(B_918))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.94/3.20  tff(c_8413, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8338, c_8404])).
% 8.94/3.20  tff(c_8422, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8233, c_8413])).
% 8.94/3.20  tff(c_8429, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_8422])).
% 8.94/3.20  tff(c_8718, plain, (![C_954, B_955, A_956]: (v2_funct_2(C_954, B_955) | ~v3_funct_2(C_954, A_956, B_955) | ~v1_funct_1(C_954) | ~m1_subset_1(C_954, k1_zfmisc_1(k2_zfmisc_1(A_956, B_955))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.94/3.20  tff(c_8728, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_8718])).
% 8.94/3.20  tff(c_8737, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_8728])).
% 8.94/3.20  tff(c_8739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8429, c_8737])).
% 8.94/3.20  tff(c_8740, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_8422])).
% 8.94/3.20  tff(c_70, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.94/3.20  tff(c_18, plain, (![A_10]: (k5_relat_1(k2_funct_1(A_10), A_10)=k6_relat_1(k2_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.94/3.20  tff(c_82, plain, (![A_10]: (k5_relat_1(k2_funct_1(A_10), A_10)=k6_partfun1(k2_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_18])).
% 8.94/3.20  tff(c_78, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.94/3.20  tff(c_9514, plain, (![A_1032, B_1033]: (k2_funct_2(A_1032, B_1033)=k2_funct_1(B_1033) | ~m1_subset_1(B_1033, k1_zfmisc_1(k2_zfmisc_1(A_1032, A_1032))) | ~v3_funct_2(B_1033, A_1032, A_1032) | ~v1_funct_2(B_1033, A_1032, A_1032) | ~v1_funct_1(B_1033))), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.94/3.20  tff(c_9524, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_9514])).
% 8.94/3.20  tff(c_9533, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_9524])).
% 8.94/3.20  tff(c_9458, plain, (![A_1029, B_1030]: (v1_funct_1(k2_funct_2(A_1029, B_1030)) | ~m1_subset_1(B_1030, k1_zfmisc_1(k2_zfmisc_1(A_1029, A_1029))) | ~v3_funct_2(B_1030, A_1029, A_1029) | ~v1_funct_2(B_1030, A_1029, A_1029) | ~v1_funct_1(B_1030))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.20  tff(c_9468, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_9458])).
% 8.94/3.20  tff(c_9477, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_9468])).
% 8.94/3.20  tff(c_9535, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9533, c_9477])).
% 8.94/3.20  tff(c_54, plain, (![A_32, B_33]: (m1_subset_1(k2_funct_2(A_32, B_33), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v3_funct_2(B_33, A_32, A_32) | ~v1_funct_2(B_33, A_32, A_32) | ~v1_funct_1(B_33))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.20  tff(c_9909, plain, (![D_1070, F_1067, B_1071, E_1069, C_1068, A_1066]: (k1_partfun1(A_1066, B_1071, C_1068, D_1070, E_1069, F_1067)=k5_relat_1(E_1069, F_1067) | ~m1_subset_1(F_1067, k1_zfmisc_1(k2_zfmisc_1(C_1068, D_1070))) | ~v1_funct_1(F_1067) | ~m1_subset_1(E_1069, k1_zfmisc_1(k2_zfmisc_1(A_1066, B_1071))) | ~v1_funct_1(E_1069))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.94/3.20  tff(c_9920, plain, (![A_1066, B_1071, E_1069]: (k1_partfun1(A_1066, B_1071, '#skF_1', '#skF_1', E_1069, '#skF_2')=k5_relat_1(E_1069, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_1069, k1_zfmisc_1(k2_zfmisc_1(A_1066, B_1071))) | ~v1_funct_1(E_1069))), inference(resolution, [status(thm)], [c_74, c_9909])).
% 8.94/3.20  tff(c_9946, plain, (![A_1072, B_1073, E_1074]: (k1_partfun1(A_1072, B_1073, '#skF_1', '#skF_1', E_1074, '#skF_2')=k5_relat_1(E_1074, '#skF_2') | ~m1_subset_1(E_1074, k1_zfmisc_1(k2_zfmisc_1(A_1072, B_1073))) | ~v1_funct_1(E_1074))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9920])).
% 8.94/3.20  tff(c_10393, plain, (![A_1090, B_1091]: (k1_partfun1(A_1090, A_1090, '#skF_1', '#skF_1', k2_funct_2(A_1090, B_1091), '#skF_2')=k5_relat_1(k2_funct_2(A_1090, B_1091), '#skF_2') | ~v1_funct_1(k2_funct_2(A_1090, B_1091)) | ~m1_subset_1(B_1091, k1_zfmisc_1(k2_zfmisc_1(A_1090, A_1090))) | ~v3_funct_2(B_1091, A_1090, A_1090) | ~v1_funct_2(B_1091, A_1090, A_1090) | ~v1_funct_1(B_1091))), inference(resolution, [status(thm)], [c_54, c_9946])).
% 8.94/3.20  tff(c_10408, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_10393])).
% 8.94/3.20  tff(c_10426, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_9535, c_9533, c_9533, c_9533, c_10408])).
% 8.94/3.20  tff(c_6976, plain, (![A_712, B_713, C_714, D_715]: (r2_relset_1(A_712, B_713, C_714, C_714) | ~m1_subset_1(D_715, k1_zfmisc_1(k2_zfmisc_1(A_712, B_713))) | ~m1_subset_1(C_714, k1_zfmisc_1(k2_zfmisc_1(A_712, B_713))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.94/3.20  tff(c_7187, plain, (![A_740, C_741]: (r2_relset_1(A_740, A_740, C_741, C_741) | ~m1_subset_1(C_741, k1_zfmisc_1(k2_zfmisc_1(A_740, A_740))))), inference(resolution, [status(thm)], [c_64, c_6976])).
% 8.94/3.20  tff(c_7197, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_64, c_7187])).
% 8.94/3.20  tff(c_121, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.94/3.20  tff(c_138, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_121])).
% 8.94/3.20  tff(c_801, plain, (![C_157, A_158, B_159]: (v2_funct_1(C_157) | ~v3_funct_2(C_157, A_158, B_159) | ~v1_funct_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.94/3.20  tff(c_811, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_801])).
% 8.94/3.20  tff(c_820, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_811])).
% 8.94/3.20  tff(c_1229, plain, (![A_194, B_195, C_196, D_197]: (r2_relset_1(A_194, B_195, C_196, C_196) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.94/3.20  tff(c_1442, plain, (![A_215, C_216]: (r2_relset_1(A_215, A_215, C_216, C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_215, A_215))))), inference(resolution, [status(thm)], [c_64, c_1229])).
% 8.94/3.20  tff(c_1453, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_64, c_1442])).
% 8.94/3.20  tff(c_227, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.94/3.20  tff(c_244, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_227])).
% 8.94/3.20  tff(c_307, plain, (![B_92, A_93]: (k2_relat_1(B_92)=A_93 | ~v2_funct_2(B_92, A_93) | ~v5_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.94/3.20  tff(c_316, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_244, c_307])).
% 8.94/3.20  tff(c_325, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_316])).
% 8.94/3.20  tff(c_332, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_325])).
% 8.94/3.20  tff(c_632, plain, (![C_132, B_133, A_134]: (v2_funct_2(C_132, B_133) | ~v3_funct_2(C_132, A_134, B_133) | ~v1_funct_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.94/3.20  tff(c_642, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_632])).
% 8.94/3.20  tff(c_651, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_642])).
% 8.94/3.20  tff(c_653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_332, c_651])).
% 8.94/3.20  tff(c_654, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_325])).
% 8.94/3.20  tff(c_14, plain, (![A_9]: (k2_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.94/3.20  tff(c_147, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_138, c_14])).
% 8.94/3.20  tff(c_168, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_147])).
% 8.94/3.20  tff(c_656, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_654, c_168])).
% 8.94/3.20  tff(c_702, plain, (![A_139, B_140, C_141]: (k1_relset_1(A_139, B_140, C_141)=k1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.94/3.20  tff(c_719, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_702])).
% 8.94/3.20  tff(c_1128, plain, (![B_185, A_186, C_187]: (k1_xboole_0=B_185 | k1_relset_1(A_186, B_185, C_187)=A_186 | ~v1_funct_2(C_187, A_186, B_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.94/3.20  tff(c_1138, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_1128])).
% 8.94/3.20  tff(c_1148, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_719, c_1138])).
% 8.94/3.20  tff(c_1149, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_656, c_1148])).
% 8.94/3.20  tff(c_20, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_relat_1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.94/3.20  tff(c_81, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_partfun1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_20])).
% 8.94/3.20  tff(c_1407, plain, (![A_213, B_214]: (k2_funct_2(A_213, B_214)=k2_funct_1(B_214) | ~m1_subset_1(B_214, k1_zfmisc_1(k2_zfmisc_1(A_213, A_213))) | ~v3_funct_2(B_214, A_213, A_213) | ~v1_funct_2(B_214, A_213, A_213) | ~v1_funct_1(B_214))), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.94/3.20  tff(c_1417, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1407])).
% 8.94/3.20  tff(c_1426, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1417])).
% 8.94/3.20  tff(c_1318, plain, (![A_207, B_208]: (v1_funct_1(k2_funct_2(A_207, B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(k2_zfmisc_1(A_207, A_207))) | ~v3_funct_2(B_208, A_207, A_207) | ~v1_funct_2(B_208, A_207, A_207) | ~v1_funct_1(B_208))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.20  tff(c_1328, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1318])).
% 8.94/3.20  tff(c_1337, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1328])).
% 8.94/3.20  tff(c_1428, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1426, c_1337])).
% 8.94/3.20  tff(c_1662, plain, (![A_239, B_240]: (m1_subset_1(k2_funct_2(A_239, B_240), k1_zfmisc_1(k2_zfmisc_1(A_239, A_239))) | ~m1_subset_1(B_240, k1_zfmisc_1(k2_zfmisc_1(A_239, A_239))) | ~v3_funct_2(B_240, A_239, A_239) | ~v1_funct_2(B_240, A_239, A_239) | ~v1_funct_1(B_240))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.20  tff(c_1718, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1426, c_1662])).
% 8.94/3.20  tff(c_1739, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_1718])).
% 8.94/3.20  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, B_3) | ~m1_subset_1(A_2, k1_zfmisc_1(B_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.94/3.20  tff(c_1815, plain, (r1_tarski(k2_funct_1('#skF_2'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1739, c_4])).
% 8.94/3.20  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.94/3.20  tff(c_1816, plain, (![A_244, B_249, D_248, E_247, C_246, F_245]: (k1_partfun1(A_244, B_249, C_246, D_248, E_247, F_245)=k5_relat_1(E_247, F_245) | ~m1_subset_1(F_245, k1_zfmisc_1(k2_zfmisc_1(C_246, D_248))) | ~v1_funct_1(F_245) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_244, B_249))) | ~v1_funct_1(E_247))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.94/3.20  tff(c_4400, plain, (![A_386, B_385, A_384, E_387, C_388, D_389]: (k1_partfun1(A_384, B_385, C_388, D_389, E_387, A_386)=k5_relat_1(E_387, A_386) | ~v1_funct_1(A_386) | ~m1_subset_1(E_387, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))) | ~v1_funct_1(E_387) | ~r1_tarski(A_386, k2_zfmisc_1(C_388, D_389)))), inference(resolution, [status(thm)], [c_6, c_1816])).
% 8.94/3.20  tff(c_4419, plain, (![C_388, D_389, A_386]: (k1_partfun1('#skF_1', '#skF_1', C_388, D_389, '#skF_2', A_386)=k5_relat_1('#skF_2', A_386) | ~v1_funct_1(A_386) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_386, k2_zfmisc_1(C_388, D_389)))), inference(resolution, [status(thm)], [c_74, c_4400])).
% 8.94/3.20  tff(c_4468, plain, (![C_396, D_397, A_398]: (k1_partfun1('#skF_1', '#skF_1', C_396, D_397, '#skF_2', A_398)=k5_relat_1('#skF_2', A_398) | ~v1_funct_1(A_398) | ~r1_tarski(A_398, k2_zfmisc_1(C_396, D_397)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4419])).
% 8.94/3.20  tff(c_4486, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1815, c_4468])).
% 8.94/3.20  tff(c_4516, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_4486])).
% 8.94/3.20  tff(c_72, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.94/3.20  tff(c_98, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_72])).
% 8.94/3.20  tff(c_1429, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1426, c_98])).
% 8.94/3.20  tff(c_4523, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4516, c_1429])).
% 8.94/3.20  tff(c_4530, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_81, c_4523])).
% 8.94/3.20  tff(c_4533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_80, c_820, c_1453, c_1149, c_4530])).
% 8.94/3.20  tff(c_4534, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_147])).
% 8.94/3.20  tff(c_4542, plain, (![A_1]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_2])).
% 8.94/3.20  tff(c_4976, plain, (![C_489, B_490, A_491]: (v2_funct_2(C_489, B_490) | ~v3_funct_2(C_489, A_491, B_490) | ~v1_funct_1(C_489) | ~m1_subset_1(C_489, k1_zfmisc_1(k2_zfmisc_1(A_491, B_490))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.94/3.20  tff(c_4980, plain, (![B_490, A_491]: (v2_funct_2('#skF_2', B_490) | ~v3_funct_2('#skF_2', A_491, B_490) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_4542, c_4976])).
% 8.94/3.20  tff(c_4993, plain, (![B_492, A_493]: (v2_funct_2('#skF_2', B_492) | ~v3_funct_2('#skF_2', A_493, B_492))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4980])).
% 8.94/3.20  tff(c_4997, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_4993])).
% 8.94/3.20  tff(c_4535, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_147])).
% 8.94/3.20  tff(c_4548, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_4535])).
% 8.94/3.20  tff(c_101, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.94/3.20  tff(c_113, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_101])).
% 8.94/3.20  tff(c_4538, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_113])).
% 8.94/3.20  tff(c_4555, plain, (![B_400, A_401]: (v5_relat_1(B_400, A_401) | ~r1_tarski(k2_relat_1(B_400), A_401) | ~v1_relat_1(B_400))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.94/3.20  tff(c_4558, plain, (![A_401]: (v5_relat_1('#skF_2', A_401) | ~r1_tarski('#skF_2', A_401) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4548, c_4555])).
% 8.94/3.20  tff(c_4560, plain, (![A_401]: (v5_relat_1('#skF_2', A_401))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_4538, c_4558])).
% 8.94/3.20  tff(c_4722, plain, (![B_438, A_439]: (k2_relat_1(B_438)=A_439 | ~v2_funct_2(B_438, A_439) | ~v5_relat_1(B_438, A_439) | ~v1_relat_1(B_438))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.94/3.20  tff(c_4728, plain, (![A_401]: (k2_relat_1('#skF_2')=A_401 | ~v2_funct_2('#skF_2', A_401) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_4560, c_4722])).
% 8.94/3.20  tff(c_4734, plain, (![A_401]: (A_401='#skF_2' | ~v2_funct_2('#skF_2', A_401))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_4548, c_4728])).
% 8.94/3.20  tff(c_5001, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_4997, c_4734])).
% 8.94/3.20  tff(c_16, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.94/3.20  tff(c_146, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_138, c_16])).
% 8.94/3.20  tff(c_167, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_146])).
% 8.94/3.20  tff(c_4536, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_167])).
% 8.94/3.20  tff(c_5018, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_5001, c_4536])).
% 8.94/3.20  tff(c_4767, plain, (![A_449, B_450, C_451]: (k1_relset_1(A_449, B_450, C_451)=k1_relat_1(C_451) | ~m1_subset_1(C_451, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.94/3.20  tff(c_4779, plain, (![A_449, B_450]: (k1_relset_1(A_449, B_450, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_4542, c_4767])).
% 8.94/3.20  tff(c_5006, plain, (![A_449, B_450]: (k1_relset_1(A_449, B_450, '#skF_1')=k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_5001, c_4779])).
% 8.94/3.20  tff(c_5141, plain, (![A_501]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_501)))), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_4542])).
% 8.94/3.20  tff(c_5021, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_4534])).
% 8.94/3.20  tff(c_46, plain, (![B_28, C_29]: (k1_relset_1(k1_xboole_0, B_28, C_29)=k1_xboole_0 | ~v1_funct_2(C_29, k1_xboole_0, B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.94/3.20  tff(c_5128, plain, (![B_28, C_29]: (k1_relset_1('#skF_1', B_28, C_29)='#skF_1' | ~v1_funct_2(C_29, '#skF_1', B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_28))))), inference(demodulation, [status(thm), theory('equality')], [c_5021, c_5021, c_5021, c_5021, c_46])).
% 8.94/3.20  tff(c_5179, plain, (![B_28]: (k1_relset_1('#skF_1', B_28, '#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', B_28))), inference(resolution, [status(thm)], [c_5141, c_5128])).
% 8.94/3.20  tff(c_5366, plain, (![B_28]: (k1_relat_1('#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', B_28))), inference(demodulation, [status(thm), theory('equality')], [c_5006, c_5179])).
% 8.94/3.20  tff(c_5367, plain, (![B_28]: (~v1_funct_2('#skF_1', '#skF_1', B_28))), inference(negUnitSimplification, [status(thm)], [c_5018, c_5366])).
% 8.94/3.20  tff(c_5025, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_78])).
% 8.94/3.20  tff(c_5369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5367, c_5025])).
% 8.94/3.20  tff(c_5370, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_146])).
% 8.94/3.20  tff(c_5377, plain, (![A_1]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_5370, c_2])).
% 8.94/3.20  tff(c_6820, plain, (![C_702, B_703, A_704]: (v2_funct_2(C_702, B_703) | ~v3_funct_2(C_702, A_704, B_703) | ~v1_funct_1(C_702) | ~m1_subset_1(C_702, k1_zfmisc_1(k2_zfmisc_1(A_704, B_703))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.94/3.20  tff(c_6824, plain, (![B_703, A_704]: (v2_funct_2('#skF_2', B_703) | ~v3_funct_2('#skF_2', A_704, B_703) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5377, c_6820])).
% 8.94/3.20  tff(c_6837, plain, (![B_705, A_706]: (v2_funct_2('#skF_2', B_705) | ~v3_funct_2('#skF_2', A_706, B_705))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6824])).
% 8.94/3.20  tff(c_6841, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_6837])).
% 8.94/3.20  tff(c_5371, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_146])).
% 8.94/3.20  tff(c_5383, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5370, c_5371])).
% 8.94/3.20  tff(c_5594, plain, (![A_579, B_580, C_581]: (k1_relset_1(A_579, B_580, C_581)=k1_relat_1(C_581) | ~m1_subset_1(C_581, k1_zfmisc_1(k2_zfmisc_1(A_579, B_580))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.94/3.20  tff(c_5598, plain, (![A_579, B_580]: (k1_relset_1(A_579, B_580, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_5377, c_5594])).
% 8.94/3.20  tff(c_5607, plain, (![A_579, B_580]: (k1_relset_1(A_579, B_580, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5383, c_5598])).
% 8.94/3.20  tff(c_48, plain, (![B_28, A_27, C_29]: (k1_xboole_0=B_28 | k1_relset_1(A_27, B_28, C_29)=A_27 | ~v1_funct_2(C_29, A_27, B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.94/3.20  tff(c_6164, plain, (![B_639, A_640, C_641]: (B_639='#skF_2' | k1_relset_1(A_640, B_639, C_641)=A_640 | ~v1_funct_2(C_641, A_640, B_639) | ~m1_subset_1(C_641, k1_zfmisc_1(k2_zfmisc_1(A_640, B_639))))), inference(demodulation, [status(thm), theory('equality')], [c_5370, c_48])).
% 8.94/3.20  tff(c_6168, plain, (![B_639, A_640]: (B_639='#skF_2' | k1_relset_1(A_640, B_639, '#skF_2')=A_640 | ~v1_funct_2('#skF_2', A_640, B_639))), inference(resolution, [status(thm)], [c_5377, c_6164])).
% 8.94/3.20  tff(c_6384, plain, (![B_656, A_657]: (B_656='#skF_2' | A_657='#skF_2' | ~v1_funct_2('#skF_2', A_657, B_656))), inference(demodulation, [status(thm), theory('equality')], [c_5607, c_6168])).
% 8.94/3.20  tff(c_6398, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_78, c_6384])).
% 8.94/3.20  tff(c_6426, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6398, c_6398, c_5383])).
% 8.94/3.20  tff(c_5824, plain, (![C_609, B_610, A_611]: (v2_funct_2(C_609, B_610) | ~v3_funct_2(C_609, A_611, B_610) | ~v1_funct_1(C_609) | ~m1_subset_1(C_609, k1_zfmisc_1(k2_zfmisc_1(A_611, B_610))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.94/3.20  tff(c_5828, plain, (![B_610, A_611]: (v2_funct_2('#skF_2', B_610) | ~v3_funct_2('#skF_2', A_611, B_610) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5377, c_5824])).
% 8.94/3.20  tff(c_5952, plain, (![B_621, A_622]: (v2_funct_2('#skF_2', B_621) | ~v3_funct_2('#skF_2', A_622, B_621))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5828])).
% 8.94/3.20  tff(c_5956, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_5952])).
% 8.94/3.20  tff(c_5438, plain, (![C_543, B_544, A_545]: (v5_relat_1(C_543, B_544) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_545, B_544))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.94/3.20  tff(c_5450, plain, (![B_544]: (v5_relat_1('#skF_2', B_544))), inference(resolution, [status(thm)], [c_5377, c_5438])).
% 8.94/3.20  tff(c_5558, plain, (![B_574, A_575]: (k2_relat_1(B_574)=A_575 | ~v2_funct_2(B_574, A_575) | ~v5_relat_1(B_574, A_575) | ~v1_relat_1(B_574))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.94/3.20  tff(c_5564, plain, (![B_544]: (k2_relat_1('#skF_2')=B_544 | ~v2_funct_2('#skF_2', B_544) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_5450, c_5558])).
% 8.94/3.20  tff(c_5570, plain, (![B_544]: (k2_relat_1('#skF_2')=B_544 | ~v2_funct_2('#skF_2', B_544))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_5564])).
% 8.94/3.20  tff(c_5960, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_5956, c_5570])).
% 8.94/3.20  tff(c_5502, plain, (![B_558, A_559]: (r1_tarski(k2_relat_1(B_558), A_559) | ~v5_relat_1(B_558, A_559) | ~v1_relat_1(B_558))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.94/3.20  tff(c_137, plain, (![A_2, A_58, B_59]: (v1_relat_1(A_2) | ~r1_tarski(A_2, k2_zfmisc_1(A_58, B_59)))), inference(resolution, [status(thm)], [c_6, c_121])).
% 8.94/3.20  tff(c_5543, plain, (![B_571, A_572, B_573]: (v1_relat_1(k2_relat_1(B_571)) | ~v5_relat_1(B_571, k2_zfmisc_1(A_572, B_573)) | ~v1_relat_1(B_571))), inference(resolution, [status(thm)], [c_5502, c_137])).
% 8.94/3.20  tff(c_5551, plain, (v1_relat_1(k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_5450, c_5543])).
% 8.94/3.20  tff(c_5557, plain, (v1_relat_1(k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_5551])).
% 8.94/3.20  tff(c_5374, plain, (![A_9]: (k1_relat_1(A_9)!='#skF_2' | A_9='#skF_2' | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_5370, c_5370, c_16])).
% 8.94/3.20  tff(c_5578, plain, (k1_relat_1(k2_relat_1('#skF_2'))!='#skF_2' | k2_relat_1('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_5557, c_5374])).
% 8.94/3.20  tff(c_5617, plain, (k1_relat_1(k2_relat_1('#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_5578])).
% 8.94/3.20  tff(c_5974, plain, (k1_relat_1('#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5960, c_5617])).
% 8.94/3.20  tff(c_6406, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6398, c_5974])).
% 8.94/3.20  tff(c_6554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6426, c_6406])).
% 8.94/3.20  tff(c_6555, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_5578])).
% 8.94/3.20  tff(c_6557, plain, (![B_544]: (B_544='#skF_2' | ~v2_funct_2('#skF_2', B_544))), inference(demodulation, [status(thm), theory('equality')], [c_6555, c_5570])).
% 8.94/3.20  tff(c_6845, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_6841, c_6557])).
% 8.94/3.20  tff(c_6875, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_80])).
% 8.94/3.20  tff(c_6872, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_138])).
% 8.94/3.20  tff(c_6645, plain, (![C_669, A_670, B_671]: (v2_funct_1(C_669) | ~v3_funct_2(C_669, A_670, B_671) | ~v1_funct_1(C_669) | ~m1_subset_1(C_669, k1_zfmisc_1(k2_zfmisc_1(A_670, B_671))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.94/3.20  tff(c_6649, plain, (![A_670, B_671]: (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', A_670, B_671) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5377, c_6645])).
% 8.94/3.20  tff(c_6659, plain, (![A_670, B_671]: (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', A_670, B_671))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6649])).
% 8.94/3.20  tff(c_6662, plain, (![A_670, B_671]: (~v3_funct_2('#skF_2', A_670, B_671))), inference(splitLeft, [status(thm)], [c_6659])).
% 8.94/3.20  tff(c_6664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6662, c_76])).
% 8.94/3.20  tff(c_6665, plain, (v2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_6659])).
% 8.94/3.20  tff(c_6853, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_6665])).
% 8.94/3.20  tff(c_6869, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_6845, c_5383])).
% 8.94/3.20  tff(c_6857, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_6845, c_6555])).
% 8.94/3.20  tff(c_42, plain, (![C_29, B_28]: (v1_funct_2(C_29, k1_xboole_0, B_28) | k1_relset_1(k1_xboole_0, B_28, C_29)!=k1_xboole_0 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.94/3.20  tff(c_6790, plain, (![C_695, B_696]: (v1_funct_2(C_695, '#skF_2', B_696) | k1_relset_1('#skF_2', B_696, C_695)!='#skF_2' | ~m1_subset_1(C_695, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_696))))), inference(demodulation, [status(thm), theory('equality')], [c_5370, c_5370, c_5370, c_5370, c_42])).
% 8.94/3.20  tff(c_6794, plain, (![B_696]: (v1_funct_2('#skF_2', '#skF_2', B_696) | k1_relset_1('#skF_2', B_696, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_5377, c_6790])).
% 8.94/3.20  tff(c_6805, plain, (![B_696]: (v1_funct_2('#skF_2', '#skF_2', B_696))), inference(demodulation, [status(thm), theory('equality')], [c_5607, c_6794])).
% 8.94/3.20  tff(c_6849, plain, (![B_696]: (v1_funct_2('#skF_1', '#skF_1', B_696))), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_6845, c_6805])).
% 8.94/3.20  tff(c_6873, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_76])).
% 8.94/3.20  tff(c_6867, plain, (![A_1]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_5377])).
% 8.94/3.20  tff(c_7100, plain, (![A_730, B_731]: (k2_funct_2(A_730, B_731)=k2_funct_1(B_731) | ~m1_subset_1(B_731, k1_zfmisc_1(k2_zfmisc_1(A_730, A_730))) | ~v3_funct_2(B_731, A_730, A_730) | ~v1_funct_2(B_731, A_730, A_730) | ~v1_funct_1(B_731))), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.94/3.20  tff(c_7104, plain, (![A_730]: (k2_funct_2(A_730, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_730, A_730) | ~v1_funct_2('#skF_1', A_730, A_730) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_6867, c_7100])).
% 8.94/3.20  tff(c_7457, plain, (![A_792]: (k2_funct_2(A_792, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_792, A_792) | ~v1_funct_2('#skF_1', A_792, A_792))), inference(demodulation, [status(thm), theory('equality')], [c_6875, c_7104])).
% 8.94/3.20  tff(c_7460, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_6873, c_7457])).
% 8.94/3.20  tff(c_7463, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6849, c_7460])).
% 8.94/3.20  tff(c_7469, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7463, c_54])).
% 8.94/3.20  tff(c_7473, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6875, c_6849, c_6873, c_6867, c_7469])).
% 8.94/3.20  tff(c_22, plain, (![C_13, A_11, B_12]: (v1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.94/3.20  tff(c_7548, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_7473, c_22])).
% 8.94/3.20  tff(c_6861, plain, (![A_9]: (k1_relat_1(A_9)!='#skF_1' | A_9='#skF_1' | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_6845, c_5374])).
% 8.94/3.20  tff(c_7556, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_7548, c_6861])).
% 8.94/3.20  tff(c_7606, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_7556])).
% 8.94/3.20  tff(c_28, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.94/3.20  tff(c_7544, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_7473, c_28])).
% 8.94/3.20  tff(c_7549, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_7473, c_4])).
% 8.94/3.20  tff(c_6733, plain, (![B_684, C_685]: (k1_relset_1('#skF_2', B_684, C_685)='#skF_2' | ~v1_funct_2(C_685, '#skF_2', B_684) | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_684))))), inference(demodulation, [status(thm), theory('equality')], [c_5370, c_5370, c_5370, c_5370, c_46])).
% 8.94/3.20  tff(c_6750, plain, (![B_684, A_2]: (k1_relset_1('#skF_2', B_684, A_2)='#skF_2' | ~v1_funct_2(A_2, '#skF_2', B_684) | ~r1_tarski(A_2, k2_zfmisc_1('#skF_2', B_684)))), inference(resolution, [status(thm)], [c_6, c_6733])).
% 8.94/3.20  tff(c_7678, plain, (![B_801, A_802]: (k1_relset_1('#skF_1', B_801, A_802)='#skF_1' | ~v1_funct_2(A_802, '#skF_1', B_801) | ~r1_tarski(A_802, k2_zfmisc_1('#skF_1', B_801)))), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_6845, c_6845, c_6845, c_6750])).
% 8.94/3.20  tff(c_7681, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_7549, c_7678])).
% 8.94/3.20  tff(c_7695, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7544, c_7681])).
% 8.94/3.20  tff(c_7696, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_7606, c_7695])).
% 8.94/3.20  tff(c_7199, plain, (![A_742, B_743]: (v1_funct_2(k2_funct_2(A_742, B_743), A_742, A_742) | ~m1_subset_1(B_743, k1_zfmisc_1(k2_zfmisc_1(A_742, A_742))) | ~v3_funct_2(B_743, A_742, A_742) | ~v1_funct_2(B_743, A_742, A_742) | ~v1_funct_1(B_743))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.20  tff(c_7202, plain, (![A_742]: (v1_funct_2(k2_funct_2(A_742, '#skF_1'), A_742, A_742) | ~v3_funct_2('#skF_1', A_742, A_742) | ~v1_funct_2('#skF_1', A_742, A_742) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_6867, c_7199])).
% 8.94/3.20  tff(c_7732, plain, (![A_808]: (v1_funct_2(k2_funct_2(A_808, '#skF_1'), A_808, A_808) | ~v3_funct_2('#skF_1', A_808, A_808) | ~v1_funct_2('#skF_1', A_808, A_808))), inference(demodulation, [status(thm), theory('equality')], [c_6875, c_7202])).
% 8.94/3.20  tff(c_7735, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7463, c_7732])).
% 8.94/3.20  tff(c_7737, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6849, c_6873, c_7735])).
% 8.94/3.20  tff(c_7739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7696, c_7737])).
% 8.94/3.20  tff(c_7740, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_7556])).
% 8.94/3.20  tff(c_5375, plain, (![A_9]: (k2_relat_1(A_9)!='#skF_2' | A_9='#skF_2' | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_5370, c_5370, c_14])).
% 8.94/3.20  tff(c_6860, plain, (![A_9]: (k2_relat_1(A_9)!='#skF_1' | A_9='#skF_1' | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_6845, c_5375])).
% 8.94/3.20  tff(c_7557, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_7548, c_6860])).
% 8.94/3.20  tff(c_7603, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_7557])).
% 8.94/3.20  tff(c_7742, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7740, c_7603])).
% 8.94/3.20  tff(c_7755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6857, c_7742])).
% 8.94/3.20  tff(c_7756, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_7557])).
% 8.94/3.20  tff(c_7778, plain, (k6_partfun1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7756, c_81])).
% 8.94/3.20  tff(c_7785, plain, (k5_relat_1('#skF_1', '#skF_1')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6872, c_6875, c_6853, c_6869, c_7778])).
% 8.94/3.20  tff(c_7081, plain, (![A_728, B_729]: (v1_funct_1(k2_funct_2(A_728, B_729)) | ~m1_subset_1(B_729, k1_zfmisc_1(k2_zfmisc_1(A_728, A_728))) | ~v3_funct_2(B_729, A_728, A_728) | ~v1_funct_2(B_729, A_728, A_728) | ~v1_funct_1(B_729))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.20  tff(c_7085, plain, (![A_728]: (v1_funct_1(k2_funct_2(A_728, '#skF_1')) | ~v3_funct_2('#skF_1', A_728, A_728) | ~v1_funct_2('#skF_1', A_728, A_728) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_6867, c_7081])).
% 8.94/3.20  tff(c_7368, plain, (![A_771]: (v1_funct_1(k2_funct_2(A_771, '#skF_1')) | ~v3_funct_2('#skF_1', A_771, A_771) | ~v1_funct_2('#skF_1', A_771, A_771))), inference(demodulation, [status(thm), theory('equality')], [c_6875, c_7085])).
% 8.94/3.20  tff(c_7370, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_6873, c_7368])).
% 8.94/3.20  tff(c_7373, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6849, c_7370])).
% 8.94/3.20  tff(c_7464, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7463, c_7373])).
% 8.94/3.20  tff(c_66, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40)=k5_relat_1(E_39, F_40) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.94/3.20  tff(c_7476, plain, (![A_35, B_36, E_39]: (k1_partfun1(A_35, B_36, '#skF_1', '#skF_1', E_39, k2_funct_1('#skF_1'))=k5_relat_1(E_39, k2_funct_1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(resolution, [status(thm)], [c_7473, c_66])).
% 8.94/3.20  tff(c_7520, plain, (![A_35, B_36, E_39]: (k1_partfun1(A_35, B_36, '#skF_1', '#skF_1', E_39, k2_funct_1('#skF_1'))=k5_relat_1(E_39, k2_funct_1('#skF_1')) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(demodulation, [status(thm), theory('equality')], [c_7464, c_7476])).
% 8.94/3.20  tff(c_8167, plain, (![A_868, B_869, E_870]: (k1_partfun1(A_868, B_869, '#skF_1', '#skF_1', E_870, '#skF_1')=k5_relat_1(E_870, '#skF_1') | ~m1_subset_1(E_870, k1_zfmisc_1(k2_zfmisc_1(A_868, B_869))) | ~v1_funct_1(E_870))), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_7756, c_7520])).
% 8.94/3.20  tff(c_8174, plain, (![A_868, B_869]: (k1_partfun1(A_868, B_869, '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_6867, c_8167])).
% 8.94/3.20  tff(c_8185, plain, (![A_868, B_869]: (k1_partfun1(A_868, B_869, '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6875, c_7785, c_8174])).
% 8.94/3.20  tff(c_6871, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_6845, c_98])).
% 8.94/3.20  tff(c_7465, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7463, c_6871])).
% 8.94/3.20  tff(c_7762, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_7465])).
% 8.94/3.20  tff(c_8188, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8185, c_7762])).
% 8.94/3.20  tff(c_8191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7197, c_8188])).
% 8.94/3.20  tff(c_8192, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_72])).
% 8.94/3.20  tff(c_9536, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9533, c_8192])).
% 8.94/3.20  tff(c_10500, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10426, c_9536])).
% 8.94/3.20  tff(c_10507, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_82, c_10500])).
% 8.94/3.20  tff(c_10510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8233, c_80, c_8922, c_9553, c_8740, c_10507])).
% 8.94/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.94/3.20  
% 8.94/3.20  Inference rules
% 8.94/3.20  ----------------------
% 8.94/3.20  #Ref     : 0
% 8.94/3.20  #Sup     : 1912
% 8.94/3.20  #Fact    : 0
% 8.94/3.20  #Define  : 0
% 8.94/3.20  #Split   : 49
% 8.94/3.20  #Chain   : 0
% 8.94/3.20  #Close   : 0
% 8.94/3.20  
% 8.94/3.20  Ordering : KBO
% 8.94/3.20  
% 8.94/3.20  Simplification rules
% 8.94/3.20  ----------------------
% 8.94/3.20  #Subsume      : 207
% 8.94/3.20  #Demod        : 2237
% 8.94/3.20  #Tautology    : 677
% 8.94/3.20  #SimpNegUnit  : 81
% 8.94/3.20  #BackRed      : 209
% 8.94/3.20  
% 8.94/3.20  #Partial instantiations: 0
% 8.94/3.20  #Strategies tried      : 1
% 8.94/3.20  
% 8.94/3.20  Timing (in seconds)
% 8.94/3.20  ----------------------
% 9.07/3.20  Preprocessing        : 0.37
% 9.07/3.20  Parsing              : 0.19
% 9.07/3.20  CNF conversion       : 0.02
% 9.07/3.20  Main loop            : 1.99
% 9.07/3.21  Inferencing          : 0.66
% 9.07/3.21  Reduction            : 0.76
% 9.07/3.21  Demodulation         : 0.55
% 9.07/3.21  BG Simplification    : 0.07
% 9.07/3.21  Subsumption          : 0.33
% 9.07/3.21  Abstraction          : 0.07
% 9.07/3.21  MUC search           : 0.00
% 9.07/3.21  Cooper               : 0.00
% 9.07/3.21  Total                : 2.45
% 9.07/3.21  Index Insertion      : 0.00
% 9.07/3.21  Index Deletion       : 0.00
% 9.07/3.21  Index Matching       : 0.00
% 9.07/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

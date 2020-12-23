%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:28 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  135 (3696 expanded)
%              Number of leaves         :   37 (1328 expanded)
%              Depth                    :   16
%              Number of atoms          :  235 (11528 expanded)
%              Number of equality atoms :   94 (4362 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_58,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_66,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_58])).

tff(c_52,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_65,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_58])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_46])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_96,c_4])).

tff(c_102,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_426,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_430,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_426])).

tff(c_44,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_91,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_44])).

tff(c_435,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_91])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_71,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_48])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_71])).

tff(c_444,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_72])).

tff(c_421,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_425,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_421])).

tff(c_441,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_425])).

tff(c_442,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_96])).

tff(c_500,plain,(
    ! [B_94,A_95,C_96] :
      ( k1_xboole_0 = B_94
      | k1_relset_1(A_95,B_94,C_96) = A_95
      | ~ v1_funct_2(C_96,A_95,B_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_503,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_442,c_500])).

tff(c_506,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_441,c_503])).

tff(c_514,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_520,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_444])).

tff(c_440,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_430])).

tff(c_517,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_440])).

tff(c_519,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_442])).

tff(c_604,plain,(
    ! [C_106,B_107,A_108] :
      ( m1_subset_1(k2_funct_1(C_106),k1_zfmisc_1(k2_zfmisc_1(B_107,A_108)))
      | k2_relset_1(A_108,B_107,C_106) != B_107
      | ~ v2_funct_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_2(C_106,A_108,B_107)
      | ~ v1_funct_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_696,plain,(
    ! [B_115,A_116,C_117] :
      ( k2_relset_1(B_115,A_116,k2_funct_1(C_117)) = k2_relat_1(k2_funct_1(C_117))
      | k2_relset_1(A_116,B_115,C_117) != B_115
      | ~ v2_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115)))
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ v1_funct_1(C_117) ) ),
    inference(resolution,[status(thm)],[c_604,c_14])).

tff(c_702,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_519,c_696])).

tff(c_706,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_520,c_42,c_517,c_702])).

tff(c_591,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_tops_2(A_103,B_104,C_105) = k2_funct_1(C_105)
      | ~ v2_funct_1(C_105)
      | k2_relset_1(A_103,B_104,C_105) != B_104
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_2(C_105,A_103,B_104)
      | ~ v1_funct_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_594,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_519,c_591])).

tff(c_597,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_520,c_517,c_42,c_594])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_relset_1(A_39,B_40,C_41) = k2_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_132])).

tff(c_137,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_91])).

tff(c_146,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_72])).

tff(c_123,plain,(
    ! [A_36,B_37,C_38] :
      ( k1_relset_1(A_36,B_37,C_38) = k1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_123])).

tff(c_143,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_127])).

tff(c_144,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_96])).

tff(c_197,plain,(
    ! [B_52,A_53,C_54] :
      ( k1_xboole_0 = B_52
      | k1_relset_1(A_53,B_52,C_54) = A_53
      | ~ v1_funct_2(C_54,A_53,B_52)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_200,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_144,c_197])).

tff(c_203,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_143,c_200])).

tff(c_204,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_209,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_146])).

tff(c_142,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_136])).

tff(c_206,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_142])).

tff(c_208,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_144])).

tff(c_289,plain,(
    ! [C_64,B_65,A_66] :
      ( m1_subset_1(k2_funct_1(C_64),k1_zfmisc_1(k2_zfmisc_1(B_65,A_66)))
      | k2_relset_1(A_66,B_65,C_64) != B_65
      | ~ v2_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65)))
      | ~ v1_funct_2(C_64,A_66,B_65)
      | ~ v1_funct_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_365,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_relset_1(B_73,A_74,k2_funct_1(C_75)) = k1_relat_1(k2_funct_1(C_75))
      | k2_relset_1(A_74,B_73,C_75) != B_73
      | ~ v2_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73)))
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ v1_funct_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_289,c_12])).

tff(c_371,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_208,c_365])).

tff(c_375,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_209,c_42,c_206,c_371])).

tff(c_277,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_tops_2(A_61,B_62,C_63) = k2_funct_1(C_63)
      | ~ v2_funct_1(C_63)
      | k2_relset_1(A_61,B_62,C_63) != B_62
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(C_63,A_61,B_62)
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_280,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_208,c_277])).

tff(c_283,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_209,c_206,c_42,c_280])).

tff(c_40,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_103,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_65,c_65,c_66,c_66,c_65,c_65,c_40])).

tff(c_104,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_187,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_137,c_137,c_104])).

tff(c_205,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_204,c_187])).

tff(c_284,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_205])).

tff(c_376,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_284])).

tff(c_383,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_376])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_50,c_42,c_383])).

tff(c_388,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_77,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_83,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_77])).

tff(c_87,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_83])).

tff(c_88,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_87])).

tff(c_145,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_88])).

tff(c_396,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_145])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_396])).

tff(c_401,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_485,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_435,c_401])).

tff(c_516,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_514,c_514,c_485])).

tff(c_598,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_516])).

tff(c_707,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_598])).

tff(c_714,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_707])).

tff(c_718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_50,c_42,c_714])).

tff(c_719,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_443,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_88])).

tff(c_735,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_443])).

tff(c_739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:16:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.44  
% 3.00/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.44  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.00/1.44  
% 3.00/1.44  %Foreground sorts:
% 3.00/1.44  
% 3.00/1.44  
% 3.00/1.44  %Background operators:
% 3.00/1.44  
% 3.00/1.44  
% 3.00/1.44  %Foreground operators:
% 3.00/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.00/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.00/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.00/1.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.00/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.00/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.44  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.00/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.00/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.44  tff('#skF_1', type, '#skF_1': $i).
% 3.00/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.00/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.00/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.00/1.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.00/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.44  
% 3.00/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.00/1.46  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.00/1.46  tff(f_135, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.00/1.46  tff(f_91, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.00/1.46  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.00/1.46  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.00/1.46  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.00/1.46  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.00/1.46  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.00/1.46  tff(f_87, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.00/1.46  tff(f_111, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.00/1.46  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.00/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.00/1.46  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.46  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.00/1.46  tff(c_58, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.00/1.46  tff(c_66, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_58])).
% 3.00/1.46  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.00/1.46  tff(c_65, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_58])).
% 3.00/1.46  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.00/1.46  tff(c_96, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_46])).
% 3.00/1.46  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.00/1.46  tff(c_99, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_96, c_4])).
% 3.00/1.46  tff(c_102, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_99])).
% 3.00/1.46  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.00/1.46  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.00/1.46  tff(c_8, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.46  tff(c_426, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.46  tff(c_430, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_426])).
% 3.00/1.46  tff(c_44, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.00/1.46  tff(c_91, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_44])).
% 3.00/1.46  tff(c_435, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_91])).
% 3.00/1.46  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.00/1.46  tff(c_71, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_48])).
% 3.00/1.46  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_71])).
% 3.00/1.46  tff(c_444, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_72])).
% 3.00/1.46  tff(c_421, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.46  tff(c_425, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_421])).
% 3.00/1.46  tff(c_441, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_425])).
% 3.00/1.46  tff(c_442, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_96])).
% 3.00/1.46  tff(c_500, plain, (![B_94, A_95, C_96]: (k1_xboole_0=B_94 | k1_relset_1(A_95, B_94, C_96)=A_95 | ~v1_funct_2(C_96, A_95, B_94) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.00/1.46  tff(c_503, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_442, c_500])).
% 3.00/1.46  tff(c_506, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_441, c_503])).
% 3.00/1.46  tff(c_514, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_506])).
% 3.00/1.46  tff(c_520, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_514, c_444])).
% 3.00/1.46  tff(c_440, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_430])).
% 3.00/1.46  tff(c_517, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_440])).
% 3.00/1.46  tff(c_519, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_514, c_442])).
% 3.00/1.46  tff(c_604, plain, (![C_106, B_107, A_108]: (m1_subset_1(k2_funct_1(C_106), k1_zfmisc_1(k2_zfmisc_1(B_107, A_108))) | k2_relset_1(A_108, B_107, C_106)!=B_107 | ~v2_funct_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_2(C_106, A_108, B_107) | ~v1_funct_1(C_106))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.00/1.46  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.46  tff(c_696, plain, (![B_115, A_116, C_117]: (k2_relset_1(B_115, A_116, k2_funct_1(C_117))=k2_relat_1(k2_funct_1(C_117)) | k2_relset_1(A_116, B_115, C_117)!=B_115 | ~v2_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))) | ~v1_funct_2(C_117, A_116, B_115) | ~v1_funct_1(C_117))), inference(resolution, [status(thm)], [c_604, c_14])).
% 3.00/1.46  tff(c_702, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_519, c_696])).
% 3.00/1.46  tff(c_706, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_520, c_42, c_517, c_702])).
% 3.00/1.46  tff(c_591, plain, (![A_103, B_104, C_105]: (k2_tops_2(A_103, B_104, C_105)=k2_funct_1(C_105) | ~v2_funct_1(C_105) | k2_relset_1(A_103, B_104, C_105)!=B_104 | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_2(C_105, A_103, B_104) | ~v1_funct_1(C_105))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.00/1.46  tff(c_594, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_519, c_591])).
% 3.00/1.46  tff(c_597, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_520, c_517, c_42, c_594])).
% 3.00/1.46  tff(c_10, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.46  tff(c_132, plain, (![A_39, B_40, C_41]: (k2_relset_1(A_39, B_40, C_41)=k2_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.46  tff(c_136, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_132])).
% 3.00/1.46  tff(c_137, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_91])).
% 3.00/1.46  tff(c_146, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_72])).
% 3.00/1.46  tff(c_123, plain, (![A_36, B_37, C_38]: (k1_relset_1(A_36, B_37, C_38)=k1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.46  tff(c_127, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_123])).
% 3.00/1.46  tff(c_143, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_127])).
% 3.00/1.46  tff(c_144, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_96])).
% 3.00/1.46  tff(c_197, plain, (![B_52, A_53, C_54]: (k1_xboole_0=B_52 | k1_relset_1(A_53, B_52, C_54)=A_53 | ~v1_funct_2(C_54, A_53, B_52) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.00/1.46  tff(c_200, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_144, c_197])).
% 3.00/1.46  tff(c_203, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_143, c_200])).
% 3.00/1.46  tff(c_204, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_203])).
% 3.00/1.46  tff(c_209, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_146])).
% 3.00/1.46  tff(c_142, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_136])).
% 3.00/1.46  tff(c_206, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_142])).
% 3.00/1.46  tff(c_208, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_144])).
% 3.00/1.46  tff(c_289, plain, (![C_64, B_65, A_66]: (m1_subset_1(k2_funct_1(C_64), k1_zfmisc_1(k2_zfmisc_1(B_65, A_66))) | k2_relset_1(A_66, B_65, C_64)!=B_65 | ~v2_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))) | ~v1_funct_2(C_64, A_66, B_65) | ~v1_funct_1(C_64))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.00/1.46  tff(c_12, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.46  tff(c_365, plain, (![B_73, A_74, C_75]: (k1_relset_1(B_73, A_74, k2_funct_1(C_75))=k1_relat_1(k2_funct_1(C_75)) | k2_relset_1(A_74, B_73, C_75)!=B_73 | ~v2_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))) | ~v1_funct_2(C_75, A_74, B_73) | ~v1_funct_1(C_75))), inference(resolution, [status(thm)], [c_289, c_12])).
% 3.00/1.46  tff(c_371, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_208, c_365])).
% 3.00/1.46  tff(c_375, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_209, c_42, c_206, c_371])).
% 3.00/1.46  tff(c_277, plain, (![A_61, B_62, C_63]: (k2_tops_2(A_61, B_62, C_63)=k2_funct_1(C_63) | ~v2_funct_1(C_63) | k2_relset_1(A_61, B_62, C_63)!=B_62 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(C_63, A_61, B_62) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.00/1.46  tff(c_280, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_208, c_277])).
% 3.00/1.46  tff(c_283, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_209, c_206, c_42, c_280])).
% 3.00/1.46  tff(c_40, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.00/1.46  tff(c_103, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_65, c_65, c_66, c_66, c_65, c_65, c_40])).
% 3.00/1.46  tff(c_104, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_103])).
% 3.00/1.46  tff(c_187, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_137, c_137, c_104])).
% 3.00/1.46  tff(c_205, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_204, c_187])).
% 3.00/1.46  tff(c_284, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_205])).
% 3.00/1.46  tff(c_376, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_375, c_284])).
% 3.00/1.46  tff(c_383, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_376])).
% 3.00/1.46  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_50, c_42, c_383])).
% 3.00/1.46  tff(c_388, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_203])).
% 3.00/1.46  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.00/1.46  tff(c_77, plain, (![A_31]: (~v1_xboole_0(u1_struct_0(A_31)) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.00/1.46  tff(c_83, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_65, c_77])).
% 3.00/1.46  tff(c_87, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_83])).
% 3.00/1.46  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_87])).
% 3.00/1.46  tff(c_145, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_88])).
% 3.00/1.46  tff(c_396, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_388, c_145])).
% 3.00/1.46  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_396])).
% 3.00/1.46  tff(c_401, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_103])).
% 3.00/1.46  tff(c_485, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_435, c_401])).
% 3.00/1.46  tff(c_516, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_514, c_514, c_485])).
% 3.00/1.46  tff(c_598, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_516])).
% 3.00/1.46  tff(c_707, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_706, c_598])).
% 3.00/1.46  tff(c_714, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_707])).
% 3.00/1.46  tff(c_718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_50, c_42, c_714])).
% 3.00/1.46  tff(c_719, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_506])).
% 3.00/1.46  tff(c_443, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_88])).
% 3.00/1.46  tff(c_735, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_719, c_443])).
% 3.00/1.46  tff(c_739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_735])).
% 3.00/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.46  
% 3.00/1.46  Inference rules
% 3.00/1.46  ----------------------
% 3.00/1.46  #Ref     : 0
% 3.00/1.46  #Sup     : 151
% 3.00/1.46  #Fact    : 0
% 3.00/1.46  #Define  : 0
% 3.00/1.46  #Split   : 4
% 3.00/1.46  #Chain   : 0
% 3.00/1.46  #Close   : 0
% 3.00/1.46  
% 3.00/1.46  Ordering : KBO
% 3.00/1.46  
% 3.00/1.46  Simplification rules
% 3.00/1.46  ----------------------
% 3.00/1.46  #Subsume      : 8
% 3.00/1.46  #Demod        : 194
% 3.00/1.46  #Tautology    : 93
% 3.00/1.46  #SimpNegUnit  : 3
% 3.00/1.46  #BackRed      : 52
% 3.00/1.46  
% 3.00/1.46  #Partial instantiations: 0
% 3.00/1.46  #Strategies tried      : 1
% 3.00/1.46  
% 3.00/1.46  Timing (in seconds)
% 3.00/1.46  ----------------------
% 3.00/1.46  Preprocessing        : 0.33
% 3.00/1.46  Parsing              : 0.18
% 3.00/1.46  CNF conversion       : 0.02
% 3.00/1.46  Main loop            : 0.35
% 3.31/1.46  Inferencing          : 0.12
% 3.31/1.47  Reduction            : 0.12
% 3.31/1.47  Demodulation         : 0.09
% 3.31/1.47  BG Simplification    : 0.02
% 3.31/1.47  Subsumption          : 0.06
% 3.31/1.47  Abstraction          : 0.02
% 3.31/1.47  MUC search           : 0.00
% 3.31/1.47  Cooper               : 0.00
% 3.31/1.47  Total                : 0.73
% 3.31/1.47  Index Insertion      : 0.00
% 3.31/1.47  Index Deletion       : 0.00
% 3.31/1.47  Index Matching       : 0.00
% 3.31/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:22 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  140 (2819 expanded)
%              Number of leaves         :   42 (1031 expanded)
%              Depth                    :   18
%              Number of atoms          :  272 (8942 expanded)
%              Number of equality atoms :  114 (3308 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_144,negated_conjecture,(
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

tff(f_100,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_64,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_30,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_80,axiom,(
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

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_56,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_86,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_94,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_86])).

tff(c_52,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_93,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_86])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_117,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_93,c_46])).

tff(c_124,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_128,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_124])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_8,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_13] : k6_relat_1(A_13) = k6_partfun1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_57,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_147,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_relset_1(A_39,B_40,C_41) = k2_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_151,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_147])).

tff(c_44,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_119,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_93,c_44])).

tff(c_157,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_119])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_95,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_48])).

tff(c_104,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95])).

tff(c_165,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_104])).

tff(c_162,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_151])).

tff(c_164,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_117])).

tff(c_610,plain,(
    ! [A_91,C_92,B_93] :
      ( k6_partfun1(A_91) = k5_relat_1(C_92,k2_funct_1(C_92))
      | k1_xboole_0 = B_93
      | ~ v2_funct_1(C_92)
      | k2_relset_1(A_91,B_93,C_92) != B_93
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_93)))
      | ~ v1_funct_2(C_92,A_91,B_93)
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_614,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_610])).

tff(c_618,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_165,c_162,c_42,c_614])).

tff(c_619,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_105,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(u1_struct_0(A_33))
      | ~ l1_struct_0(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_111,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_105])).

tff(c_115,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_111])).

tff(c_116,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_115])).

tff(c_163,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_116])).

tff(c_629,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_163])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_629])).

tff(c_634,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_relat_1(k5_relat_1(A_3,k2_funct_1(A_3))) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_648,plain,
    ( k2_relat_1(k6_partfun1(k2_struct_0('#skF_1'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_12])).

tff(c_655,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_50,c_42,c_57,c_648])).

tff(c_664,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_162])).

tff(c_667,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_165])).

tff(c_665,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_164])).

tff(c_574,plain,(
    ! [C_85,B_86,A_87] :
      ( m1_subset_1(k2_funct_1(C_85),k1_zfmisc_1(k2_zfmisc_1(B_86,A_87)))
      | k2_relset_1(A_87,B_86,C_85) != B_86
      | ~ v2_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86)))
      | ~ v1_funct_2(C_85,A_87,B_86)
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_597,plain,(
    ! [B_86,A_87,C_85] :
      ( k2_relset_1(B_86,A_87,k2_funct_1(C_85)) = k2_relat_1(k2_funct_1(C_85))
      | k2_relset_1(A_87,B_86,C_85) != B_86
      | ~ v2_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86)))
      | ~ v1_funct_2(C_85,A_87,B_86)
      | ~ v1_funct_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_574,c_20])).

tff(c_705,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_665,c_597])).

tff(c_733,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_667,c_42,c_705])).

tff(c_813,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_733])).

tff(c_557,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_tops_2(A_82,B_83,C_84) = k2_funct_1(C_84)
      | ~ v2_funct_1(C_84)
      | k2_relset_1(A_82,B_83,C_84) != B_83
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(C_84,A_82,B_83)
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_560,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_557])).

tff(c_563,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_165,c_162,c_42,c_560])).

tff(c_166,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_93])).

tff(c_10,plain,(
    ! [A_2] :
      ( k1_relat_1(k2_funct_1(A_2)) = k2_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_58,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4])).

tff(c_288,plain,(
    ! [B_62,C_63,A_64] :
      ( k6_partfun1(B_62) = k5_relat_1(k2_funct_1(C_63),C_63)
      | k1_xboole_0 = B_62
      | ~ v2_funct_1(C_63)
      | k2_relset_1(A_64,B_62,C_63) != B_62
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_62)))
      | ~ v1_funct_2(C_63,A_64,B_62)
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_292,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_288])).

tff(c_296,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_165,c_162,c_42,c_292])).

tff(c_297,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_306,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_163])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_306])).

tff(c_312,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_317,plain,(
    ! [A_65,C_66,B_67] :
      ( k6_partfun1(A_65) = k5_relat_1(C_66,k2_funct_1(C_66))
      | k1_xboole_0 = B_67
      | ~ v2_funct_1(C_66)
      | k2_relset_1(A_65,B_67,C_66) != B_67
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_65,B_67)))
      | ~ v1_funct_2(C_66,A_65,B_67)
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_321,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_317])).

tff(c_325,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_165,c_162,c_42,c_321])).

tff(c_326,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_325])).

tff(c_14,plain,(
    ! [A_3] :
      ( k1_relat_1(k5_relat_1(A_3,k2_funct_1(A_3))) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_341,plain,
    ( k1_relat_1(k6_partfun1(k2_struct_0('#skF_1'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_14])).

tff(c_348,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_50,c_42,c_58,c_341])).

tff(c_252,plain,(
    ! [C_56,B_57,A_58] :
      ( m1_subset_1(k2_funct_1(C_56),k1_zfmisc_1(k2_zfmisc_1(B_57,A_58)))
      | k2_relset_1(A_58,B_57,C_56) != B_57
      | ~ v2_funct_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57)))
      | ~ v1_funct_2(C_56,A_58,B_57)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_327,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_relset_1(B_68,A_69,k2_funct_1(C_70)) = k1_relat_1(k2_funct_1(C_70))
      | k2_relset_1(A_69,B_68,C_70) != B_68
      | ~ v2_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68)))
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ v1_funct_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_252,c_18])).

tff(c_333,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_327])).

tff(c_337,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_165,c_42,c_162,c_333])).

tff(c_470,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_337])).

tff(c_240,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_tops_2(A_53,B_54,C_55) = k2_funct_1(C_55)
      | ~ v2_funct_1(C_55)
      | k2_relset_1(A_53,B_54,C_55) != B_54
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(C_55,A_53,B_54)
      | ~ v1_funct_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_243,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_240])).

tff(c_246,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_165,c_162,c_42,c_243])).

tff(c_40,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_171,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_94,c_94,c_94,c_94,c_40])).

tff(c_172,plain,(
    k1_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_225,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_172])).

tff(c_247,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_225])).

tff(c_353,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_247])).

tff(c_475,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_353])).

tff(c_478,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_475])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_50,c_42,c_478])).

tff(c_483,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_542,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_483])).

tff(c_564,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_542])).

tff(c_661,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_655,c_564])).

tff(c_814,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_661])).

tff(c_821,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_814])).

tff(c_825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_50,c_42,c_821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.51  
% 3.28/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.51  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.28/1.51  
% 3.28/1.51  %Foreground sorts:
% 3.28/1.51  
% 3.28/1.51  
% 3.28/1.51  %Background operators:
% 3.28/1.51  
% 3.28/1.51  
% 3.28/1.51  %Foreground operators:
% 3.28/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.28/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.28/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.28/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.28/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.28/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.51  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.28/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.28/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.28/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.28/1.51  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.28/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.28/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.28/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.28/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.51  
% 3.41/1.53  tff(f_144, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.41/1.53  tff(f_100, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.41/1.53  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.41/1.53  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.41/1.53  tff(f_64, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.41/1.53  tff(f_30, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.41/1.53  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.41/1.53  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.41/1.53  tff(f_96, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 3.41/1.53  tff(f_108, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.41/1.53  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 3.41/1.53  tff(f_80, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.41/1.53  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.41/1.53  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.41/1.53  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.41/1.53  tff(c_86, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.41/1.53  tff(c_94, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_86])).
% 3.41/1.53  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.41/1.53  tff(c_93, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_86])).
% 3.41/1.53  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.41/1.53  tff(c_117, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_93, c_46])).
% 3.41/1.53  tff(c_124, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.41/1.53  tff(c_128, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_117, c_124])).
% 3.41/1.53  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.41/1.53  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.41/1.53  tff(c_8, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.41/1.53  tff(c_22, plain, (![A_13]: (k6_relat_1(A_13)=k6_partfun1(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.41/1.53  tff(c_6, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.41/1.53  tff(c_57, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6])).
% 3.41/1.53  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.41/1.53  tff(c_147, plain, (![A_39, B_40, C_41]: (k2_relset_1(A_39, B_40, C_41)=k2_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.41/1.53  tff(c_151, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_117, c_147])).
% 3.41/1.53  tff(c_44, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.41/1.53  tff(c_119, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_93, c_44])).
% 3.41/1.53  tff(c_157, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_119])).
% 3.41/1.53  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.41/1.53  tff(c_95, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_48])).
% 3.41/1.53  tff(c_104, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95])).
% 3.41/1.53  tff(c_165, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_104])).
% 3.41/1.53  tff(c_162, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_151])).
% 3.41/1.53  tff(c_164, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_117])).
% 3.41/1.53  tff(c_610, plain, (![A_91, C_92, B_93]: (k6_partfun1(A_91)=k5_relat_1(C_92, k2_funct_1(C_92)) | k1_xboole_0=B_93 | ~v2_funct_1(C_92) | k2_relset_1(A_91, B_93, C_92)!=B_93 | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_93))) | ~v1_funct_2(C_92, A_91, B_93) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.41/1.53  tff(c_614, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_164, c_610])).
% 3.41/1.53  tff(c_618, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_165, c_162, c_42, c_614])).
% 3.41/1.53  tff(c_619, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_618])).
% 3.41/1.53  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.41/1.53  tff(c_105, plain, (![A_33]: (~v1_xboole_0(u1_struct_0(A_33)) | ~l1_struct_0(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.41/1.53  tff(c_111, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_105])).
% 3.41/1.53  tff(c_115, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_111])).
% 3.41/1.53  tff(c_116, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_115])).
% 3.41/1.53  tff(c_163, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_116])).
% 3.41/1.53  tff(c_629, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_619, c_163])).
% 3.41/1.53  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_629])).
% 3.41/1.53  tff(c_634, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_618])).
% 3.41/1.53  tff(c_12, plain, (![A_3]: (k2_relat_1(k5_relat_1(A_3, k2_funct_1(A_3)))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.41/1.53  tff(c_648, plain, (k2_relat_1(k6_partfun1(k2_struct_0('#skF_1')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_634, c_12])).
% 3.41/1.53  tff(c_655, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_50, c_42, c_57, c_648])).
% 3.41/1.53  tff(c_664, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_655, c_162])).
% 3.41/1.53  tff(c_667, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_655, c_165])).
% 3.41/1.53  tff(c_665, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_655, c_164])).
% 3.41/1.53  tff(c_574, plain, (![C_85, B_86, A_87]: (m1_subset_1(k2_funct_1(C_85), k1_zfmisc_1(k2_zfmisc_1(B_86, A_87))) | k2_relset_1(A_87, B_86, C_85)!=B_86 | ~v2_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))) | ~v1_funct_2(C_85, A_87, B_86) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.41/1.53  tff(c_20, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.41/1.53  tff(c_597, plain, (![B_86, A_87, C_85]: (k2_relset_1(B_86, A_87, k2_funct_1(C_85))=k2_relat_1(k2_funct_1(C_85)) | k2_relset_1(A_87, B_86, C_85)!=B_86 | ~v2_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))) | ~v1_funct_2(C_85, A_87, B_86) | ~v1_funct_1(C_85))), inference(resolution, [status(thm)], [c_574, c_20])).
% 3.41/1.53  tff(c_705, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_665, c_597])).
% 3.41/1.53  tff(c_733, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_667, c_42, c_705])).
% 3.41/1.53  tff(c_813, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_664, c_733])).
% 3.41/1.53  tff(c_557, plain, (![A_82, B_83, C_84]: (k2_tops_2(A_82, B_83, C_84)=k2_funct_1(C_84) | ~v2_funct_1(C_84) | k2_relset_1(A_82, B_83, C_84)!=B_83 | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(C_84, A_82, B_83) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.41/1.53  tff(c_560, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_164, c_557])).
% 3.41/1.53  tff(c_563, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_165, c_162, c_42, c_560])).
% 3.41/1.53  tff(c_166, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_93])).
% 3.41/1.53  tff(c_10, plain, (![A_2]: (k1_relat_1(k2_funct_1(A_2))=k2_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.41/1.53  tff(c_4, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.41/1.53  tff(c_58, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4])).
% 3.41/1.53  tff(c_288, plain, (![B_62, C_63, A_64]: (k6_partfun1(B_62)=k5_relat_1(k2_funct_1(C_63), C_63) | k1_xboole_0=B_62 | ~v2_funct_1(C_63) | k2_relset_1(A_64, B_62, C_63)!=B_62 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_62))) | ~v1_funct_2(C_63, A_64, B_62) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.41/1.53  tff(c_292, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_164, c_288])).
% 3.41/1.53  tff(c_296, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_165, c_162, c_42, c_292])).
% 3.41/1.53  tff(c_297, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_296])).
% 3.41/1.53  tff(c_306, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_163])).
% 3.41/1.53  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_306])).
% 3.41/1.53  tff(c_312, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_296])).
% 3.41/1.53  tff(c_317, plain, (![A_65, C_66, B_67]: (k6_partfun1(A_65)=k5_relat_1(C_66, k2_funct_1(C_66)) | k1_xboole_0=B_67 | ~v2_funct_1(C_66) | k2_relset_1(A_65, B_67, C_66)!=B_67 | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_65, B_67))) | ~v1_funct_2(C_66, A_65, B_67) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.41/1.53  tff(c_321, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_164, c_317])).
% 3.41/1.53  tff(c_325, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_165, c_162, c_42, c_321])).
% 3.41/1.53  tff(c_326, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_312, c_325])).
% 3.41/1.53  tff(c_14, plain, (![A_3]: (k1_relat_1(k5_relat_1(A_3, k2_funct_1(A_3)))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.41/1.53  tff(c_341, plain, (k1_relat_1(k6_partfun1(k2_struct_0('#skF_1')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_14])).
% 3.41/1.53  tff(c_348, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_50, c_42, c_58, c_341])).
% 3.41/1.53  tff(c_252, plain, (![C_56, B_57, A_58]: (m1_subset_1(k2_funct_1(C_56), k1_zfmisc_1(k2_zfmisc_1(B_57, A_58))) | k2_relset_1(A_58, B_57, C_56)!=B_57 | ~v2_funct_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))) | ~v1_funct_2(C_56, A_58, B_57) | ~v1_funct_1(C_56))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.41/1.53  tff(c_18, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.41/1.53  tff(c_327, plain, (![B_68, A_69, C_70]: (k1_relset_1(B_68, A_69, k2_funct_1(C_70))=k1_relat_1(k2_funct_1(C_70)) | k2_relset_1(A_69, B_68, C_70)!=B_68 | ~v2_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))) | ~v1_funct_2(C_70, A_69, B_68) | ~v1_funct_1(C_70))), inference(resolution, [status(thm)], [c_252, c_18])).
% 3.41/1.53  tff(c_333, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_164, c_327])).
% 3.41/1.53  tff(c_337, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_165, c_42, c_162, c_333])).
% 3.41/1.53  tff(c_470, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_337])).
% 3.41/1.53  tff(c_240, plain, (![A_53, B_54, C_55]: (k2_tops_2(A_53, B_54, C_55)=k2_funct_1(C_55) | ~v2_funct_1(C_55) | k2_relset_1(A_53, B_54, C_55)!=B_54 | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(C_55, A_53, B_54) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.41/1.53  tff(c_243, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_164, c_240])).
% 3.41/1.53  tff(c_246, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_165, c_162, c_42, c_243])).
% 3.41/1.53  tff(c_40, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.41/1.53  tff(c_171, plain, (k2_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_94, c_94, c_94, c_94, c_40])).
% 3.41/1.53  tff(c_172, plain, (k1_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_171])).
% 3.41/1.53  tff(c_225, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_172])).
% 3.41/1.53  tff(c_247, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_225])).
% 3.41/1.53  tff(c_353, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_247])).
% 3.41/1.53  tff(c_475, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_353])).
% 3.41/1.53  tff(c_478, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_475])).
% 3.41/1.53  tff(c_482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_50, c_42, c_478])).
% 3.41/1.53  tff(c_483, plain, (k2_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_171])).
% 3.41/1.53  tff(c_542, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_483])).
% 3.41/1.53  tff(c_564, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_563, c_542])).
% 3.41/1.53  tff(c_661, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_655, c_655, c_564])).
% 3.41/1.53  tff(c_814, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_813, c_661])).
% 3.41/1.53  tff(c_821, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_814])).
% 3.41/1.53  tff(c_825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_50, c_42, c_821])).
% 3.41/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.53  
% 3.41/1.53  Inference rules
% 3.41/1.53  ----------------------
% 3.41/1.53  #Ref     : 0
% 3.41/1.53  #Sup     : 174
% 3.41/1.53  #Fact    : 0
% 3.41/1.53  #Define  : 0
% 3.41/1.53  #Split   : 4
% 3.41/1.53  #Chain   : 0
% 3.41/1.53  #Close   : 0
% 3.41/1.53  
% 3.41/1.53  Ordering : KBO
% 3.41/1.53  
% 3.41/1.53  Simplification rules
% 3.41/1.53  ----------------------
% 3.41/1.53  #Subsume      : 4
% 3.41/1.53  #Demod        : 271
% 3.41/1.53  #Tautology    : 120
% 3.41/1.53  #SimpNegUnit  : 9
% 3.41/1.53  #BackRed      : 53
% 3.41/1.53  
% 3.41/1.53  #Partial instantiations: 0
% 3.41/1.53  #Strategies tried      : 1
% 3.41/1.53  
% 3.41/1.53  Timing (in seconds)
% 3.41/1.53  ----------------------
% 3.41/1.54  Preprocessing        : 0.36
% 3.41/1.54  Parsing              : 0.19
% 3.41/1.54  CNF conversion       : 0.02
% 3.41/1.54  Main loop            : 0.38
% 3.41/1.54  Inferencing          : 0.13
% 3.41/1.54  Reduction            : 0.14
% 3.41/1.54  Demodulation         : 0.10
% 3.41/1.54  BG Simplification    : 0.02
% 3.41/1.54  Subsumption          : 0.06
% 3.41/1.54  Abstraction          : 0.02
% 3.41/1.54  MUC search           : 0.00
% 3.41/1.54  Cooper               : 0.00
% 3.41/1.54  Total                : 0.79
% 3.41/1.54  Index Insertion      : 0.00
% 3.41/1.54  Index Deletion       : 0.00
% 3.41/1.54  Index Matching       : 0.00
% 3.41/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

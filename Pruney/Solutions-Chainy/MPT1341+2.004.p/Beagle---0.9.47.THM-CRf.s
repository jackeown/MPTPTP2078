%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:46 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  104 (1744 expanded)
%              Number of leaves         :   36 ( 647 expanded)
%              Depth                    :   14
%              Number of atoms          :  226 (5156 expanded)
%              Number of equality atoms :   75 (2028 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(A),C,k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k6_partfun1(k1_relset_1(u1_struct_0(A),u1_struct_0(B),C))
                    & k1_partfun1(u1_struct_0(B),u1_struct_0(A),u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),C) = k6_partfun1(k2_relset_1(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_40,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_53,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_61,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_38,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_60,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_60,c_32])).

tff(c_73,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_73])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14,plain,(
    ! [A_17] : k6_relat_1(A_17) = k6_partfun1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_relat_1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_partfun1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2])).

tff(c_83,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_relset_1(A_34,B_35,C_36) = k2_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_83])).

tff(c_30,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_78,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_60,c_30])).

tff(c_93,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_78])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62])).

tff(c_99,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_72])).

tff(c_100,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_71])).

tff(c_98,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_87])).

tff(c_378,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_funct_1(k2_funct_1(C_95))
      | k2_relset_1(A_96,B_97,C_95) != B_97
      | ~ v2_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_95,A_96,B_97)
      | ~ v1_funct_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_381,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_378])).

tff(c_384,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_28,c_98,c_381])).

tff(c_16,plain,(
    ! [C_20,B_19,A_18] :
      ( m1_subset_1(k2_funct_1(C_20),k1_zfmisc_1(k2_zfmisc_1(B_19,A_18)))
      | k2_relset_1(A_18,B_19,C_20) != B_19
      | ~ v2_funct_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_450,plain,(
    ! [E_115,A_112,C_111,F_110,D_114,B_113] :
      ( k1_partfun1(A_112,B_113,C_111,D_114,E_115,F_110) = k5_relat_1(E_115,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_111,D_114)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_1(E_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_454,plain,(
    ! [A_112,B_113,E_115] :
      ( k1_partfun1(A_112,B_113,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),E_115,'#skF_3') = k5_relat_1(E_115,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_1(E_115) ) ),
    inference(resolution,[status(thm)],[c_100,c_450])).

tff(c_459,plain,(
    ! [A_116,B_117,E_118] :
      ( k1_partfun1(A_116,B_117,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),E_118,'#skF_3') = k5_relat_1(E_118,'#skF_3')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_454])).

tff(c_504,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_partfun1(B_125,A_126,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1(C_127),'#skF_3') = k5_relat_1(k2_funct_1(C_127),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_127))
      | k2_relset_1(A_126,B_125,C_127) != B_125
      | ~ v2_funct_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ v1_funct_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_16,c_459])).

tff(c_397,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_tops_2(A_101,B_102,C_103) = k2_funct_1(C_103)
      | ~ v2_funct_1(C_103)
      | k2_relset_1(A_101,B_102,C_103) != B_102
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2(C_103,A_101,B_102)
      | ~ v1_funct_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_400,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_397])).

tff(c_403,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_98,c_28,c_400])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_partfun1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4])).

tff(c_154,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_funct_1(k2_funct_1(C_42))
      | k2_relset_1(A_43,B_44,C_42) != B_44
      | ~ v2_funct_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(C_42,A_43,B_44)
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_157,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_154])).

tff(c_160,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_28,c_98,c_157])).

tff(c_217,plain,(
    ! [F_57,E_62,A_59,D_61,C_58,B_60] :
      ( k1_partfun1(A_59,B_60,C_58,D_61,E_62,F_57) = k5_relat_1(E_62,F_57)
      | ~ m1_subset_1(F_57,k1_zfmisc_1(k2_zfmisc_1(C_58,D_61)))
      | ~ v1_funct_1(F_57)
      | ~ m1_subset_1(E_62,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_1(E_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_304,plain,(
    ! [E_88,B_89,B_85,C_87,A_84,A_86] :
      ( k1_partfun1(A_84,B_85,B_89,A_86,E_88,k2_funct_1(C_87)) = k5_relat_1(E_88,k2_funct_1(C_87))
      | ~ v1_funct_1(k2_funct_1(C_87))
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_1(E_88)
      | k2_relset_1(A_86,B_89,C_87) != B_89
      | ~ v2_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_89)))
      | ~ v1_funct_2(C_87,A_86,B_89)
      | ~ v1_funct_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_16,c_217])).

tff(c_308,plain,(
    ! [B_89,A_86,C_87] :
      ( k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),B_89,A_86,'#skF_3',k2_funct_1(C_87)) = k5_relat_1('#skF_3',k2_funct_1(C_87))
      | ~ v1_funct_1(k2_funct_1(C_87))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_86,B_89,C_87) != B_89
      | ~ v2_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_89)))
      | ~ v1_funct_2(C_87,A_86,B_89)
      | ~ v1_funct_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_100,c_304])).

tff(c_313,plain,(
    ! [B_90,A_91,C_92] :
      ( k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),B_90,A_91,'#skF_3',k2_funct_1(C_92)) = k5_relat_1('#skF_3',k2_funct_1(C_92))
      | ~ v1_funct_1(k2_funct_1(C_92))
      | k2_relset_1(A_91,B_90,C_92) != B_90
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90)))
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ v1_funct_1(C_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_308])).

tff(c_169,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_tops_2(A_48,B_49,C_50) = k2_funct_1(C_50)
      | ~ v2_funct_1(C_50)
      | k2_relset_1(A_48,B_49,C_50) != B_49
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_172,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_169])).

tff(c_175,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_98,c_28,c_172])).

tff(c_88,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_relset_1(A_37,B_38,C_39) = k1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_88])).

tff(c_112,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92])).

tff(c_101,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_60])).

tff(c_26,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_41,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26])).

tff(c_110,plain,
    ( k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3'))
    | k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_101,c_101,c_101,c_61,c_61,c_61,c_61,c_101,c_101,c_101,c_93,c_61,c_61,c_61,c_41])).

tff(c_111,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_161,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_111])).

tff(c_176,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_161])).

tff(c_319,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_176])).

tff(c_325,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_100,c_28,c_98,c_160,c_319])).

tff(c_329,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_325])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_36,c_28,c_329])).

tff(c_334,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_405,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_334])).

tff(c_510,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_405])).

tff(c_516,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_100,c_28,c_98,c_384,c_510])).

tff(c_520,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_516])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_36,c_28,c_520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:44:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.51  
% 3.30/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.51  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.30/1.51  
% 3.30/1.51  %Foreground sorts:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Background operators:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Foreground operators:
% 3.30/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.30/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.30/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.30/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.51  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.30/1.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.30/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.30/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.30/1.51  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.30/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.30/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.51  
% 3.30/1.54  tff(f_112, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_partfun1(u1_struct_0(A), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), C, k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k6_partfun1(k1_relset_1(u1_struct_0(A), u1_struct_0(B), C))) & (k1_partfun1(u1_struct_0(B), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), C) = k6_partfun1(k2_relset_1(u1_struct_0(A), u1_struct_0(B), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_2)).
% 3.30/1.54  tff(f_79, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.30/1.54  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.30/1.54  tff(f_59, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.30/1.54  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.30/1.54  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.30/1.54  tff(f_75, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.30/1.54  tff(f_57, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.30/1.54  tff(f_91, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.30/1.54  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.30/1.54  tff(c_40, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.54  tff(c_53, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.30/1.54  tff(c_61, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_53])).
% 3.30/1.54  tff(c_38, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.54  tff(c_60, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_53])).
% 3.30/1.54  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.54  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_60, c_32])).
% 3.30/1.54  tff(c_73, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.54  tff(c_77, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_73])).
% 3.30/1.54  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.54  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.54  tff(c_14, plain, (![A_17]: (k6_relat_1(A_17)=k6_partfun1(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.30/1.54  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.54  tff(c_43, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2])).
% 3.30/1.54  tff(c_83, plain, (![A_34, B_35, C_36]: (k2_relset_1(A_34, B_35, C_36)=k2_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.54  tff(c_87, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_83])).
% 3.30/1.54  tff(c_30, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.54  tff(c_78, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_60, c_30])).
% 3.30/1.54  tff(c_93, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_78])).
% 3.30/1.54  tff(c_34, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.54  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_34])).
% 3.30/1.54  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62])).
% 3.30/1.54  tff(c_99, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_72])).
% 3.30/1.54  tff(c_100, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_71])).
% 3.30/1.54  tff(c_98, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_87])).
% 3.30/1.54  tff(c_378, plain, (![C_95, A_96, B_97]: (v1_funct_1(k2_funct_1(C_95)) | k2_relset_1(A_96, B_97, C_95)!=B_97 | ~v2_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_95, A_96, B_97) | ~v1_funct_1(C_95))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.54  tff(c_381, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_378])).
% 3.30/1.54  tff(c_384, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_28, c_98, c_381])).
% 3.30/1.54  tff(c_16, plain, (![C_20, B_19, A_18]: (m1_subset_1(k2_funct_1(C_20), k1_zfmisc_1(k2_zfmisc_1(B_19, A_18))) | k2_relset_1(A_18, B_19, C_20)!=B_19 | ~v2_funct_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.54  tff(c_450, plain, (![E_115, A_112, C_111, F_110, D_114, B_113]: (k1_partfun1(A_112, B_113, C_111, D_114, E_115, F_110)=k5_relat_1(E_115, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_111, D_114))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_1(E_115))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.30/1.54  tff(c_454, plain, (![A_112, B_113, E_115]: (k1_partfun1(A_112, B_113, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), E_115, '#skF_3')=k5_relat_1(E_115, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_1(E_115))), inference(resolution, [status(thm)], [c_100, c_450])).
% 3.30/1.54  tff(c_459, plain, (![A_116, B_117, E_118]: (k1_partfun1(A_116, B_117, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), E_118, '#skF_3')=k5_relat_1(E_118, '#skF_3') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_454])).
% 3.30/1.54  tff(c_504, plain, (![B_125, A_126, C_127]: (k1_partfun1(B_125, A_126, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1(C_127), '#skF_3')=k5_relat_1(k2_funct_1(C_127), '#skF_3') | ~v1_funct_1(k2_funct_1(C_127)) | k2_relset_1(A_126, B_125, C_127)!=B_125 | ~v2_funct_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2(C_127, A_126, B_125) | ~v1_funct_1(C_127))), inference(resolution, [status(thm)], [c_16, c_459])).
% 3.30/1.54  tff(c_397, plain, (![A_101, B_102, C_103]: (k2_tops_2(A_101, B_102, C_103)=k2_funct_1(C_103) | ~v2_funct_1(C_103) | k2_relset_1(A_101, B_102, C_103)!=B_102 | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2(C_103, A_101, B_102) | ~v1_funct_1(C_103))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.30/1.54  tff(c_400, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_397])).
% 3.30/1.54  tff(c_403, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_98, c_28, c_400])).
% 3.30/1.54  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.54  tff(c_42, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4])).
% 3.30/1.54  tff(c_154, plain, (![C_42, A_43, B_44]: (v1_funct_1(k2_funct_1(C_42)) | k2_relset_1(A_43, B_44, C_42)!=B_44 | ~v2_funct_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(C_42, A_43, B_44) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.54  tff(c_157, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_154])).
% 3.30/1.54  tff(c_160, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_28, c_98, c_157])).
% 3.30/1.54  tff(c_217, plain, (![F_57, E_62, A_59, D_61, C_58, B_60]: (k1_partfun1(A_59, B_60, C_58, D_61, E_62, F_57)=k5_relat_1(E_62, F_57) | ~m1_subset_1(F_57, k1_zfmisc_1(k2_zfmisc_1(C_58, D_61))) | ~v1_funct_1(F_57) | ~m1_subset_1(E_62, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_1(E_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.30/1.54  tff(c_304, plain, (![E_88, B_89, B_85, C_87, A_84, A_86]: (k1_partfun1(A_84, B_85, B_89, A_86, E_88, k2_funct_1(C_87))=k5_relat_1(E_88, k2_funct_1(C_87)) | ~v1_funct_1(k2_funct_1(C_87)) | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_1(E_88) | k2_relset_1(A_86, B_89, C_87)!=B_89 | ~v2_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_86, B_89))) | ~v1_funct_2(C_87, A_86, B_89) | ~v1_funct_1(C_87))), inference(resolution, [status(thm)], [c_16, c_217])).
% 3.30/1.54  tff(c_308, plain, (![B_89, A_86, C_87]: (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), B_89, A_86, '#skF_3', k2_funct_1(C_87))=k5_relat_1('#skF_3', k2_funct_1(C_87)) | ~v1_funct_1(k2_funct_1(C_87)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_86, B_89, C_87)!=B_89 | ~v2_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_86, B_89))) | ~v1_funct_2(C_87, A_86, B_89) | ~v1_funct_1(C_87))), inference(resolution, [status(thm)], [c_100, c_304])).
% 3.30/1.54  tff(c_313, plain, (![B_90, A_91, C_92]: (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), B_90, A_91, '#skF_3', k2_funct_1(C_92))=k5_relat_1('#skF_3', k2_funct_1(C_92)) | ~v1_funct_1(k2_funct_1(C_92)) | k2_relset_1(A_91, B_90, C_92)!=B_90 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))) | ~v1_funct_2(C_92, A_91, B_90) | ~v1_funct_1(C_92))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_308])).
% 3.30/1.54  tff(c_169, plain, (![A_48, B_49, C_50]: (k2_tops_2(A_48, B_49, C_50)=k2_funct_1(C_50) | ~v2_funct_1(C_50) | k2_relset_1(A_48, B_49, C_50)!=B_49 | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.30/1.54  tff(c_172, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_169])).
% 3.30/1.54  tff(c_175, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_98, c_28, c_172])).
% 3.30/1.54  tff(c_88, plain, (![A_37, B_38, C_39]: (k1_relset_1(A_37, B_38, C_39)=k1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.54  tff(c_92, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_88])).
% 3.30/1.54  tff(c_112, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_92])).
% 3.30/1.54  tff(c_101, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_60])).
% 3.30/1.54  tff(c_26, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.54  tff(c_41, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26])).
% 3.30/1.54  tff(c_110, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3')) | k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_101, c_101, c_101, c_61, c_61, c_61, c_61, c_101, c_101, c_101, c_93, c_61, c_61, c_61, c_41])).
% 3.30/1.54  tff(c_111, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_110])).
% 3.30/1.54  tff(c_161, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_111])).
% 3.30/1.54  tff(c_176, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_161])).
% 3.30/1.54  tff(c_319, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_313, c_176])).
% 3.30/1.54  tff(c_325, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_100, c_28, c_98, c_160, c_319])).
% 3.30/1.54  tff(c_329, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_325])).
% 3.30/1.54  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_36, c_28, c_329])).
% 3.30/1.54  tff(c_334, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_110])).
% 3.30/1.54  tff(c_405, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_403, c_334])).
% 3.30/1.54  tff(c_510, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_504, c_405])).
% 3.30/1.54  tff(c_516, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_100, c_28, c_98, c_384, c_510])).
% 3.30/1.54  tff(c_520, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_43, c_516])).
% 3.30/1.54  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_36, c_28, c_520])).
% 3.30/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.54  
% 3.30/1.54  Inference rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Ref     : 0
% 3.30/1.54  #Sup     : 115
% 3.30/1.54  #Fact    : 0
% 3.30/1.54  #Define  : 0
% 3.30/1.54  #Split   : 2
% 3.30/1.54  #Chain   : 0
% 3.30/1.54  #Close   : 0
% 3.30/1.54  
% 3.30/1.54  Ordering : KBO
% 3.30/1.54  
% 3.30/1.54  Simplification rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Subsume      : 1
% 3.30/1.54  #Demod        : 127
% 3.30/1.54  #Tautology    : 62
% 3.30/1.54  #SimpNegUnit  : 0
% 3.30/1.54  #BackRed      : 9
% 3.30/1.54  
% 3.30/1.54  #Partial instantiations: 0
% 3.30/1.54  #Strategies tried      : 1
% 3.30/1.54  
% 3.30/1.54  Timing (in seconds)
% 3.30/1.54  ----------------------
% 3.30/1.54  Preprocessing        : 0.35
% 3.30/1.54  Parsing              : 0.19
% 3.30/1.54  CNF conversion       : 0.02
% 3.30/1.54  Main loop            : 0.36
% 3.30/1.54  Inferencing          : 0.14
% 3.30/1.54  Reduction            : 0.11
% 3.30/1.54  Demodulation         : 0.08
% 3.30/1.54  BG Simplification    : 0.02
% 3.30/1.54  Subsumption          : 0.07
% 3.30/1.54  Abstraction          : 0.02
% 3.30/1.54  MUC search           : 0.00
% 3.30/1.54  Cooper               : 0.00
% 3.30/1.54  Total                : 0.77
% 3.30/1.54  Index Insertion      : 0.00
% 3.30/1.54  Index Deletion       : 0.00
% 3.30/1.54  Index Matching       : 0.00
% 3.30/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

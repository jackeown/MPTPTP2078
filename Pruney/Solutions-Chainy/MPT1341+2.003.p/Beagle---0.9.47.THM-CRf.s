%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:46 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  109 (2129 expanded)
%              Number of leaves         :   36 ( 783 expanded)
%              Depth                    :   16
%              Number of atoms          :  194 (6272 expanded)
%              Number of equality atoms :   62 (2459 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

tff(f_108,negated_conjecture,(
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

tff(f_63,axiom,(
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
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_40,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_53,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_61,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_38,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

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
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

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
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_78,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_60,c_30])).

tff(c_93,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_78])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62])).

tff(c_99,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_72])).

tff(c_98,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_87])).

tff(c_100,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_71])).

tff(c_420,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_tops_2(A_83,B_84,C_85) = k2_funct_1(C_85)
      | ~ v2_funct_1(C_85)
      | k2_relset_1(A_83,B_84,C_85) != B_84
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_85,A_83,B_84)
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_426,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_420])).

tff(c_430,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_98,c_28,c_426])).

tff(c_371,plain,(
    ! [A_71,B_72,C_73] :
      ( v1_funct_1(k2_tops_2(A_71,B_72,C_73))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_73,A_71,B_72)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_374,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_371])).

tff(c_377,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_374])).

tff(c_434,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_377])).

tff(c_20,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k2_tops_2(A_22,B_23,C_24),k1_zfmisc_1(k2_zfmisc_1(B_23,A_22)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_439,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_20])).

tff(c_443,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_100,c_439])).

tff(c_481,plain,(
    ! [A_88,F_86,E_91,B_89,C_87,D_90] :
      ( k1_partfun1(A_88,B_89,C_87,D_90,E_91,F_86) = k5_relat_1(E_91,F_86)
      | ~ m1_subset_1(F_86,k1_zfmisc_1(k2_zfmisc_1(C_87,D_90)))
      | ~ v1_funct_1(F_86)
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_1(E_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_487,plain,(
    ! [A_88,B_89,E_91] :
      ( k1_partfun1(A_88,B_89,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),E_91,'#skF_3') = k5_relat_1(E_91,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_1(E_91) ) ),
    inference(resolution,[status(thm)],[c_100,c_481])).

tff(c_507,plain,(
    ! [A_92,B_93,E_94] :
      ( k1_partfun1(A_92,B_93,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),E_94,'#skF_3') = k5_relat_1(E_94,'#skF_3')
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_1(E_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_487])).

tff(c_510,plain,
    ( k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_443,c_507])).

tff(c_519,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_510])).

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

tff(c_199,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_tops_2(A_54,B_55,C_56) = k2_funct_1(C_56)
      | ~ v2_funct_1(C_56)
      | k2_relset_1(A_54,B_55,C_56) != B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_205,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_199])).

tff(c_209,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_98,c_28,c_205])).

tff(c_154,plain,(
    ! [A_42,B_43,C_44] :
      ( v1_funct_1(k2_tops_2(A_42,B_43,C_44))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(C_44,A_42,B_43)
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_157,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_154])).

tff(c_160,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_157])).

tff(c_213,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_160])).

tff(c_217,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_20])).

tff(c_221,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99,c_100,c_217])).

tff(c_267,plain,(
    ! [F_57,E_62,A_59,D_61,C_58,B_60] :
      ( k1_partfun1(A_59,B_60,C_58,D_61,E_62,F_57) = k5_relat_1(E_62,F_57)
      | ~ m1_subset_1(F_57,k1_zfmisc_1(k2_zfmisc_1(C_58,D_61)))
      | ~ v1_funct_1(F_57)
      | ~ m1_subset_1(E_62,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_1(E_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_269,plain,(
    ! [A_59,B_60,E_62] :
      ( k1_partfun1(A_59,B_60,k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),E_62,k2_funct_1('#skF_3')) = k5_relat_1(E_62,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_62,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_1(E_62) ) ),
    inference(resolution,[status(thm)],[c_221,c_267])).

tff(c_306,plain,(
    ! [A_66,B_67,E_68] :
      ( k1_partfun1(A_66,B_67,k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),E_68,k2_funct_1('#skF_3')) = k5_relat_1(E_68,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_1(E_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_269])).

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
    inference(cnfTransformation,[status(thm)],[f_108])).

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

tff(c_212,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_161])).

tff(c_312,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_212])).

tff(c_318,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_312])).

tff(c_322,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_318])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_36,c_28,c_322])).

tff(c_327,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_435,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_327])).

tff(c_542,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_435])).

tff(c_549,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_542])).

tff(c_553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_36,c_28,c_549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:35:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.35  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.65/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.65/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.65/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.35  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.65/1.35  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.65/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.65/1.35  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.65/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.35  
% 2.65/1.38  tff(f_108, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_partfun1(u1_struct_0(A), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), C, k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k6_partfun1(k1_relset_1(u1_struct_0(A), u1_struct_0(B), C))) & (k1_partfun1(u1_struct_0(B), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), C) = k6_partfun1(k2_relset_1(u1_struct_0(A), u1_struct_0(B), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_2)).
% 2.65/1.38  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.65/1.38  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.65/1.38  tff(f_59, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.65/1.38  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.65/1.38  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.65/1.38  tff(f_75, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 2.65/1.38  tff(f_87, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 2.65/1.38  tff(f_57, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.65/1.38  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.65/1.38  tff(c_40, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.38  tff(c_53, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.38  tff(c_61, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_53])).
% 2.65/1.38  tff(c_38, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.38  tff(c_60, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.65/1.38  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.38  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_60, c_32])).
% 2.65/1.38  tff(c_73, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.38  tff(c_77, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_73])).
% 2.65/1.38  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.38  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.38  tff(c_14, plain, (![A_17]: (k6_relat_1(A_17)=k6_partfun1(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.38  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.38  tff(c_43, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2])).
% 2.65/1.38  tff(c_83, plain, (![A_34, B_35, C_36]: (k2_relset_1(A_34, B_35, C_36)=k2_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.38  tff(c_87, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_83])).
% 2.65/1.38  tff(c_30, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.38  tff(c_78, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_60, c_30])).
% 2.65/1.38  tff(c_93, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_78])).
% 2.65/1.38  tff(c_34, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.38  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_34])).
% 2.65/1.38  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62])).
% 2.65/1.38  tff(c_99, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_72])).
% 2.65/1.38  tff(c_98, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_87])).
% 2.65/1.38  tff(c_100, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_71])).
% 2.65/1.38  tff(c_420, plain, (![A_83, B_84, C_85]: (k2_tops_2(A_83, B_84, C_85)=k2_funct_1(C_85) | ~v2_funct_1(C_85) | k2_relset_1(A_83, B_84, C_85)!=B_84 | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_85, A_83, B_84) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.38  tff(c_426, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_420])).
% 2.65/1.38  tff(c_430, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_98, c_28, c_426])).
% 2.65/1.38  tff(c_371, plain, (![A_71, B_72, C_73]: (v1_funct_1(k2_tops_2(A_71, B_72, C_73)) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2(C_73, A_71, B_72) | ~v1_funct_1(C_73))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.38  tff(c_374, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_371])).
% 2.65/1.38  tff(c_377, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_374])).
% 2.65/1.38  tff(c_434, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_377])).
% 2.65/1.38  tff(c_20, plain, (![A_22, B_23, C_24]: (m1_subset_1(k2_tops_2(A_22, B_23, C_24), k1_zfmisc_1(k2_zfmisc_1(B_23, A_22))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.38  tff(c_439, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_430, c_20])).
% 2.65/1.38  tff(c_443, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_100, c_439])).
% 2.65/1.38  tff(c_481, plain, (![A_88, F_86, E_91, B_89, C_87, D_90]: (k1_partfun1(A_88, B_89, C_87, D_90, E_91, F_86)=k5_relat_1(E_91, F_86) | ~m1_subset_1(F_86, k1_zfmisc_1(k2_zfmisc_1(C_87, D_90))) | ~v1_funct_1(F_86) | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_1(E_91))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.38  tff(c_487, plain, (![A_88, B_89, E_91]: (k1_partfun1(A_88, B_89, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), E_91, '#skF_3')=k5_relat_1(E_91, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_1(E_91))), inference(resolution, [status(thm)], [c_100, c_481])).
% 2.65/1.38  tff(c_507, plain, (![A_92, B_93, E_94]: (k1_partfun1(A_92, B_93, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), E_94, '#skF_3')=k5_relat_1(E_94, '#skF_3') | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_1(E_94))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_487])).
% 2.65/1.38  tff(c_510, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_443, c_507])).
% 2.65/1.38  tff(c_519, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_510])).
% 2.65/1.38  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.38  tff(c_42, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4])).
% 2.65/1.38  tff(c_199, plain, (![A_54, B_55, C_56]: (k2_tops_2(A_54, B_55, C_56)=k2_funct_1(C_56) | ~v2_funct_1(C_56) | k2_relset_1(A_54, B_55, C_56)!=B_55 | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(C_56, A_54, B_55) | ~v1_funct_1(C_56))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.38  tff(c_205, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_199])).
% 2.65/1.38  tff(c_209, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_98, c_28, c_205])).
% 2.65/1.38  tff(c_154, plain, (![A_42, B_43, C_44]: (v1_funct_1(k2_tops_2(A_42, B_43, C_44)) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(C_44, A_42, B_43) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.38  tff(c_157, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_154])).
% 2.65/1.38  tff(c_160, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_157])).
% 2.65/1.38  tff(c_213, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_160])).
% 2.65/1.38  tff(c_217, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_209, c_20])).
% 2.65/1.38  tff(c_221, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99, c_100, c_217])).
% 2.65/1.38  tff(c_267, plain, (![F_57, E_62, A_59, D_61, C_58, B_60]: (k1_partfun1(A_59, B_60, C_58, D_61, E_62, F_57)=k5_relat_1(E_62, F_57) | ~m1_subset_1(F_57, k1_zfmisc_1(k2_zfmisc_1(C_58, D_61))) | ~v1_funct_1(F_57) | ~m1_subset_1(E_62, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_1(E_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.38  tff(c_269, plain, (![A_59, B_60, E_62]: (k1_partfun1(A_59, B_60, k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), E_62, k2_funct_1('#skF_3'))=k5_relat_1(E_62, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_62, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_1(E_62))), inference(resolution, [status(thm)], [c_221, c_267])).
% 2.65/1.38  tff(c_306, plain, (![A_66, B_67, E_68]: (k1_partfun1(A_66, B_67, k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), E_68, k2_funct_1('#skF_3'))=k5_relat_1(E_68, k2_funct_1('#skF_3')) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_1(E_68))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_269])).
% 2.65/1.38  tff(c_88, plain, (![A_37, B_38, C_39]: (k1_relset_1(A_37, B_38, C_39)=k1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.38  tff(c_92, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_88])).
% 2.65/1.38  tff(c_112, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_92])).
% 2.65/1.38  tff(c_101, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_60])).
% 2.65/1.38  tff(c_26, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.38  tff(c_41, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26])).
% 2.65/1.38  tff(c_110, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3')) | k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_101, c_101, c_101, c_61, c_61, c_61, c_61, c_101, c_101, c_101, c_93, c_61, c_61, c_61, c_41])).
% 2.65/1.38  tff(c_111, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_110])).
% 2.65/1.38  tff(c_161, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_111])).
% 2.65/1.38  tff(c_212, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_161])).
% 2.65/1.38  tff(c_312, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_306, c_212])).
% 2.65/1.38  tff(c_318, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_100, c_312])).
% 2.65/1.38  tff(c_322, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_318])).
% 2.65/1.38  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_36, c_28, c_322])).
% 2.65/1.38  tff(c_327, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_110])).
% 2.65/1.38  tff(c_435, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_327])).
% 2.65/1.38  tff(c_542, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_435])).
% 2.65/1.38  tff(c_549, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_43, c_542])).
% 2.65/1.38  tff(c_553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_36, c_28, c_549])).
% 2.65/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.38  
% 2.65/1.38  Inference rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Ref     : 0
% 2.65/1.38  #Sup     : 123
% 2.65/1.38  #Fact    : 0
% 2.65/1.38  #Define  : 0
% 2.65/1.38  #Split   : 1
% 2.65/1.38  #Chain   : 0
% 2.65/1.38  #Close   : 0
% 2.65/1.38  
% 2.65/1.38  Ordering : KBO
% 2.65/1.38  
% 2.65/1.38  Simplification rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Subsume      : 0
% 2.65/1.38  #Demod        : 116
% 2.65/1.38  #Tautology    : 65
% 2.65/1.38  #SimpNegUnit  : 0
% 2.65/1.38  #BackRed      : 16
% 2.65/1.38  
% 2.65/1.38  #Partial instantiations: 0
% 2.65/1.38  #Strategies tried      : 1
% 2.65/1.38  
% 2.65/1.38  Timing (in seconds)
% 2.65/1.38  ----------------------
% 2.65/1.38  Preprocessing        : 0.32
% 2.65/1.38  Parsing              : 0.18
% 2.65/1.38  CNF conversion       : 0.02
% 2.65/1.38  Main loop            : 0.30
% 2.65/1.38  Inferencing          : 0.11
% 2.65/1.38  Reduction            : 0.10
% 2.65/1.38  Demodulation         : 0.08
% 2.65/1.38  BG Simplification    : 0.02
% 2.65/1.38  Subsumption          : 0.05
% 2.65/1.38  Abstraction          : 0.02
% 2.65/1.38  MUC search           : 0.00
% 2.65/1.38  Cooper               : 0.00
% 2.65/1.38  Total                : 0.67
% 2.65/1.38  Index Insertion      : 0.00
% 2.65/1.38  Index Deletion       : 0.00
% 2.65/1.38  Index Matching       : 0.00
% 2.65/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

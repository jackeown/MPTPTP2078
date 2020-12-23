%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:47 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  107 (1744 expanded)
%              Number of leaves         :   37 ( 649 expanded)
%              Depth                    :   14
%              Number of atoms          :  237 (5162 expanded)
%              Number of equality atoms :   76 (2028 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_117,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_56,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_40,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_63,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_34])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_83])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_16,plain,(
    ! [A_19] : k6_relat_1(A_19) = k6_partfun1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_45,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6])).

tff(c_87,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_relset_1(A_37,B_38,C_39) = k2_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_91,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_87])).

tff(c_32,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_74,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_32])).

tff(c_97,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_74])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_73,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_36])).

tff(c_104,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_73])).

tff(c_103,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_80])).

tff(c_102,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_91])).

tff(c_386,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_funct_1(k2_funct_1(C_98))
      | k2_relset_1(A_99,B_100,C_98) != B_100
      | ~ v2_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_2(C_98,A_99,B_100)
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_389,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_386])).

tff(c_392,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_30,c_102,c_389])).

tff(c_439,plain,(
    ! [C_116,B_117,A_118] :
      ( m1_subset_1(k2_funct_1(C_116),k1_zfmisc_1(k2_zfmisc_1(B_117,A_118)))
      | k2_relset_1(A_118,B_117,C_116) != B_117
      | ~ v2_funct_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117)))
      | ~ v1_funct_2(C_116,A_118,B_117)
      | ~ v1_funct_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_422,plain,(
    ! [D_108,A_111,F_107,E_110,B_109,C_112] :
      ( k1_partfun1(A_111,B_109,C_112,D_108,E_110,F_107) = k5_relat_1(E_110,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_112,D_108)))
      | ~ v1_funct_1(F_107)
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_424,plain,(
    ! [A_111,B_109,E_110] :
      ( k1_partfun1(A_111,B_109,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),E_110,'#skF_3') = k5_relat_1(E_110,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(resolution,[status(thm)],[c_103,c_422])).

tff(c_427,plain,(
    ! [A_111,B_109,E_110] :
      ( k1_partfun1(A_111,B_109,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),E_110,'#skF_3') = k5_relat_1(E_110,'#skF_3')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_424])).

tff(c_514,plain,(
    ! [B_128,A_129,C_130] :
      ( k1_partfun1(B_128,A_129,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1(C_130),'#skF_3') = k5_relat_1(k2_funct_1(C_130),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_130))
      | k2_relset_1(A_129,B_128,C_130) != B_128
      | ~ v2_funct_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128)))
      | ~ v1_funct_2(C_130,A_129,B_128)
      | ~ v1_funct_1(C_130) ) ),
    inference(resolution,[status(thm)],[c_439,c_427])).

tff(c_405,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_tops_2(A_104,B_105,C_106) = k2_funct_1(C_106)
      | ~ v2_funct_1(C_106)
      | k2_relset_1(A_104,B_105,C_106) != B_105
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_2(C_106,A_104,B_105)
      | ~ v1_funct_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_408,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_405])).

tff(c_411,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_102,c_30,c_408])).

tff(c_8,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8])).

tff(c_159,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_funct_1(k2_funct_1(C_45))
      | k2_relset_1(A_46,B_47,C_45) != B_47
      | ~ v2_funct_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_2(C_45,A_46,B_47)
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_162,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_159])).

tff(c_165,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_30,c_102,c_162])).

tff(c_203,plain,(
    ! [C_63,B_64,A_65] :
      ( m1_subset_1(k2_funct_1(C_63),k1_zfmisc_1(k2_zfmisc_1(B_64,A_65)))
      | k2_relset_1(A_65,B_64,C_63) != B_64
      | ~ v2_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64)))
      | ~ v1_funct_2(C_63,A_65,B_64)
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] :
      ( k1_partfun1(A_13,B_14,C_15,D_16,E_17,F_18) = k5_relat_1(E_17,F_18)
      | ~ m1_subset_1(F_18,k1_zfmisc_1(k2_zfmisc_1(C_15,D_16)))
      | ~ v1_funct_1(F_18)
      | ~ m1_subset_1(E_17,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(E_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_311,plain,(
    ! [C_89,B_87,E_88,A_92,A_91,B_90] :
      ( k1_partfun1(A_91,B_87,B_90,A_92,E_88,k2_funct_1(C_89)) = k5_relat_1(E_88,k2_funct_1(C_89))
      | ~ v1_funct_1(k2_funct_1(C_89))
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_91,B_87)))
      | ~ v1_funct_1(E_88)
      | k2_relset_1(A_92,B_90,C_89) != B_90
      | ~ v2_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_92,B_90)))
      | ~ v1_funct_2(C_89,A_92,B_90)
      | ~ v1_funct_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_203,c_14])).

tff(c_315,plain,(
    ! [B_90,A_92,C_89] :
      ( k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),B_90,A_92,'#skF_3',k2_funct_1(C_89)) = k5_relat_1('#skF_3',k2_funct_1(C_89))
      | ~ v1_funct_1(k2_funct_1(C_89))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_92,B_90,C_89) != B_90
      | ~ v2_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_92,B_90)))
      | ~ v1_funct_2(C_89,A_92,B_90)
      | ~ v1_funct_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_103,c_311])).

tff(c_320,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),B_93,A_94,'#skF_3',k2_funct_1(C_95)) = k5_relat_1('#skF_3',k2_funct_1(C_95))
      | ~ v1_funct_1(k2_funct_1(C_95))
      | k2_relset_1(A_94,B_93,C_95) != B_93
      | ~ v2_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93)))
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ v1_funct_1(C_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_315])).

tff(c_174,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_tops_2(A_51,B_52,C_53) = k2_funct_1(C_53)
      | ~ v2_funct_1(C_53)
      | k2_relset_1(A_51,B_52,C_53) != B_52
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ v1_funct_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_177,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_174])).

tff(c_180,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_102,c_30,c_177])).

tff(c_92,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_96,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_92])).

tff(c_116,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_96])).

tff(c_105,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_63])).

tff(c_28,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_43,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_114,plain,
    ( k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3'))
    | k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_105,c_105,c_105,c_64,c_64,c_64,c_64,c_105,c_105,c_105,c_97,c_64,c_64,c_64,c_43])).

tff(c_115,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_166,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_115])).

tff(c_181,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_166])).

tff(c_326,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_181])).

tff(c_332,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_103,c_30,c_102,c_165,c_326])).

tff(c_336,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_332])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_38,c_30,c_336])).

tff(c_341,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_413,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_341])).

tff(c_520,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_413])).

tff(c_526,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_103,c_30,c_102,c_392,c_520])).

tff(c_530,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_526])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_38,c_30,c_530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.48  
% 2.99/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.48  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.99/1.48  
% 2.99/1.48  %Foreground sorts:
% 2.99/1.48  
% 2.99/1.48  
% 2.99/1.48  %Background operators:
% 2.99/1.48  
% 2.99/1.48  
% 2.99/1.48  %Foreground operators:
% 2.99/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.99/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.99/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.48  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.99/1.48  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.99/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.99/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.99/1.48  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.99/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.99/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.48  
% 2.99/1.50  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.99/1.50  tff(f_117, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_partfun1(u1_struct_0(A), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), C, k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k6_partfun1(k1_relset_1(u1_struct_0(A), u1_struct_0(B), C))) & (k1_partfun1(u1_struct_0(B), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), C) = k6_partfun1(k2_relset_1(u1_struct_0(A), u1_struct_0(B), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_2)).
% 2.99/1.50  tff(f_84, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.99/1.50  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.99/1.50  tff(f_64, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.99/1.50  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.99/1.50  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.99/1.50  tff(f_80, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 2.99/1.50  tff(f_62, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.99/1.50  tff(f_96, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 2.99/1.50  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.99/1.50  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.50  tff(c_42, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.99/1.50  tff(c_56, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.50  tff(c_64, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_56])).
% 2.99/1.50  tff(c_40, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.99/1.50  tff(c_63, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.99/1.50  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.99/1.50  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_34])).
% 2.99/1.50  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.50  tff(c_83, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_80, c_2])).
% 2.99/1.50  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_83])).
% 2.99/1.50  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.99/1.50  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.99/1.50  tff(c_16, plain, (![A_19]: (k6_relat_1(A_19)=k6_partfun1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.99/1.50  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.99/1.50  tff(c_45, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6])).
% 2.99/1.50  tff(c_87, plain, (![A_37, B_38, C_39]: (k2_relset_1(A_37, B_38, C_39)=k2_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.99/1.50  tff(c_91, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_87])).
% 2.99/1.50  tff(c_32, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.99/1.50  tff(c_74, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_32])).
% 2.99/1.50  tff(c_97, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_74])).
% 2.99/1.50  tff(c_36, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.99/1.50  tff(c_73, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_36])).
% 2.99/1.50  tff(c_104, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_73])).
% 2.99/1.50  tff(c_103, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_80])).
% 2.99/1.50  tff(c_102, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_91])).
% 2.99/1.50  tff(c_386, plain, (![C_98, A_99, B_100]: (v1_funct_1(k2_funct_1(C_98)) | k2_relset_1(A_99, B_100, C_98)!=B_100 | ~v2_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_2(C_98, A_99, B_100) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.50  tff(c_389, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_386])).
% 2.99/1.50  tff(c_392, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_30, c_102, c_389])).
% 2.99/1.50  tff(c_439, plain, (![C_116, B_117, A_118]: (m1_subset_1(k2_funct_1(C_116), k1_zfmisc_1(k2_zfmisc_1(B_117, A_118))) | k2_relset_1(A_118, B_117, C_116)!=B_117 | ~v2_funct_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))) | ~v1_funct_2(C_116, A_118, B_117) | ~v1_funct_1(C_116))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.50  tff(c_422, plain, (![D_108, A_111, F_107, E_110, B_109, C_112]: (k1_partfun1(A_111, B_109, C_112, D_108, E_110, F_107)=k5_relat_1(E_110, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_112, D_108))) | ~v1_funct_1(F_107) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))) | ~v1_funct_1(E_110))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.50  tff(c_424, plain, (![A_111, B_109, E_110]: (k1_partfun1(A_111, B_109, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), E_110, '#skF_3')=k5_relat_1(E_110, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))) | ~v1_funct_1(E_110))), inference(resolution, [status(thm)], [c_103, c_422])).
% 2.99/1.50  tff(c_427, plain, (![A_111, B_109, E_110]: (k1_partfun1(A_111, B_109, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), E_110, '#skF_3')=k5_relat_1(E_110, '#skF_3') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))) | ~v1_funct_1(E_110))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_424])).
% 2.99/1.50  tff(c_514, plain, (![B_128, A_129, C_130]: (k1_partfun1(B_128, A_129, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1(C_130), '#skF_3')=k5_relat_1(k2_funct_1(C_130), '#skF_3') | ~v1_funct_1(k2_funct_1(C_130)) | k2_relset_1(A_129, B_128, C_130)!=B_128 | ~v2_funct_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))) | ~v1_funct_2(C_130, A_129, B_128) | ~v1_funct_1(C_130))), inference(resolution, [status(thm)], [c_439, c_427])).
% 2.99/1.50  tff(c_405, plain, (![A_104, B_105, C_106]: (k2_tops_2(A_104, B_105, C_106)=k2_funct_1(C_106) | ~v2_funct_1(C_106) | k2_relset_1(A_104, B_105, C_106)!=B_105 | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_2(C_106, A_104, B_105) | ~v1_funct_1(C_106))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.50  tff(c_408, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_405])).
% 2.99/1.50  tff(c_411, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_102, c_30, c_408])).
% 2.99/1.50  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.99/1.50  tff(c_44, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8])).
% 2.99/1.50  tff(c_159, plain, (![C_45, A_46, B_47]: (v1_funct_1(k2_funct_1(C_45)) | k2_relset_1(A_46, B_47, C_45)!=B_47 | ~v2_funct_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_2(C_45, A_46, B_47) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.50  tff(c_162, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_159])).
% 2.99/1.50  tff(c_165, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_30, c_102, c_162])).
% 2.99/1.50  tff(c_203, plain, (![C_63, B_64, A_65]: (m1_subset_1(k2_funct_1(C_63), k1_zfmisc_1(k2_zfmisc_1(B_64, A_65))) | k2_relset_1(A_65, B_64, C_63)!=B_64 | ~v2_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))) | ~v1_funct_2(C_63, A_65, B_64) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.50  tff(c_14, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (k1_partfun1(A_13, B_14, C_15, D_16, E_17, F_18)=k5_relat_1(E_17, F_18) | ~m1_subset_1(F_18, k1_zfmisc_1(k2_zfmisc_1(C_15, D_16))) | ~v1_funct_1(F_18) | ~m1_subset_1(E_17, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(E_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.50  tff(c_311, plain, (![C_89, B_87, E_88, A_92, A_91, B_90]: (k1_partfun1(A_91, B_87, B_90, A_92, E_88, k2_funct_1(C_89))=k5_relat_1(E_88, k2_funct_1(C_89)) | ~v1_funct_1(k2_funct_1(C_89)) | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_91, B_87))) | ~v1_funct_1(E_88) | k2_relset_1(A_92, B_90, C_89)!=B_90 | ~v2_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_92, B_90))) | ~v1_funct_2(C_89, A_92, B_90) | ~v1_funct_1(C_89))), inference(resolution, [status(thm)], [c_203, c_14])).
% 2.99/1.50  tff(c_315, plain, (![B_90, A_92, C_89]: (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), B_90, A_92, '#skF_3', k2_funct_1(C_89))=k5_relat_1('#skF_3', k2_funct_1(C_89)) | ~v1_funct_1(k2_funct_1(C_89)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_92, B_90, C_89)!=B_90 | ~v2_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_92, B_90))) | ~v1_funct_2(C_89, A_92, B_90) | ~v1_funct_1(C_89))), inference(resolution, [status(thm)], [c_103, c_311])).
% 2.99/1.50  tff(c_320, plain, (![B_93, A_94, C_95]: (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), B_93, A_94, '#skF_3', k2_funct_1(C_95))=k5_relat_1('#skF_3', k2_funct_1(C_95)) | ~v1_funct_1(k2_funct_1(C_95)) | k2_relset_1(A_94, B_93, C_95)!=B_93 | ~v2_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))) | ~v1_funct_2(C_95, A_94, B_93) | ~v1_funct_1(C_95))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_315])).
% 2.99/1.50  tff(c_174, plain, (![A_51, B_52, C_53]: (k2_tops_2(A_51, B_52, C_53)=k2_funct_1(C_53) | ~v2_funct_1(C_53) | k2_relset_1(A_51, B_52, C_53)!=B_52 | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(C_53, A_51, B_52) | ~v1_funct_1(C_53))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.50  tff(c_177, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_174])).
% 2.99/1.50  tff(c_180, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_102, c_30, c_177])).
% 2.99/1.50  tff(c_92, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.99/1.50  tff(c_96, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_92])).
% 2.99/1.50  tff(c_116, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_96])).
% 2.99/1.50  tff(c_105, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_63])).
% 2.99/1.50  tff(c_28, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.99/1.50  tff(c_43, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 2.99/1.50  tff(c_114, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3')) | k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_105, c_105, c_105, c_64, c_64, c_64, c_64, c_105, c_105, c_105, c_97, c_64, c_64, c_64, c_43])).
% 2.99/1.50  tff(c_115, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_114])).
% 2.99/1.50  tff(c_166, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_115])).
% 2.99/1.50  tff(c_181, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_166])).
% 2.99/1.50  tff(c_326, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_320, c_181])).
% 2.99/1.50  tff(c_332, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_103, c_30, c_102, c_165, c_326])).
% 2.99/1.50  tff(c_336, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_332])).
% 2.99/1.50  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_38, c_30, c_336])).
% 2.99/1.50  tff(c_341, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_114])).
% 2.99/1.50  tff(c_413, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_341])).
% 2.99/1.50  tff(c_520, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_514, c_413])).
% 2.99/1.50  tff(c_526, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_103, c_30, c_102, c_392, c_520])).
% 2.99/1.50  tff(c_530, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_45, c_526])).
% 2.99/1.50  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_38, c_30, c_530])).
% 2.99/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.50  
% 2.99/1.50  Inference rules
% 2.99/1.50  ----------------------
% 2.99/1.50  #Ref     : 0
% 2.99/1.50  #Sup     : 115
% 2.99/1.50  #Fact    : 0
% 2.99/1.50  #Define  : 0
% 2.99/1.50  #Split   : 2
% 2.99/1.50  #Chain   : 0
% 2.99/1.50  #Close   : 0
% 2.99/1.50  
% 2.99/1.50  Ordering : KBO
% 2.99/1.50  
% 2.99/1.50  Simplification rules
% 2.99/1.50  ----------------------
% 2.99/1.50  #Subsume      : 1
% 2.99/1.50  #Demod        : 132
% 2.99/1.50  #Tautology    : 62
% 2.99/1.50  #SimpNegUnit  : 0
% 2.99/1.50  #BackRed      : 8
% 2.99/1.50  
% 2.99/1.50  #Partial instantiations: 0
% 2.99/1.50  #Strategies tried      : 1
% 2.99/1.50  
% 2.99/1.50  Timing (in seconds)
% 2.99/1.50  ----------------------
% 2.99/1.51  Preprocessing        : 0.32
% 2.99/1.51  Parsing              : 0.17
% 2.99/1.51  CNF conversion       : 0.02
% 2.99/1.51  Main loop            : 0.33
% 2.99/1.51  Inferencing          : 0.12
% 2.99/1.51  Reduction            : 0.10
% 2.99/1.51  Demodulation         : 0.07
% 2.99/1.51  BG Simplification    : 0.02
% 2.99/1.51  Subsumption          : 0.06
% 2.99/1.51  Abstraction          : 0.02
% 2.99/1.51  MUC search           : 0.00
% 2.99/1.51  Cooper               : 0.00
% 2.99/1.51  Total                : 0.69
% 2.99/1.51  Index Insertion      : 0.00
% 2.99/1.51  Index Deletion       : 0.00
% 2.99/1.51  Index Matching       : 0.00
% 2.99/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

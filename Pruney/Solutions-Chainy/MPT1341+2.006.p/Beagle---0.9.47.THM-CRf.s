%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:46 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  111 (2125 expanded)
%              Number of leaves         :   37 ( 785 expanded)
%              Depth                    :   16
%              Number of atoms          :  199 (6274 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_113,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_64,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_40,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_63,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_34])).

tff(c_75,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_74,c_75])).

tff(c_81,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

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
    inference(resolution,[status(thm)],[c_74,c_87])).

tff(c_32,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_82,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_32])).

tff(c_97,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_82])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_73,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_36])).

tff(c_104,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_73])).

tff(c_102,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_91])).

tff(c_103,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_74])).

tff(c_431,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_tops_2(A_86,B_87,C_88) = k2_funct_1(C_88)
      | ~ v2_funct_1(C_88)
      | k2_relset_1(A_86,B_87,C_88) != B_87
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_2(C_88,A_86,B_87)
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_437,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_431])).

tff(c_441,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_102,c_30,c_437])).

tff(c_380,plain,(
    ! [A_74,B_75,C_76] :
      ( v1_funct_1(k2_tops_2(A_74,B_75,C_76))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_76,A_74,B_75)
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_383,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_380])).

tff(c_386,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_383])).

tff(c_445,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_386])).

tff(c_22,plain,(
    ! [A_24,B_25,C_26] :
      ( m1_subset_1(k2_tops_2(A_24,B_25,C_26),k1_zfmisc_1(k2_zfmisc_1(B_25,A_24)))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_450,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_22])).

tff(c_454,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_103,c_450])).

tff(c_493,plain,(
    ! [F_89,C_94,B_91,E_92,A_93,D_90] :
      ( k1_partfun1(A_93,B_91,C_94,D_90,E_92,F_89) = k5_relat_1(E_92,F_89)
      | ~ m1_subset_1(F_89,k1_zfmisc_1(k2_zfmisc_1(C_94,D_90)))
      | ~ v1_funct_1(F_89)
      | ~ m1_subset_1(E_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_1(E_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_499,plain,(
    ! [A_93,B_91,E_92] :
      ( k1_partfun1(A_93,B_91,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),E_92,'#skF_3') = k5_relat_1(E_92,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_1(E_92) ) ),
    inference(resolution,[status(thm)],[c_103,c_493])).

tff(c_519,plain,(
    ! [A_95,B_96,E_97] :
      ( k1_partfun1(A_95,B_96,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),E_97,'#skF_3') = k5_relat_1(E_97,'#skF_3')
      | ~ m1_subset_1(E_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1(E_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_499])).

tff(c_522,plain,
    ( k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_454,c_519])).

tff(c_531,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_522])).

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

tff(c_206,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_tops_2(A_57,B_58,C_59) = k2_funct_1(C_59)
      | ~ v2_funct_1(C_59)
      | k2_relset_1(A_57,B_58,C_59) != B_58
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_212,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_206])).

tff(c_216,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_102,c_30,c_212])).

tff(c_159,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_1(k2_tops_2(A_45,B_46,C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_162,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_159])).

tff(c_165,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_162])).

tff(c_220,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_165])).

tff(c_224,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_22])).

tff(c_228,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104,c_103,c_224])).

tff(c_275,plain,(
    ! [B_62,C_65,D_61,E_63,F_60,A_64] :
      ( k1_partfun1(A_64,B_62,C_65,D_61,E_63,F_60) = k5_relat_1(E_63,F_60)
      | ~ m1_subset_1(F_60,k1_zfmisc_1(k2_zfmisc_1(C_65,D_61)))
      | ~ v1_funct_1(F_60)
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_62)))
      | ~ v1_funct_1(E_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_277,plain,(
    ! [A_64,B_62,E_63] :
      ( k1_partfun1(A_64,B_62,k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),E_63,k2_funct_1('#skF_3')) = k5_relat_1(E_63,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_62)))
      | ~ v1_funct_1(E_63) ) ),
    inference(resolution,[status(thm)],[c_228,c_275])).

tff(c_314,plain,(
    ! [A_69,B_70,E_71] :
      ( k1_partfun1(A_69,B_70,k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),E_71,k2_funct_1('#skF_3')) = k5_relat_1(E_71,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_1(E_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_277])).

tff(c_92,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_96,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_92])).

tff(c_116,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_96])).

tff(c_105,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_63])).

tff(c_28,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

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

tff(c_219,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_166])).

tff(c_320,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_219])).

tff(c_326,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_103,c_320])).

tff(c_330,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_326])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_38,c_30,c_330])).

tff(c_335,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_446,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_335])).

tff(c_554,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_446])).

tff(c_561,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_554])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_38,c_30,c_561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:39:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.45  
% 2.99/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.45  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.99/1.45  
% 2.99/1.45  %Foreground sorts:
% 2.99/1.45  
% 2.99/1.45  
% 2.99/1.45  %Background operators:
% 2.99/1.45  
% 2.99/1.45  
% 2.99/1.45  %Foreground operators:
% 2.99/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.99/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.45  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.99/1.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.45  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.99/1.45  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.99/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.99/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.99/1.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.99/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.99/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.45  
% 2.99/1.47  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.99/1.47  tff(f_113, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_partfun1(u1_struct_0(A), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), C, k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k6_partfun1(k1_relset_1(u1_struct_0(A), u1_struct_0(B), C))) & (k1_partfun1(u1_struct_0(B), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), C) = k6_partfun1(k2_relset_1(u1_struct_0(A), u1_struct_0(B), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_2)).
% 2.99/1.47  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.99/1.47  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.99/1.47  tff(f_64, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.99/1.47  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.99/1.47  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.99/1.47  tff(f_80, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 2.99/1.47  tff(f_92, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 2.99/1.47  tff(f_62, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.99/1.47  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.99/1.47  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.47  tff(c_42, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.99/1.47  tff(c_56, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.99/1.47  tff(c_64, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_56])).
% 2.99/1.47  tff(c_40, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.99/1.47  tff(c_63, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.99/1.47  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.99/1.47  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_34])).
% 2.99/1.47  tff(c_75, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.47  tff(c_78, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_74, c_75])).
% 2.99/1.47  tff(c_81, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_78])).
% 2.99/1.47  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.99/1.47  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.99/1.47  tff(c_16, plain, (![A_19]: (k6_relat_1(A_19)=k6_partfun1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.99/1.47  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.99/1.47  tff(c_45, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6])).
% 2.99/1.47  tff(c_87, plain, (![A_37, B_38, C_39]: (k2_relset_1(A_37, B_38, C_39)=k2_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.99/1.47  tff(c_91, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_87])).
% 2.99/1.47  tff(c_32, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.99/1.47  tff(c_82, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_32])).
% 2.99/1.47  tff(c_97, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_82])).
% 2.99/1.47  tff(c_36, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.99/1.47  tff(c_73, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_36])).
% 2.99/1.47  tff(c_104, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_73])).
% 2.99/1.47  tff(c_102, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_91])).
% 2.99/1.47  tff(c_103, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_74])).
% 2.99/1.47  tff(c_431, plain, (![A_86, B_87, C_88]: (k2_tops_2(A_86, B_87, C_88)=k2_funct_1(C_88) | ~v2_funct_1(C_88) | k2_relset_1(A_86, B_87, C_88)!=B_87 | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_2(C_88, A_86, B_87) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.47  tff(c_437, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_431])).
% 2.99/1.47  tff(c_441, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_102, c_30, c_437])).
% 2.99/1.47  tff(c_380, plain, (![A_74, B_75, C_76]: (v1_funct_1(k2_tops_2(A_74, B_75, C_76)) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_76, A_74, B_75) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.99/1.47  tff(c_383, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_380])).
% 2.99/1.47  tff(c_386, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_383])).
% 2.99/1.47  tff(c_445, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_386])).
% 2.99/1.47  tff(c_22, plain, (![A_24, B_25, C_26]: (m1_subset_1(k2_tops_2(A_24, B_25, C_26), k1_zfmisc_1(k2_zfmisc_1(B_25, A_24))) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.99/1.47  tff(c_450, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_441, c_22])).
% 2.99/1.47  tff(c_454, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_103, c_450])).
% 2.99/1.47  tff(c_493, plain, (![F_89, C_94, B_91, E_92, A_93, D_90]: (k1_partfun1(A_93, B_91, C_94, D_90, E_92, F_89)=k5_relat_1(E_92, F_89) | ~m1_subset_1(F_89, k1_zfmisc_1(k2_zfmisc_1(C_94, D_90))) | ~v1_funct_1(F_89) | ~m1_subset_1(E_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_1(E_92))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.47  tff(c_499, plain, (![A_93, B_91, E_92]: (k1_partfun1(A_93, B_91, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), E_92, '#skF_3')=k5_relat_1(E_92, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_1(E_92))), inference(resolution, [status(thm)], [c_103, c_493])).
% 2.99/1.47  tff(c_519, plain, (![A_95, B_96, E_97]: (k1_partfun1(A_95, B_96, k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), E_97, '#skF_3')=k5_relat_1(E_97, '#skF_3') | ~m1_subset_1(E_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1(E_97))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_499])).
% 2.99/1.47  tff(c_522, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_454, c_519])).
% 2.99/1.47  tff(c_531, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_522])).
% 2.99/1.47  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.99/1.47  tff(c_44, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8])).
% 2.99/1.47  tff(c_206, plain, (![A_57, B_58, C_59]: (k2_tops_2(A_57, B_58, C_59)=k2_funct_1(C_59) | ~v2_funct_1(C_59) | k2_relset_1(A_57, B_58, C_59)!=B_58 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.47  tff(c_212, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_206])).
% 2.99/1.47  tff(c_216, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_102, c_30, c_212])).
% 2.99/1.47  tff(c_159, plain, (![A_45, B_46, C_47]: (v1_funct_1(k2_tops_2(A_45, B_46, C_47)) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.99/1.47  tff(c_162, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_159])).
% 2.99/1.47  tff(c_165, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_162])).
% 2.99/1.47  tff(c_220, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_165])).
% 2.99/1.47  tff(c_224, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_216, c_22])).
% 2.99/1.47  tff(c_228, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104, c_103, c_224])).
% 2.99/1.47  tff(c_275, plain, (![B_62, C_65, D_61, E_63, F_60, A_64]: (k1_partfun1(A_64, B_62, C_65, D_61, E_63, F_60)=k5_relat_1(E_63, F_60) | ~m1_subset_1(F_60, k1_zfmisc_1(k2_zfmisc_1(C_65, D_61))) | ~v1_funct_1(F_60) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_62))) | ~v1_funct_1(E_63))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.47  tff(c_277, plain, (![A_64, B_62, E_63]: (k1_partfun1(A_64, B_62, k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), E_63, k2_funct_1('#skF_3'))=k5_relat_1(E_63, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_62))) | ~v1_funct_1(E_63))), inference(resolution, [status(thm)], [c_228, c_275])).
% 2.99/1.47  tff(c_314, plain, (![A_69, B_70, E_71]: (k1_partfun1(A_69, B_70, k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), E_71, k2_funct_1('#skF_3'))=k5_relat_1(E_71, k2_funct_1('#skF_3')) | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_1(E_71))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_277])).
% 2.99/1.47  tff(c_92, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.99/1.47  tff(c_96, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_92])).
% 2.99/1.47  tff(c_116, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_96])).
% 2.99/1.47  tff(c_105, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_63])).
% 2.99/1.47  tff(c_28, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.99/1.47  tff(c_43, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 2.99/1.47  tff(c_114, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3')) | k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_105, c_105, c_105, c_64, c_64, c_64, c_64, c_105, c_105, c_105, c_97, c_64, c_64, c_64, c_43])).
% 2.99/1.47  tff(c_115, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_114])).
% 2.99/1.47  tff(c_166, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_115])).
% 2.99/1.47  tff(c_219, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_166])).
% 2.99/1.47  tff(c_320, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_314, c_219])).
% 2.99/1.47  tff(c_326, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_103, c_320])).
% 2.99/1.47  tff(c_330, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_326])).
% 2.99/1.47  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_38, c_30, c_330])).
% 2.99/1.47  tff(c_335, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_114])).
% 2.99/1.47  tff(c_446, plain, (k1_partfun1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_335])).
% 2.99/1.47  tff(c_554, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_446])).
% 2.99/1.47  tff(c_561, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_45, c_554])).
% 2.99/1.47  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_38, c_30, c_561])).
% 2.99/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.47  
% 2.99/1.47  Inference rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Ref     : 0
% 2.99/1.47  #Sup     : 123
% 2.99/1.47  #Fact    : 0
% 2.99/1.47  #Define  : 0
% 2.99/1.47  #Split   : 1
% 2.99/1.47  #Chain   : 0
% 2.99/1.47  #Close   : 0
% 2.99/1.47  
% 2.99/1.47  Ordering : KBO
% 2.99/1.47  
% 2.99/1.47  Simplification rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Subsume      : 0
% 2.99/1.47  #Demod        : 123
% 2.99/1.47  #Tautology    : 65
% 2.99/1.47  #SimpNegUnit  : 0
% 2.99/1.47  #BackRed      : 15
% 2.99/1.47  
% 2.99/1.47  #Partial instantiations: 0
% 2.99/1.47  #Strategies tried      : 1
% 2.99/1.47  
% 2.99/1.47  Timing (in seconds)
% 2.99/1.47  ----------------------
% 3.14/1.48  Preprocessing        : 0.35
% 3.14/1.48  Parsing              : 0.19
% 3.14/1.48  CNF conversion       : 0.02
% 3.14/1.48  Main loop            : 0.35
% 3.14/1.48  Inferencing          : 0.13
% 3.14/1.48  Reduction            : 0.11
% 3.14/1.48  Demodulation         : 0.08
% 3.14/1.48  BG Simplification    : 0.02
% 3.14/1.48  Subsumption          : 0.05
% 3.14/1.48  Abstraction          : 0.02
% 3.14/1.48  MUC search           : 0.00
% 3.14/1.48  Cooper               : 0.00
% 3.14/1.48  Total                : 0.74
% 3.14/1.48  Index Insertion      : 0.00
% 3.14/1.48  Index Deletion       : 0.00
% 3.14/1.48  Index Matching       : 0.00
% 3.14/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:45 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  136 (13717 expanded)
%              Number of leaves         :   40 (4819 expanded)
%              Depth                    :   22
%              Number of atoms          :  371 (40864 expanded)
%              Number of equality atoms :   86 (10369 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_178,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_121,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_117,axiom,(
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

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_156,axiom,(
    ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_62,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_62])).

tff(c_54,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_69,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_62])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_48])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_71])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_94,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_91])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_44,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_137,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_141,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_137])).

tff(c_46,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_83,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_46])).

tff(c_142,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_83])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_50])).

tff(c_81,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72])).

tff(c_150,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_81])).

tff(c_149,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_88])).

tff(c_147,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_141])).

tff(c_373,plain,(
    ! [C_72,B_73,A_74] :
      ( m1_subset_1(k2_funct_1(C_72),k1_zfmisc_1(k2_zfmisc_1(B_73,A_74)))
      | k2_relset_1(A_74,B_73,C_72) != B_73
      | ~ v2_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73)))
      | ~ v1_funct_2(C_72,A_74,B_73)
      | ~ v1_funct_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( k2_relset_1(A_13,B_14,C_15) = k2_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_442,plain,(
    ! [B_80,A_81,C_82] :
      ( k2_relset_1(B_80,A_81,k2_funct_1(C_82)) = k2_relat_1(k2_funct_1(C_82))
      | k2_relset_1(A_81,B_80,C_82) != B_80
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ v1_funct_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_373,c_24])).

tff(c_448,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_442])).

tff(c_452,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150,c_44,c_147,c_448])).

tff(c_318,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_tops_2(A_68,B_69,C_70) = k2_funct_1(C_70)
      | ~ v2_funct_1(C_70)
      | k2_relset_1(A_68,B_69,C_70) != B_69
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_2(C_70,A_68,B_69)
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_321,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_318])).

tff(c_324,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150,c_147,c_44,c_321])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_151,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_69])).

tff(c_539,plain,(
    ! [B_91,A_92,C_93] :
      ( k2_relset_1(u1_struct_0(B_91),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),u1_struct_0(B_91),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),u1_struct_0(B_91),C_93) != k2_struct_0(B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0(B_91))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),u1_struct_0(B_91))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0(B_91)
      | v2_struct_0(B_91)
      | ~ l1_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_548,plain,(
    ! [A_92,C_93] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),u1_struct_0('#skF_2'),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),u1_struct_0('#skF_2'),C_93) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_539])).

tff(c_573,plain,(
    ! [A_92,C_93] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),k2_relat_1('#skF_3'),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),k2_relat_1('#skF_3'),C_93) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_93)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_151,c_151,c_151,c_142,c_151,c_548])).

tff(c_667,plain,(
    ! [A_98,C_99] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_98),k2_tops_2(u1_struct_0(A_98),k2_relat_1('#skF_3'),C_99)) = k2_struct_0(A_98)
      | ~ v2_funct_1(C_99)
      | k2_relset_1(u1_struct_0(A_98),k2_relat_1('#skF_3'),C_99) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_99,u1_struct_0(A_98),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_99)
      | ~ l1_struct_0(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_573])).

tff(c_685,plain,(
    ! [C_99] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_99)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_99)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_99) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_99,u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_99)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_667])).

tff(c_765,plain,(
    ! [C_101] :
      ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_101)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_101)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_101) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_101,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_70,c_70,c_70,c_70,c_685])).

tff(c_774,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_765])).

tff(c_778,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150,c_149,c_147,c_44,c_452,c_774])).

tff(c_14,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_789,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_14])).

tff(c_800,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52,c_44,c_789])).

tff(c_453,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( r2_funct_2(A_83,B_84,C_85,C_85)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(D_86,A_83,B_84)
      | ~ v1_funct_1(D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_85,A_83,B_84)
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_457,plain,(
    ! [C_85] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_85,C_85)
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_85,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_149,c_453])).

tff(c_466,plain,(
    ! [C_87] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_87,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_87,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150,c_457])).

tff(c_471,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_466])).

tff(c_475,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150,c_471])).

tff(c_807,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_475])).

tff(c_22,plain,(
    ! [A_12] :
      ( k2_funct_1(k2_funct_1(A_12)) = A_12
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_814,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_150])).

tff(c_812,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_147])).

tff(c_221,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_funct_1(k2_funct_1(C_57))
      | k2_relset_1(A_58,B_59,C_57) != B_59
      | ~ v2_funct_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(C_57,A_58,B_59)
      | ~ v1_funct_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_224,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_221])).

tff(c_227,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150,c_44,c_147,c_224])).

tff(c_236,plain,(
    ! [C_62,B_63,A_64] :
      ( v1_funct_2(k2_funct_1(C_62),B_63,A_64)
      | k2_relset_1(A_64,B_63,C_62) != B_63
      | ~ v2_funct_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63)))
      | ~ v1_funct_2(C_62,A_64,B_63)
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_239,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_236])).

tff(c_242,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150,c_44,c_147,c_239])).

tff(c_811,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_242])).

tff(c_779,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_452])).

tff(c_998,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_800,c_779])).

tff(c_388,plain,(
    ! [C_72,B_73,A_74] :
      ( v1_relat_1(k2_funct_1(C_72))
      | ~ v1_relat_1(k2_zfmisc_1(B_73,A_74))
      | k2_relset_1(A_74,B_73,C_72) != B_73
      | ~ v2_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73)))
      | ~ v1_funct_2(C_72,A_74,B_73)
      | ~ v1_funct_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_373,c_2])).

tff(c_431,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(k2_funct_1(C_77))
      | k2_relset_1(A_78,B_79,C_77) != B_79
      | ~ v2_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(C_77,A_78,B_79)
      | ~ v1_funct_1(C_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_388])).

tff(c_437,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_431])).

tff(c_441,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150,c_44,c_147,c_437])).

tff(c_804,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_778])).

tff(c_8,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_relat_1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_199,plain,(
    ! [B_53,A_54] :
      ( v2_funct_1(B_53)
      | k2_relat_1(B_53) != k1_relat_1(A_54)
      | ~ v2_funct_1(k5_relat_1(B_53,A_54))
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | k2_relat_1(k2_funct_1(A_11)) != k1_relat_1(A_11)
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_11)))
      | ~ v1_funct_1(k2_funct_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_199])).

tff(c_209,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | k2_relat_1(k2_funct_1(A_11)) != k1_relat_1(A_11)
      | ~ v1_funct_1(k2_funct_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_205])).

tff(c_156,plain,(
    ! [A_51] :
      ( k5_relat_1(k2_funct_1(A_51),A_51) = k6_relat_1(k2_relat_1(A_51))
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_165,plain,(
    ! [A_12] :
      ( k6_relat_1(k2_relat_1(k2_funct_1(A_12))) = k5_relat_1(A_12,k2_funct_1(A_12))
      | ~ v2_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_156])).

tff(c_786,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k2_struct_0('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_165])).

tff(c_798,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k2_struct_0('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52,c_44,c_441,c_227,c_786])).

tff(c_1033,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_798])).

tff(c_1034,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1033])).

tff(c_1037,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_209,c_1034])).

tff(c_1044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52,c_44,c_441,c_227,c_804,c_1037])).

tff(c_1046,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1033])).

tff(c_813,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_149])).

tff(c_36,plain,(
    ! [A_24,B_25,C_26] :
      ( k2_tops_2(A_24,B_25,C_26) = k2_funct_1(C_26)
      | ~ v2_funct_1(C_26)
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1137,plain,(
    ! [B_116,A_117,C_118] :
      ( k2_tops_2(B_116,A_117,k2_funct_1(C_118)) = k2_funct_1(k2_funct_1(C_118))
      | ~ v2_funct_1(k2_funct_1(C_118))
      | k2_relset_1(B_116,A_117,k2_funct_1(C_118)) != A_117
      | ~ v1_funct_2(k2_funct_1(C_118),B_116,A_117)
      | ~ v1_funct_1(k2_funct_1(C_118))
      | k2_relset_1(A_117,B_116,C_118) != B_116
      | ~ v2_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116)))
      | ~ v1_funct_2(C_118,A_117,B_116)
      | ~ v1_funct_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_373,c_36])).

tff(c_1140,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_813,c_1137])).

tff(c_1146,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_814,c_44,c_812,c_227,c_811,c_998,c_1046,c_1140])).

tff(c_42,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_112,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_70,c_69,c_69,c_69,c_42])).

tff(c_148,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_142,c_142,c_112])).

tff(c_325,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_148])).

tff(c_809,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_800,c_325])).

tff(c_1148,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_809])).

tff(c_1155,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1148])).

tff(c_1158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52,c_44,c_807,c_1155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.89  
% 4.63/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.90  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.63/1.90  
% 4.63/1.90  %Foreground sorts:
% 4.63/1.90  
% 4.63/1.90  
% 4.63/1.90  %Background operators:
% 4.63/1.90  
% 4.63/1.90  
% 4.63/1.90  %Foreground operators:
% 4.63/1.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.63/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.63/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.90  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.63/1.90  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.63/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.90  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.63/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.63/1.90  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.63/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.63/1.90  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.63/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.90  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.63/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.63/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.63/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.63/1.90  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.63/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.63/1.90  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.63/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.90  
% 5.02/1.92  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.02/1.92  tff(f_178, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 5.02/1.92  tff(f_121, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.02/1.92  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.02/1.92  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.02/1.92  tff(f_117, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.02/1.92  tff(f_133, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.02/1.92  tff(f_156, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 5.02/1.92  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.02/1.92  tff(f_101, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 5.02/1.92  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.02/1.92  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.02/1.92  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.02/1.92  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 5.02/1.92  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.02/1.92  tff(c_58, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.02/1.92  tff(c_62, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.02/1.92  tff(c_70, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_62])).
% 5.02/1.92  tff(c_54, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.02/1.92  tff(c_69, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_62])).
% 5.02/1.92  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.02/1.92  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_48])).
% 5.02/1.92  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_71])).
% 5.02/1.92  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.02/1.92  tff(c_91, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_88, c_2])).
% 5.02/1.92  tff(c_94, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_91])).
% 5.02/1.92  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.02/1.92  tff(c_44, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.02/1.92  tff(c_137, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.02/1.92  tff(c_141, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_137])).
% 5.02/1.92  tff(c_46, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.02/1.92  tff(c_83, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_46])).
% 5.02/1.92  tff(c_142, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_83])).
% 5.02/1.92  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.02/1.92  tff(c_72, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_50])).
% 5.02/1.92  tff(c_81, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72])).
% 5.02/1.92  tff(c_150, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_81])).
% 5.02/1.92  tff(c_149, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_88])).
% 5.02/1.92  tff(c_147, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_141])).
% 5.02/1.92  tff(c_373, plain, (![C_72, B_73, A_74]: (m1_subset_1(k2_funct_1(C_72), k1_zfmisc_1(k2_zfmisc_1(B_73, A_74))) | k2_relset_1(A_74, B_73, C_72)!=B_73 | ~v2_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))) | ~v1_funct_2(C_72, A_74, B_73) | ~v1_funct_1(C_72))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.02/1.92  tff(c_24, plain, (![A_13, B_14, C_15]: (k2_relset_1(A_13, B_14, C_15)=k2_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.02/1.92  tff(c_442, plain, (![B_80, A_81, C_82]: (k2_relset_1(B_80, A_81, k2_funct_1(C_82))=k2_relat_1(k2_funct_1(C_82)) | k2_relset_1(A_81, B_80, C_82)!=B_80 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_2(C_82, A_81, B_80) | ~v1_funct_1(C_82))), inference(resolution, [status(thm)], [c_373, c_24])).
% 5.02/1.92  tff(c_448, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_149, c_442])).
% 5.02/1.92  tff(c_452, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_150, c_44, c_147, c_448])).
% 5.02/1.92  tff(c_318, plain, (![A_68, B_69, C_70]: (k2_tops_2(A_68, B_69, C_70)=k2_funct_1(C_70) | ~v2_funct_1(C_70) | k2_relset_1(A_68, B_69, C_70)!=B_69 | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_2(C_70, A_68, B_69) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.02/1.92  tff(c_321, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_149, c_318])).
% 5.02/1.92  tff(c_324, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_150, c_147, c_44, c_321])).
% 5.02/1.92  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.02/1.92  tff(c_151, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_69])).
% 5.02/1.92  tff(c_539, plain, (![B_91, A_92, C_93]: (k2_relset_1(u1_struct_0(B_91), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), u1_struct_0(B_91), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), u1_struct_0(B_91), C_93)!=k2_struct_0(B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0(B_91)))) | ~v1_funct_2(C_93, u1_struct_0(A_92), u1_struct_0(B_91)) | ~v1_funct_1(C_93) | ~l1_struct_0(B_91) | v2_struct_0(B_91) | ~l1_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.02/1.92  tff(c_548, plain, (![A_92, C_93]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), u1_struct_0('#skF_2'), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), u1_struct_0('#skF_2'), C_93)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_93, u1_struct_0(A_92), u1_struct_0('#skF_2')) | ~v1_funct_1(C_93) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_151, c_539])).
% 5.02/1.92  tff(c_573, plain, (![A_92, C_93]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), k2_relat_1('#skF_3'), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), k2_relat_1('#skF_3'), C_93)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_93, u1_struct_0(A_92), k2_relat_1('#skF_3')) | ~v1_funct_1(C_93) | v2_struct_0('#skF_2') | ~l1_struct_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_151, c_151, c_151, c_142, c_151, c_548])).
% 5.02/1.92  tff(c_667, plain, (![A_98, C_99]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0(A_98), k2_tops_2(u1_struct_0(A_98), k2_relat_1('#skF_3'), C_99))=k2_struct_0(A_98) | ~v2_funct_1(C_99) | k2_relset_1(u1_struct_0(A_98), k2_relat_1('#skF_3'), C_99)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_99, u1_struct_0(A_98), k2_relat_1('#skF_3')) | ~v1_funct_1(C_99) | ~l1_struct_0(A_98))), inference(negUnitSimplification, [status(thm)], [c_56, c_573])).
% 5.02/1.92  tff(c_685, plain, (![C_99]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_99))=k2_struct_0('#skF_1') | ~v2_funct_1(C_99) | k2_relset_1(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_99)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_99, u1_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_99) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_667])).
% 5.02/1.92  tff(c_765, plain, (![C_101]: (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_101))=k2_struct_0('#skF_1') | ~v2_funct_1(C_101) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_101)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_101, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_101))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_70, c_70, c_70, c_70, c_685])).
% 5.02/1.92  tff(c_774, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_324, c_765])).
% 5.02/1.92  tff(c_778, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_150, c_149, c_147, c_44, c_452, c_774])).
% 5.02/1.92  tff(c_14, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.02/1.92  tff(c_789, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_778, c_14])).
% 5.02/1.92  tff(c_800, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_52, c_44, c_789])).
% 5.02/1.92  tff(c_453, plain, (![A_83, B_84, C_85, D_86]: (r2_funct_2(A_83, B_84, C_85, C_85) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(D_86, A_83, B_84) | ~v1_funct_1(D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_85, A_83, B_84) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.02/1.92  tff(c_457, plain, (![C_85]: (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_85, C_85) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_85, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_85))), inference(resolution, [status(thm)], [c_149, c_453])).
% 5.02/1.92  tff(c_466, plain, (![C_87]: (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_87, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_87, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_87))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_150, c_457])).
% 5.02/1.92  tff(c_471, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_149, c_466])).
% 5.02/1.92  tff(c_475, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_150, c_471])).
% 5.02/1.92  tff(c_807, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_800, c_475])).
% 5.02/1.92  tff(c_22, plain, (![A_12]: (k2_funct_1(k2_funct_1(A_12))=A_12 | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/1.92  tff(c_814, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_150])).
% 5.02/1.92  tff(c_812, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_800, c_147])).
% 5.02/1.92  tff(c_221, plain, (![C_57, A_58, B_59]: (v1_funct_1(k2_funct_1(C_57)) | k2_relset_1(A_58, B_59, C_57)!=B_59 | ~v2_funct_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(C_57, A_58, B_59) | ~v1_funct_1(C_57))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.02/1.92  tff(c_224, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_149, c_221])).
% 5.02/1.92  tff(c_227, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_150, c_44, c_147, c_224])).
% 5.02/1.92  tff(c_236, plain, (![C_62, B_63, A_64]: (v1_funct_2(k2_funct_1(C_62), B_63, A_64) | k2_relset_1(A_64, B_63, C_62)!=B_63 | ~v2_funct_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))) | ~v1_funct_2(C_62, A_64, B_63) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.02/1.92  tff(c_239, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_149, c_236])).
% 5.02/1.92  tff(c_242, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_150, c_44, c_147, c_239])).
% 5.02/1.92  tff(c_811, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_242])).
% 5.02/1.92  tff(c_779, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_778, c_452])).
% 5.02/1.92  tff(c_998, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_800, c_800, c_779])).
% 5.02/1.92  tff(c_388, plain, (![C_72, B_73, A_74]: (v1_relat_1(k2_funct_1(C_72)) | ~v1_relat_1(k2_zfmisc_1(B_73, A_74)) | k2_relset_1(A_74, B_73, C_72)!=B_73 | ~v2_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))) | ~v1_funct_2(C_72, A_74, B_73) | ~v1_funct_1(C_72))), inference(resolution, [status(thm)], [c_373, c_2])).
% 5.02/1.92  tff(c_431, plain, (![C_77, A_78, B_79]: (v1_relat_1(k2_funct_1(C_77)) | k2_relset_1(A_78, B_79, C_77)!=B_79 | ~v2_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(C_77, A_78, B_79) | ~v1_funct_1(C_77))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_388])).
% 5.02/1.92  tff(c_437, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_149, c_431])).
% 5.02/1.92  tff(c_441, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_150, c_44, c_147, c_437])).
% 5.02/1.92  tff(c_804, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_800, c_778])).
% 5.02/1.92  tff(c_8, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.02/1.92  tff(c_18, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_relat_1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.02/1.92  tff(c_199, plain, (![B_53, A_54]: (v2_funct_1(B_53) | k2_relat_1(B_53)!=k1_relat_1(A_54) | ~v2_funct_1(k5_relat_1(B_53, A_54)) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.02/1.92  tff(c_205, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | k2_relat_1(k2_funct_1(A_11))!=k1_relat_1(A_11) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_11))) | ~v1_funct_1(k2_funct_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_18, c_199])).
% 5.02/1.92  tff(c_209, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | k2_relat_1(k2_funct_1(A_11))!=k1_relat_1(A_11) | ~v1_funct_1(k2_funct_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_205])).
% 5.02/1.92  tff(c_156, plain, (![A_51]: (k5_relat_1(k2_funct_1(A_51), A_51)=k6_relat_1(k2_relat_1(A_51)) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.02/1.92  tff(c_165, plain, (![A_12]: (k6_relat_1(k2_relat_1(k2_funct_1(A_12)))=k5_relat_1(A_12, k2_funct_1(A_12)) | ~v2_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_22, c_156])).
% 5.02/1.92  tff(c_786, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k2_struct_0('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_778, c_165])).
% 5.02/1.92  tff(c_798, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k2_struct_0('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_52, c_44, c_441, c_227, c_786])).
% 5.02/1.92  tff(c_1033, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k1_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_798])).
% 5.02/1.92  tff(c_1034, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1033])).
% 5.02/1.92  tff(c_1037, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_209, c_1034])).
% 5.02/1.92  tff(c_1044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_52, c_44, c_441, c_227, c_804, c_1037])).
% 5.02/1.92  tff(c_1046, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1033])).
% 5.02/1.92  tff(c_813, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_149])).
% 5.02/1.92  tff(c_36, plain, (![A_24, B_25, C_26]: (k2_tops_2(A_24, B_25, C_26)=k2_funct_1(C_26) | ~v2_funct_1(C_26) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.02/1.92  tff(c_1137, plain, (![B_116, A_117, C_118]: (k2_tops_2(B_116, A_117, k2_funct_1(C_118))=k2_funct_1(k2_funct_1(C_118)) | ~v2_funct_1(k2_funct_1(C_118)) | k2_relset_1(B_116, A_117, k2_funct_1(C_118))!=A_117 | ~v1_funct_2(k2_funct_1(C_118), B_116, A_117) | ~v1_funct_1(k2_funct_1(C_118)) | k2_relset_1(A_117, B_116, C_118)!=B_116 | ~v2_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))) | ~v1_funct_2(C_118, A_117, B_116) | ~v1_funct_1(C_118))), inference(resolution, [status(thm)], [c_373, c_36])).
% 5.02/1.92  tff(c_1140, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_813, c_1137])).
% 5.02/1.92  tff(c_1146, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_814, c_44, c_812, c_227, c_811, c_998, c_1046, c_1140])).
% 5.02/1.92  tff(c_42, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.02/1.92  tff(c_112, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_70, c_69, c_69, c_69, c_42])).
% 5.02/1.92  tff(c_148, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_142, c_142, c_112])).
% 5.02/1.92  tff(c_325, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_148])).
% 5.02/1.92  tff(c_809, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_800, c_800, c_325])).
% 5.02/1.92  tff(c_1148, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_809])).
% 5.02/1.92  tff(c_1155, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1148])).
% 5.02/1.92  tff(c_1158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_52, c_44, c_807, c_1155])).
% 5.02/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.92  
% 5.02/1.92  Inference rules
% 5.02/1.92  ----------------------
% 5.02/1.92  #Ref     : 0
% 5.02/1.92  #Sup     : 261
% 5.02/1.92  #Fact    : 0
% 5.02/1.92  #Define  : 0
% 5.02/1.92  #Split   : 1
% 5.02/1.92  #Chain   : 0
% 5.02/1.92  #Close   : 0
% 5.02/1.92  
% 5.02/1.92  Ordering : KBO
% 5.02/1.92  
% 5.02/1.92  Simplification rules
% 5.02/1.92  ----------------------
% 5.02/1.92  #Subsume      : 41
% 5.02/1.92  #Demod        : 431
% 5.02/1.92  #Tautology    : 137
% 5.02/1.92  #SimpNegUnit  : 4
% 5.02/1.92  #BackRed      : 23
% 5.02/1.92  
% 5.02/1.92  #Partial instantiations: 0
% 5.02/1.92  #Strategies tried      : 1
% 5.02/1.92  
% 5.02/1.92  Timing (in seconds)
% 5.02/1.92  ----------------------
% 5.02/1.93  Preprocessing        : 0.44
% 5.02/1.93  Parsing              : 0.25
% 5.02/1.93  CNF conversion       : 0.03
% 5.02/1.93  Main loop            : 0.63
% 5.02/1.93  Inferencing          : 0.23
% 5.02/1.93  Reduction            : 0.23
% 5.02/1.93  Demodulation         : 0.18
% 5.02/1.93  BG Simplification    : 0.04
% 5.02/1.93  Subsumption          : 0.11
% 5.02/1.93  Abstraction          : 0.04
% 5.02/1.93  MUC search           : 0.00
% 5.02/1.93  Cooper               : 0.00
% 5.02/1.93  Total                : 1.13
% 5.02/1.93  Index Insertion      : 0.00
% 5.02/1.93  Index Deletion       : 0.00
% 5.02/1.93  Index Matching       : 0.00
% 5.02/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------

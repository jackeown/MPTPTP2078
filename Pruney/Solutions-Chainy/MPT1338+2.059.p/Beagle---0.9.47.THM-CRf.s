%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:22 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  124 (1494 expanded)
%              Number of leaves         :   40 ( 558 expanded)
%              Depth                    :   14
%              Number of atoms          :  241 (4711 expanded)
%              Number of equality atoms :   89 (1738 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_138,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_44,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
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

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_struct_0(B) = k1_xboole_0
                 => k2_struct_0(A) = k1_xboole_0 )
               => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_50,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_51,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_59,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_51])).

tff(c_46,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_51])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_97,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_58,c_40])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_10])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_360,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_364,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_360])).

tff(c_38,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_83,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_58,c_38])).

tff(c_365,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_83])).

tff(c_42,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_68,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_58,c_42])).

tff(c_374,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_68])).

tff(c_370,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_364])).

tff(c_372,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_97])).

tff(c_475,plain,(
    ! [C_99,B_100,A_101] :
      ( m1_subset_1(k2_funct_1(C_99),k1_zfmisc_1(k2_zfmisc_1(B_100,A_101)))
      | k2_relset_1(A_101,B_100,C_99) != B_100
      | ~ v2_funct_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_2(C_99,A_101,B_100)
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_514,plain,(
    ! [B_105,A_106,C_107] :
      ( k2_relset_1(B_105,A_106,k2_funct_1(C_107)) = k2_relat_1(k2_funct_1(C_107))
      | k2_relset_1(A_106,B_105,C_107) != B_105
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_107,A_106,B_105)
      | ~ v1_funct_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_475,c_14])).

tff(c_520,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_514])).

tff(c_524,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_374,c_36,c_370,c_520])).

tff(c_458,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_tops_2(A_96,B_97,C_98) = k2_funct_1(C_98)
      | ~ v2_funct_1(C_98)
      | k2_relset_1(A_96,B_97,C_98) != B_97
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_98,A_96,B_97)
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_461,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_458])).

tff(c_464,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_374,c_370,c_36,c_461])).

tff(c_8,plain,(
    ! [A_2] :
      ( k1_relat_1(k2_funct_1(A_2)) = k2_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_125,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_relset_1(A_43,B_44,C_45) = k2_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_129,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_125])).

tff(c_130,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_83])).

tff(c_138,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_68])).

tff(c_135,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_129])).

tff(c_136,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97])).

tff(c_229,plain,(
    ! [C_64,B_65,A_66] :
      ( m1_subset_1(k2_funct_1(C_64),k1_zfmisc_1(k2_zfmisc_1(B_65,A_66)))
      | k2_relset_1(A_66,B_65,C_64) != B_65
      | ~ v2_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65)))
      | ~ v1_funct_2(C_64,A_66,B_65)
      | ~ v1_funct_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( k1_relset_1(A_6,B_7,C_8) = k1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_289,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_relset_1(B_73,A_74,k2_funct_1(C_75)) = k1_relat_1(k2_funct_1(C_75))
      | k2_relset_1(A_74,B_73,C_75) != B_73
      | ~ v2_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73)))
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ v1_funct_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_229,c_12])).

tff(c_295,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_289])).

tff(c_299,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_138,c_36,c_135,c_295])).

tff(c_217,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_tops_2(A_61,B_62,C_63) = k2_funct_1(C_63)
      | ~ v2_funct_1(C_63)
      | k2_relset_1(A_61,B_62,C_63) != B_62
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(C_63,A_61,B_62)
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_220,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_217])).

tff(c_223,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_138,c_135,c_36,c_220])).

tff(c_34,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_102,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_58,c_58,c_59,c_59,c_58,c_58,c_34])).

tff(c_103,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_177,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_130,c_103])).

tff(c_224,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_177])).

tff(c_316,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_224])).

tff(c_323,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_316])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_44,c_36,c_323])).

tff(c_328,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_417,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_365,c_328])).

tff(c_466,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_417])).

tff(c_546,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_466])).

tff(c_553,plain,
    ( k2_struct_0('#skF_1') != k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_546])).

tff(c_555,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_44,c_36,c_553])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( k8_relset_1(A_12,B_13,C_14,D_15) = k10_relat_1(C_14,D_15)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_406,plain,(
    ! [D_15] : k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3',D_15) = k10_relat_1('#skF_3',D_15) ),
    inference(resolution,[status(thm)],[c_372,c_16])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_375,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_58])).

tff(c_525,plain,(
    ! [B_108,A_109,C_110] :
      ( k2_struct_0(B_108) = k1_xboole_0
      | k8_relset_1(u1_struct_0(A_109),u1_struct_0(B_108),C_110,k2_struct_0(B_108)) = k2_struct_0(A_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109),u1_struct_0(B_108))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_109),u1_struct_0(B_108))
      | ~ v1_funct_1(C_110)
      | ~ l1_struct_0(B_108)
      | ~ l1_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_534,plain,(
    ! [B_108,C_110] :
      ( k2_struct_0(B_108) = k1_xboole_0
      | k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_108),C_110,k2_struct_0(B_108)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_108))))
      | ~ v1_funct_2(C_110,u1_struct_0('#skF_1'),u1_struct_0(B_108))
      | ~ v1_funct_1(C_110)
      | ~ l1_struct_0(B_108)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_525])).

tff(c_556,plain,(
    ! [B_111,C_112] :
      ( k2_struct_0(B_111) = k1_xboole_0
      | k8_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_111),C_112,k2_struct_0(B_111)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_111))))
      | ~ v1_funct_2(C_112,k2_struct_0('#skF_1'),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ l1_struct_0(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_59,c_59,c_534])).

tff(c_561,plain,(
    ! [C_112] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | k8_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_112,k2_struct_0('#skF_2')) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_112,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_112)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_556])).

tff(c_566,plain,(
    ! [C_112] :
      ( k2_relat_1('#skF_3') = k1_xboole_0
      | k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_112,k2_relat_1('#skF_3')) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_112,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_375,c_375,c_365,c_365,c_561])).

tff(c_653,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_69,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_75,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_69])).

tff(c_79,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_75])).

tff(c_80,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_79])).

tff(c_373,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_80])).

tff(c_667,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_373])).

tff(c_671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_667])).

tff(c_674,plain,(
    ! [C_125] :
      ( k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_125,k2_relat_1('#skF_3')) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_125,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_125) ) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_681,plain,
    ( k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3',k2_relat_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_674])).

tff(c_685,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_374,c_406,c_681])).

tff(c_4,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_689,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_4])).

tff(c_696,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_689])).

tff(c_698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.47  
% 3.22/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.47  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.22/1.47  
% 3.22/1.47  %Foreground sorts:
% 3.22/1.47  
% 3.22/1.47  
% 3.22/1.47  %Background operators:
% 3.22/1.47  
% 3.22/1.47  
% 3.22/1.47  %Foreground operators:
% 3.22/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.22/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.22/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.47  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.22/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.47  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.22/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.22/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.22/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.22/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.22/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.47  
% 3.22/1.50  tff(f_138, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.22/1.50  tff(f_76, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.22/1.50  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.22/1.50  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.22/1.50  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.22/1.50  tff(f_72, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.22/1.50  tff(f_96, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.22/1.50  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.50  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.22/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.22/1.50  tff(f_114, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 3.22/1.50  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.22/1.50  tff(f_30, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.22/1.50  tff(c_50, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.50  tff(c_51, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.22/1.50  tff(c_59, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_51])).
% 3.22/1.50  tff(c_46, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.50  tff(c_58, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_51])).
% 3.22/1.50  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.50  tff(c_97, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_58, c_40])).
% 3.22/1.50  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.22/1.50  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_97, c_10])).
% 3.22/1.50  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.50  tff(c_36, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.50  tff(c_6, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.22/1.50  tff(c_360, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.22/1.50  tff(c_364, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_97, c_360])).
% 3.22/1.50  tff(c_38, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.50  tff(c_83, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_58, c_38])).
% 3.22/1.50  tff(c_365, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_83])).
% 3.22/1.50  tff(c_42, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.50  tff(c_68, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_58, c_42])).
% 3.22/1.50  tff(c_374, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_68])).
% 3.22/1.50  tff(c_370, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_364])).
% 3.22/1.50  tff(c_372, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_97])).
% 3.22/1.50  tff(c_475, plain, (![C_99, B_100, A_101]: (m1_subset_1(k2_funct_1(C_99), k1_zfmisc_1(k2_zfmisc_1(B_100, A_101))) | k2_relset_1(A_101, B_100, C_99)!=B_100 | ~v2_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_2(C_99, A_101, B_100) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.22/1.50  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.22/1.50  tff(c_514, plain, (![B_105, A_106, C_107]: (k2_relset_1(B_105, A_106, k2_funct_1(C_107))=k2_relat_1(k2_funct_1(C_107)) | k2_relset_1(A_106, B_105, C_107)!=B_105 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_107, A_106, B_105) | ~v1_funct_1(C_107))), inference(resolution, [status(thm)], [c_475, c_14])).
% 3.22/1.50  tff(c_520, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_514])).
% 3.22/1.50  tff(c_524, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_374, c_36, c_370, c_520])).
% 3.22/1.50  tff(c_458, plain, (![A_96, B_97, C_98]: (k2_tops_2(A_96, B_97, C_98)=k2_funct_1(C_98) | ~v2_funct_1(C_98) | k2_relset_1(A_96, B_97, C_98)!=B_97 | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_98, A_96, B_97) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.22/1.50  tff(c_461, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_458])).
% 3.22/1.50  tff(c_464, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_374, c_370, c_36, c_461])).
% 3.22/1.50  tff(c_8, plain, (![A_2]: (k1_relat_1(k2_funct_1(A_2))=k2_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.22/1.50  tff(c_125, plain, (![A_43, B_44, C_45]: (k2_relset_1(A_43, B_44, C_45)=k2_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.22/1.50  tff(c_129, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_97, c_125])).
% 3.22/1.50  tff(c_130, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_83])).
% 3.22/1.50  tff(c_138, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_68])).
% 3.22/1.50  tff(c_135, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_129])).
% 3.22/1.50  tff(c_136, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97])).
% 3.22/1.50  tff(c_229, plain, (![C_64, B_65, A_66]: (m1_subset_1(k2_funct_1(C_64), k1_zfmisc_1(k2_zfmisc_1(B_65, A_66))) | k2_relset_1(A_66, B_65, C_64)!=B_65 | ~v2_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))) | ~v1_funct_2(C_64, A_66, B_65) | ~v1_funct_1(C_64))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.22/1.50  tff(c_12, plain, (![A_6, B_7, C_8]: (k1_relset_1(A_6, B_7, C_8)=k1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.50  tff(c_289, plain, (![B_73, A_74, C_75]: (k1_relset_1(B_73, A_74, k2_funct_1(C_75))=k1_relat_1(k2_funct_1(C_75)) | k2_relset_1(A_74, B_73, C_75)!=B_73 | ~v2_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))) | ~v1_funct_2(C_75, A_74, B_73) | ~v1_funct_1(C_75))), inference(resolution, [status(thm)], [c_229, c_12])).
% 3.22/1.50  tff(c_295, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_136, c_289])).
% 3.22/1.50  tff(c_299, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_138, c_36, c_135, c_295])).
% 3.22/1.50  tff(c_217, plain, (![A_61, B_62, C_63]: (k2_tops_2(A_61, B_62, C_63)=k2_funct_1(C_63) | ~v2_funct_1(C_63) | k2_relset_1(A_61, B_62, C_63)!=B_62 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(C_63, A_61, B_62) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.22/1.50  tff(c_220, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_136, c_217])).
% 3.22/1.50  tff(c_223, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_138, c_135, c_36, c_220])).
% 3.22/1.50  tff(c_34, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.50  tff(c_102, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_58, c_58, c_59, c_59, c_58, c_58, c_34])).
% 3.22/1.50  tff(c_103, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_102])).
% 3.22/1.50  tff(c_177, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_130, c_103])).
% 3.22/1.50  tff(c_224, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_177])).
% 3.22/1.50  tff(c_316, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_224])).
% 3.22/1.50  tff(c_323, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_316])).
% 3.22/1.50  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_44, c_36, c_323])).
% 3.22/1.50  tff(c_328, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_102])).
% 3.22/1.50  tff(c_417, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_365, c_328])).
% 3.22/1.50  tff(c_466, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_417])).
% 3.22/1.50  tff(c_546, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_466])).
% 3.22/1.50  tff(c_553, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_546])).
% 3.22/1.50  tff(c_555, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_44, c_36, c_553])).
% 3.22/1.50  tff(c_16, plain, (![A_12, B_13, C_14, D_15]: (k8_relset_1(A_12, B_13, C_14, D_15)=k10_relat_1(C_14, D_15) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.50  tff(c_406, plain, (![D_15]: (k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', D_15)=k10_relat_1('#skF_3', D_15))), inference(resolution, [status(thm)], [c_372, c_16])).
% 3.22/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.22/1.50  tff(c_375, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_58])).
% 3.22/1.50  tff(c_525, plain, (![B_108, A_109, C_110]: (k2_struct_0(B_108)=k1_xboole_0 | k8_relset_1(u1_struct_0(A_109), u1_struct_0(B_108), C_110, k2_struct_0(B_108))=k2_struct_0(A_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109), u1_struct_0(B_108)))) | ~v1_funct_2(C_110, u1_struct_0(A_109), u1_struct_0(B_108)) | ~v1_funct_1(C_110) | ~l1_struct_0(B_108) | ~l1_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.22/1.50  tff(c_534, plain, (![B_108, C_110]: (k2_struct_0(B_108)=k1_xboole_0 | k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_108), C_110, k2_struct_0(B_108))=k2_struct_0('#skF_1') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_108)))) | ~v1_funct_2(C_110, u1_struct_0('#skF_1'), u1_struct_0(B_108)) | ~v1_funct_1(C_110) | ~l1_struct_0(B_108) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_525])).
% 3.22/1.50  tff(c_556, plain, (![B_111, C_112]: (k2_struct_0(B_111)=k1_xboole_0 | k8_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_111), C_112, k2_struct_0(B_111))=k2_struct_0('#skF_1') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_111)))) | ~v1_funct_2(C_112, k2_struct_0('#skF_1'), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~l1_struct_0(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_59, c_59, c_534])).
% 3.22/1.50  tff(c_561, plain, (![C_112]: (k2_struct_0('#skF_2')=k1_xboole_0 | k8_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_112, k2_struct_0('#skF_2'))=k2_struct_0('#skF_1') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_112, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_112) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_375, c_556])).
% 3.22/1.50  tff(c_566, plain, (![C_112]: (k2_relat_1('#skF_3')=k1_xboole_0 | k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_112, k2_relat_1('#skF_3'))=k2_struct_0('#skF_1') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_112, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_112))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_375, c_375, c_365, c_365, c_561])).
% 3.22/1.50  tff(c_653, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_566])).
% 3.22/1.50  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.50  tff(c_69, plain, (![A_36]: (~v1_xboole_0(u1_struct_0(A_36)) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.50  tff(c_75, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_69])).
% 3.22/1.50  tff(c_79, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_75])).
% 3.22/1.50  tff(c_80, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_79])).
% 3.22/1.50  tff(c_373, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_80])).
% 3.22/1.50  tff(c_667, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_653, c_373])).
% 3.22/1.50  tff(c_671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_667])).
% 3.22/1.50  tff(c_674, plain, (![C_125]: (k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_125, k2_relat_1('#skF_3'))=k2_struct_0('#skF_1') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_125, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_125))), inference(splitRight, [status(thm)], [c_566])).
% 3.22/1.50  tff(c_681, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', k2_relat_1('#skF_3'))=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_674])).
% 3.22/1.50  tff(c_685, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_374, c_406, c_681])).
% 3.22/1.50  tff(c_4, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.22/1.50  tff(c_689, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_685, c_4])).
% 3.22/1.50  tff(c_696, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_689])).
% 3.22/1.50  tff(c_698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_555, c_696])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 148
% 3.22/1.50  #Fact    : 0
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 6
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.50  
% 3.22/1.50  Simplification rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Subsume      : 2
% 3.22/1.50  #Demod        : 197
% 3.22/1.50  #Tautology    : 72
% 3.22/1.50  #SimpNegUnit  : 4
% 3.22/1.50  #BackRed      : 42
% 3.22/1.50  
% 3.22/1.50  #Partial instantiations: 0
% 3.22/1.50  #Strategies tried      : 1
% 3.22/1.50  
% 3.22/1.50  Timing (in seconds)
% 3.22/1.50  ----------------------
% 3.22/1.50  Preprocessing        : 0.35
% 3.22/1.50  Parsing              : 0.19
% 3.22/1.50  CNF conversion       : 0.02
% 3.22/1.50  Main loop            : 0.37
% 3.22/1.50  Inferencing          : 0.13
% 3.22/1.50  Reduction            : 0.13
% 3.22/1.50  Demodulation         : 0.09
% 3.22/1.50  BG Simplification    : 0.02
% 3.22/1.50  Subsumption          : 0.06
% 3.22/1.50  Abstraction          : 0.02
% 3.22/1.50  MUC search           : 0.00
% 3.22/1.50  Cooper               : 0.00
% 3.22/1.50  Total                : 0.77
% 3.22/1.50  Index Insertion      : 0.00
% 3.22/1.50  Index Deletion       : 0.00
% 3.22/1.50  Index Matching       : 0.00
% 3.22/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

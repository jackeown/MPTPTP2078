%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1351+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:50 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 343 expanded)
%              Number of leaves         :   33 ( 157 expanded)
%              Depth                    :   10
%              Number of atoms          :  237 (2159 expanded)
%              Number of equality atoms :   11 (  45 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v2_connsp_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v3_tops_2,type,(
    v3_tops_2: ( $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v2_connsp_1,type,(
    v2_connsp_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( v3_tops_2(C,A,B)
                        & v2_connsp_1(D,B) )
                     => v2_connsp_1(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & v5_pre_topc(C,A,B)
                  & v5_pre_topc(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                      & v2_funct_1(C) )
                   => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k7_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v5_pre_topc(C,A,B)
                      & v2_connsp_1(D,A) )
                   => v2_connsp_1(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_2)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_28,plain,(
    v2_connsp_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_20,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_30,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_113,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(u1_struct_0(A_72),u1_struct_0(B_73),C_74) = k2_struct_0(B_73)
      | ~ v3_tops_2(C_74,A_72,B_73)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72),u1_struct_0(B_73))))
      | ~ v1_funct_2(C_74,u1_struct_0(A_72),u1_struct_0(B_73))
      | ~ v1_funct_1(C_74)
      | ~ l1_pre_topc(B_73)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,
    ( k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_113])).

tff(c_124,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_36,c_30,c_120])).

tff(c_73,plain,(
    ! [C_63,A_64,B_65] :
      ( v2_funct_1(C_63)
      | ~ v3_tops_2(C_63,A_64,B_65)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64),u1_struct_0(B_65))))
      | ~ v1_funct_2(C_63,u1_struct_0(A_64),u1_struct_0(B_65))
      | ~ v1_funct_1(C_63)
      | ~ l1_pre_topc(B_65)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_84,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_36,c_30,c_80])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    ! [A_54,B_55,C_56] :
      ( v1_funct_1(k2_tops_2(A_54,B_55,C_56))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_58,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_55])).

tff(c_138,plain,(
    ! [A_78,B_79,C_80] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_78),u1_struct_0(B_79),C_80),B_79,A_78)
      | ~ v3_tops_2(C_80,A_78,B_79)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0(B_79))))
      | ~ v1_funct_2(C_80,u1_struct_0(A_78),u1_struct_0(B_79))
      | ~ v1_funct_1(C_80)
      | ~ l1_pre_topc(B_79)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_143,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_138])).

tff(c_147,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_36,c_30,c_143])).

tff(c_59,plain,(
    ! [A_57,B_58,C_59] :
      ( v1_funct_2(k2_tops_2(A_57,B_58,C_59),B_58,A_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_64,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_61])).

tff(c_22,plain,(
    ! [B_20,A_12,C_24,D_26] :
      ( k7_relset_1(u1_struct_0(B_20),u1_struct_0(A_12),k2_tops_2(u1_struct_0(A_12),u1_struct_0(B_20),C_24),D_26) = k8_relset_1(u1_struct_0(A_12),u1_struct_0(B_20),C_24,D_26)
      | ~ v2_funct_1(C_24)
      | k2_relset_1(u1_struct_0(A_12),u1_struct_0(B_20),C_24) != k2_struct_0(B_20)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(u1_struct_0(B_20)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12),u1_struct_0(B_20))))
      | ~ v1_funct_2(C_24,u1_struct_0(A_12),u1_struct_0(B_20))
      | ~ v1_funct_1(C_24)
      | ~ l1_struct_0(B_20)
      | ~ l1_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k2_tops_2(A_8,B_9,C_10),k1_zfmisc_1(k2_zfmisc_1(B_9,A_8)))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_149,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( v2_connsp_1(k7_relset_1(u1_struct_0(A_84),u1_struct_0(B_85),C_86,D_87),B_85)
      | ~ v2_connsp_1(D_87,A_84)
      | ~ v5_pre_topc(C_86,A_84,B_85)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84),u1_struct_0(B_85))))
      | ~ v1_funct_2(C_86,u1_struct_0(A_84),u1_struct_0(B_85))
      | ~ v1_funct_1(C_86)
      | ~ l1_pre_topc(B_85)
      | ~ v2_pre_topc(B_85)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_230,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( v2_connsp_1(k7_relset_1(u1_struct_0(A_114),u1_struct_0(B_115),k2_tops_2(u1_struct_0(B_115),u1_struct_0(A_114),C_116),D_117),B_115)
      | ~ v2_connsp_1(D_117,A_114)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(B_115),u1_struct_0(A_114),C_116),A_114,B_115)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_115),u1_struct_0(A_114),C_116),u1_struct_0(A_114),u1_struct_0(B_115))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_115),u1_struct_0(A_114),C_116))
      | ~ l1_pre_topc(B_115)
      | ~ v2_pre_topc(B_115)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_115),u1_struct_0(A_114))))
      | ~ v1_funct_2(C_116,u1_struct_0(B_115),u1_struct_0(A_114))
      | ~ v1_funct_1(C_116) ) ),
    inference(resolution,[status(thm)],[c_14,c_149])).

tff(c_253,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( v2_connsp_1(k8_relset_1(u1_struct_0(A_130),u1_struct_0(B_131),C_132,D_133),A_130)
      | ~ v2_connsp_1(D_133,B_131)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_130),u1_struct_0(B_131),C_132),B_131,A_130)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(u1_struct_0(B_131)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_130),u1_struct_0(B_131),C_132),u1_struct_0(B_131),u1_struct_0(A_130))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_130),u1_struct_0(B_131),C_132))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130)
      | ~ l1_pre_topc(B_131)
      | ~ v2_pre_topc(B_131)
      | v2_struct_0(B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_130),u1_struct_0(B_131))))
      | ~ v1_funct_2(C_132,u1_struct_0(A_130),u1_struct_0(B_131))
      | ~ v1_funct_1(C_132)
      | ~ v2_funct_1(C_132)
      | k2_relset_1(u1_struct_0(A_130),u1_struct_0(B_131),C_132) != k2_struct_0(B_131)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(u1_struct_0(B_131)))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_130),u1_struct_0(B_131))))
      | ~ v1_funct_2(C_132,u1_struct_0(A_130),u1_struct_0(B_131))
      | ~ v1_funct_1(C_132)
      | ~ l1_struct_0(B_131)
      | ~ l1_struct_0(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_230])).

tff(c_258,plain,(
    ! [D_133] :
      ( v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_133),'#skF_1')
      | ~ v2_connsp_1(D_133,'#skF_2')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v2_funct_1('#skF_3')
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
      | ~ m1_subset_1(D_133,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_64,c_253])).

tff(c_262,plain,(
    ! [D_133] :
      ( v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_133),'#skF_1')
      | ~ v2_connsp_1(D_133,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_133,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_124,c_84,c_42,c_40,c_48,c_46,c_58,c_147,c_258])).

tff(c_263,plain,(
    ! [D_133] :
      ( v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_133),'#skF_1')
      | ~ v2_connsp_1(D_133,'#skF_2')
      | ~ m1_subset_1(D_133,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_262])).

tff(c_264,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_267,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_264])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_267])).

tff(c_272,plain,(
    ! [D_133] :
      ( ~ l1_struct_0('#skF_2')
      | v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_133),'#skF_1')
      | ~ v2_connsp_1(D_133,'#skF_2')
      | ~ m1_subset_1(D_133,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_274,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_277,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_274])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_277])).

tff(c_293,plain,(
    ! [D_137] :
      ( v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_137),'#skF_1')
      | ~ v2_connsp_1(D_137,'#skF_2')
      | ~ m1_subset_1(D_137,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_26,plain,(
    ~ v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_296,plain,
    ( ~ v2_connsp_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_293,c_26])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_296])).

%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:23:51 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
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

tff(f_149,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_86,axiom,(
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

tff(f_117,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_28,plain,(
    v2_connsp_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_30,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_113,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(u1_struct_0(A_72),u1_struct_0(B_73),C_74) = k2_struct_0(B_73)
      | ~ v3_tops_2(C_74,A_72,B_73)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72),u1_struct_0(B_73))))
      | ~ v1_funct_2(C_74,u1_struct_0(A_72),u1_struct_0(B_73))
      | ~ v1_funct_1(C_74)
      | ~ l1_pre_topc(B_73)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

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
    inference(cnfTransformation,[status(thm)],[f_53])).

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
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    ! [A_54,B_55,C_56] :
      ( v1_funct_1(k2_tops_2(A_54,B_55,C_56))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

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
    inference(cnfTransformation,[status(thm)],[f_53])).

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
    inference(cnfTransformation,[status(thm)],[f_65])).

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
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k2_tops_2(A_9,B_10,C_11),k1_zfmisc_1(k2_zfmisc_1(B_10,A_9)))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(C_11,A_9,B_10)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

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
    inference(cnfTransformation,[status(thm)],[f_117])).

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
    inference(resolution,[status(thm)],[c_16,c_149])).

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
    inference(resolution,[status(thm)],[c_2,c_264])).

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
    inference(resolution,[status(thm)],[c_2,c_274])).

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
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_296,plain,
    ( ~ v2_connsp_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_293,c_26])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:04:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.50  
% 2.89/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.51  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v2_connsp_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.89/1.51  
% 2.89/1.51  %Foreground sorts:
% 2.89/1.51  
% 2.89/1.51  
% 2.89/1.51  %Background operators:
% 2.89/1.51  
% 2.89/1.51  
% 2.89/1.51  %Foreground operators:
% 2.89/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.89/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.89/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.89/1.51  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 2.89/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.51  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.89/1.51  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.89/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.89/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.89/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.89/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.51  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.89/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.51  tff(v2_connsp_1, type, v2_connsp_1: ($i * $i) > $o).
% 2.89/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.89/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.51  
% 2.89/1.52  tff(f_149, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_tops_2(C, A, B) & v2_connsp_1(D, B)) => v2_connsp_1(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_2)).
% 2.89/1.52  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.89/1.52  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 2.89/1.52  tff(f_65, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 2.89/1.52  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k7_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_tops_2)).
% 2.89/1.52  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v5_pre_topc(C, A, B) & v2_connsp_1(D, A)) => v2_connsp_1(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tops_2)).
% 2.89/1.52  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_28, plain, (v2_connsp_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.89/1.52  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_36, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_30, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_113, plain, (![A_72, B_73, C_74]: (k2_relset_1(u1_struct_0(A_72), u1_struct_0(B_73), C_74)=k2_struct_0(B_73) | ~v3_tops_2(C_74, A_72, B_73) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72), u1_struct_0(B_73)))) | ~v1_funct_2(C_74, u1_struct_0(A_72), u1_struct_0(B_73)) | ~v1_funct_1(C_74) | ~l1_pre_topc(B_73) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.52  tff(c_120, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_113])).
% 2.89/1.52  tff(c_124, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_36, c_30, c_120])).
% 2.89/1.52  tff(c_73, plain, (![C_63, A_64, B_65]: (v2_funct_1(C_63) | ~v3_tops_2(C_63, A_64, B_65) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64), u1_struct_0(B_65)))) | ~v1_funct_2(C_63, u1_struct_0(A_64), u1_struct_0(B_65)) | ~v1_funct_1(C_63) | ~l1_pre_topc(B_65) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.52  tff(c_80, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_73])).
% 2.89/1.52  tff(c_84, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_36, c_30, c_80])).
% 2.89/1.52  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_52, plain, (![A_54, B_55, C_56]: (v1_funct_1(k2_tops_2(A_54, B_55, C_56)) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(C_56, A_54, B_55) | ~v1_funct_1(C_56))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.52  tff(c_55, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.89/1.52  tff(c_58, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_55])).
% 2.89/1.52  tff(c_138, plain, (![A_78, B_79, C_80]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_78), u1_struct_0(B_79), C_80), B_79, A_78) | ~v3_tops_2(C_80, A_78, B_79) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78), u1_struct_0(B_79)))) | ~v1_funct_2(C_80, u1_struct_0(A_78), u1_struct_0(B_79)) | ~v1_funct_1(C_80) | ~l1_pre_topc(B_79) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.52  tff(c_143, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_138])).
% 2.89/1.52  tff(c_147, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_36, c_30, c_143])).
% 2.89/1.52  tff(c_59, plain, (![A_57, B_58, C_59]: (v1_funct_2(k2_tops_2(A_57, B_58, C_59), B_58, A_57) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.52  tff(c_61, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_59])).
% 2.89/1.52  tff(c_64, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_61])).
% 2.89/1.52  tff(c_22, plain, (![B_20, A_12, C_24, D_26]: (k7_relset_1(u1_struct_0(B_20), u1_struct_0(A_12), k2_tops_2(u1_struct_0(A_12), u1_struct_0(B_20), C_24), D_26)=k8_relset_1(u1_struct_0(A_12), u1_struct_0(B_20), C_24, D_26) | ~v2_funct_1(C_24) | k2_relset_1(u1_struct_0(A_12), u1_struct_0(B_20), C_24)!=k2_struct_0(B_20) | ~m1_subset_1(D_26, k1_zfmisc_1(u1_struct_0(B_20))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12), u1_struct_0(B_20)))) | ~v1_funct_2(C_24, u1_struct_0(A_12), u1_struct_0(B_20)) | ~v1_funct_1(C_24) | ~l1_struct_0(B_20) | ~l1_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.89/1.52  tff(c_16, plain, (![A_9, B_10, C_11]: (m1_subset_1(k2_tops_2(A_9, B_10, C_11), k1_zfmisc_1(k2_zfmisc_1(B_10, A_9))) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_2(C_11, A_9, B_10) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.52  tff(c_149, plain, (![A_84, B_85, C_86, D_87]: (v2_connsp_1(k7_relset_1(u1_struct_0(A_84), u1_struct_0(B_85), C_86, D_87), B_85) | ~v2_connsp_1(D_87, A_84) | ~v5_pre_topc(C_86, A_84, B_85) | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84), u1_struct_0(B_85)))) | ~v1_funct_2(C_86, u1_struct_0(A_84), u1_struct_0(B_85)) | ~v1_funct_1(C_86) | ~l1_pre_topc(B_85) | ~v2_pre_topc(B_85) | v2_struct_0(B_85) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.89/1.52  tff(c_230, plain, (![A_114, B_115, C_116, D_117]: (v2_connsp_1(k7_relset_1(u1_struct_0(A_114), u1_struct_0(B_115), k2_tops_2(u1_struct_0(B_115), u1_struct_0(A_114), C_116), D_117), B_115) | ~v2_connsp_1(D_117, A_114) | ~v5_pre_topc(k2_tops_2(u1_struct_0(B_115), u1_struct_0(A_114), C_116), A_114, B_115) | ~m1_subset_1(D_117, k1_zfmisc_1(u1_struct_0(A_114))) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_115), u1_struct_0(A_114), C_116), u1_struct_0(A_114), u1_struct_0(B_115)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_115), u1_struct_0(A_114), C_116)) | ~l1_pre_topc(B_115) | ~v2_pre_topc(B_115) | v2_struct_0(B_115) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_115), u1_struct_0(A_114)))) | ~v1_funct_2(C_116, u1_struct_0(B_115), u1_struct_0(A_114)) | ~v1_funct_1(C_116))), inference(resolution, [status(thm)], [c_16, c_149])).
% 2.89/1.52  tff(c_253, plain, (![A_130, B_131, C_132, D_133]: (v2_connsp_1(k8_relset_1(u1_struct_0(A_130), u1_struct_0(B_131), C_132, D_133), A_130) | ~v2_connsp_1(D_133, B_131) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_130), u1_struct_0(B_131), C_132), B_131, A_130) | ~m1_subset_1(D_133, k1_zfmisc_1(u1_struct_0(B_131))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_130), u1_struct_0(B_131), C_132), u1_struct_0(B_131), u1_struct_0(A_130)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_130), u1_struct_0(B_131), C_132)) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130) | ~l1_pre_topc(B_131) | ~v2_pre_topc(B_131) | v2_struct_0(B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_130), u1_struct_0(B_131)))) | ~v1_funct_2(C_132, u1_struct_0(A_130), u1_struct_0(B_131)) | ~v1_funct_1(C_132) | ~v2_funct_1(C_132) | k2_relset_1(u1_struct_0(A_130), u1_struct_0(B_131), C_132)!=k2_struct_0(B_131) | ~m1_subset_1(D_133, k1_zfmisc_1(u1_struct_0(B_131))) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_130), u1_struct_0(B_131)))) | ~v1_funct_2(C_132, u1_struct_0(A_130), u1_struct_0(B_131)) | ~v1_funct_1(C_132) | ~l1_struct_0(B_131) | ~l1_struct_0(A_130))), inference(superposition, [status(thm), theory('equality')], [c_22, c_230])).
% 2.89/1.52  tff(c_258, plain, (![D_133]: (v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_133), '#skF_1') | ~v2_connsp_1(D_133, '#skF_2') | ~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1(D_133, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_253])).
% 2.89/1.52  tff(c_262, plain, (![D_133]: (v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_133), '#skF_1') | ~v2_connsp_1(D_133, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2') | ~m1_subset_1(D_133, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_124, c_84, c_42, c_40, c_48, c_46, c_58, c_147, c_258])).
% 2.89/1.52  tff(c_263, plain, (![D_133]: (v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_133), '#skF_1') | ~v2_connsp_1(D_133, '#skF_2') | ~m1_subset_1(D_133, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_262])).
% 2.89/1.52  tff(c_264, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_263])).
% 2.89/1.52  tff(c_267, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_264])).
% 2.89/1.52  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_267])).
% 2.89/1.52  tff(c_272, plain, (![D_133]: (~l1_struct_0('#skF_2') | v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_133), '#skF_1') | ~v2_connsp_1(D_133, '#skF_2') | ~m1_subset_1(D_133, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_263])).
% 2.89/1.52  tff(c_274, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_272])).
% 2.89/1.52  tff(c_277, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_274])).
% 2.89/1.52  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_277])).
% 2.89/1.52  tff(c_293, plain, (![D_137]: (v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_137), '#skF_1') | ~v2_connsp_1(D_137, '#skF_2') | ~m1_subset_1(D_137, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_272])).
% 2.89/1.52  tff(c_26, plain, (~v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.89/1.52  tff(c_296, plain, (~v2_connsp_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_293, c_26])).
% 2.89/1.52  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_296])).
% 2.89/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.52  
% 2.89/1.52  Inference rules
% 2.89/1.52  ----------------------
% 2.89/1.52  #Ref     : 0
% 2.89/1.52  #Sup     : 46
% 2.89/1.52  #Fact    : 0
% 2.89/1.52  #Define  : 0
% 2.89/1.52  #Split   : 3
% 2.89/1.52  #Chain   : 0
% 2.89/1.52  #Close   : 0
% 2.89/1.52  
% 2.89/1.52  Ordering : KBO
% 2.89/1.52  
% 2.89/1.52  Simplification rules
% 2.89/1.52  ----------------------
% 2.89/1.52  #Subsume      : 4
% 2.89/1.52  #Demod        : 90
% 2.89/1.52  #Tautology    : 12
% 2.89/1.52  #SimpNegUnit  : 2
% 2.89/1.52  #BackRed      : 0
% 2.89/1.52  
% 2.89/1.53  #Partial instantiations: 0
% 2.89/1.53  #Strategies tried      : 1
% 2.89/1.53  
% 2.89/1.53  Timing (in seconds)
% 2.89/1.53  ----------------------
% 3.23/1.53  Preprocessing        : 0.37
% 3.23/1.53  Parsing              : 0.20
% 3.23/1.53  CNF conversion       : 0.03
% 3.23/1.53  Main loop            : 0.34
% 3.23/1.53  Inferencing          : 0.14
% 3.23/1.53  Reduction            : 0.10
% 3.23/1.53  Demodulation         : 0.07
% 3.23/1.53  BG Simplification    : 0.02
% 3.23/1.53  Subsumption          : 0.07
% 3.23/1.53  Abstraction          : 0.01
% 3.23/1.53  MUC search           : 0.00
% 3.23/1.53  Cooper               : 0.00
% 3.23/1.53  Total                : 0.75
% 3.23/1.53  Index Insertion      : 0.00
% 3.23/1.53  Index Deletion       : 0.00
% 3.23/1.53  Index Matching       : 0.00
% 3.23/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

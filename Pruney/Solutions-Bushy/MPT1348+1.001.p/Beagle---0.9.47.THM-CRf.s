%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1348+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:50 EST 2020

% Result     : Theorem 9.19s
% Output     : CNFRefutation 9.58s
% Verified   : 
% Statistics : Number of formulae       :  188 (5068 expanded)
%              Number of leaves         :   39 (1888 expanded)
%              Depth                    :   23
%              Number of atoms          :  755 (33592 expanded)
%              Number of equality atoms :   62 (5958 expanded)
%              Maximal formula depth    :   32 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_tops_2(C,A,B)
                <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                    & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                       => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(B,D)) = k2_pre_topc(A,k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => r1_tarski(k2_pre_topc(A,k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)),k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(B,D))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_146,axiom,(
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

tff(f_125,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => r1_tarski(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(A,D)),k2_pre_topc(B,k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_54,axiom,(
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

tff(c_84,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_100,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_78,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_105,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_92,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_64,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_119,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_105,c_92,c_64])).

tff(c_120,plain,(
    ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_215,plain,(
    ! [A_131,B_132,C_133] :
      ( m1_subset_1('#skF_1'(A_131,B_132,C_133),k1_zfmisc_1(u1_struct_0(B_132)))
      | v5_pre_topc(C_133,A_131,B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131),u1_struct_0(B_132))))
      | ~ v1_funct_2(C_133,u1_struct_0(A_131),u1_struct_0(B_132))
      | ~ v1_funct_1(C_133)
      | ~ l1_pre_topc(B_132)
      | ~ v2_pre_topc(B_132)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_220,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_215])).

tff(c_224,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_46,c_220])).

tff(c_225,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k2_tops_2(A_12,B_13,C_14),k1_zfmisc_1(k2_zfmisc_1(B_13,A_12)))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_28,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_111,plain,(
    ! [A_100,B_101,C_102] :
      ( v1_funct_1(k2_tops_2(A_100,B_101,C_102))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(C_102,A_100,B_101)
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_114,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_111])).

tff(c_117,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_114])).

tff(c_121,plain,(
    ! [A_103,B_104,C_105] :
      ( v1_funct_2(k2_tops_2(A_103,B_104,C_105),B_104,A_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_2(C_105,A_103,B_104)
      | ~ v1_funct_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_123,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_121])).

tff(c_126,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_123])).

tff(c_66,plain,(
    ! [D_93] :
      ( v3_tops_2('#skF_5','#skF_3','#skF_4')
      | k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_93)) = k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_147,plain,(
    ! [D_93] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_93)) = k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_66])).

tff(c_42,plain,(
    ! [B_68,A_60,C_72,D_74] :
      ( k7_relset_1(u1_struct_0(B_68),u1_struct_0(A_60),k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),D_74) = k8_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72,D_74)
      | ~ v2_funct_1(C_72)
      | k2_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72) != k2_struct_0(B_68)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(B_68)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60),u1_struct_0(B_68))))
      | ~ v1_funct_2(C_72,u1_struct_0(A_60),u1_struct_0(B_68))
      | ~ v1_funct_1(C_72)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_305,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( r1_tarski(k7_relset_1(u1_struct_0(A_154),u1_struct_0(B_155),C_156,k2_pre_topc(A_154,D_157)),k2_pre_topc(B_155,k7_relset_1(u1_struct_0(A_154),u1_struct_0(B_155),C_156,D_157)))
      | ~ m1_subset_1(D_157,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ v5_pre_topc(C_156,A_154,B_155)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_154),u1_struct_0(B_155))))
      | ~ v1_funct_2(C_156,u1_struct_0(A_154),u1_struct_0(B_155))
      | ~ v1_funct_1(C_156)
      | ~ l1_pre_topc(B_155)
      | ~ v2_pre_topc(B_155)
      | v2_struct_0(B_155)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_957,plain,(
    ! [B_214,A_215,C_216,D_217] :
      ( r1_tarski(k7_relset_1(u1_struct_0(B_214),u1_struct_0(A_215),k2_tops_2(u1_struct_0(A_215),u1_struct_0(B_214),C_216),k2_pre_topc(B_214,D_217)),k2_pre_topc(A_215,k8_relset_1(u1_struct_0(A_215),u1_struct_0(B_214),C_216,D_217)))
      | ~ m1_subset_1(D_217,k1_zfmisc_1(u1_struct_0(B_214)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_215),u1_struct_0(B_214),C_216),B_214,A_215)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_215),u1_struct_0(B_214),C_216),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_214),u1_struct_0(A_215))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_215),u1_struct_0(B_214),C_216),u1_struct_0(B_214),u1_struct_0(A_215))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_215),u1_struct_0(B_214),C_216))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215)
      | ~ l1_pre_topc(B_214)
      | ~ v2_pre_topc(B_214)
      | ~ v2_funct_1(C_216)
      | k2_relset_1(u1_struct_0(A_215),u1_struct_0(B_214),C_216) != k2_struct_0(B_214)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(u1_struct_0(B_214)))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_215),u1_struct_0(B_214))))
      | ~ v1_funct_2(C_216,u1_struct_0(A_215),u1_struct_0(B_214))
      | ~ v1_funct_1(C_216)
      | ~ l1_struct_0(B_214)
      | ~ l1_struct_0(A_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_305])).

tff(c_978,plain,(
    ! [D_93] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_93))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ v2_funct_1('#skF_5')
      | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_957])).

tff(c_991,plain,(
    ! [D_93] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_93))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_105,c_92,c_52,c_50,c_56,c_54,c_117,c_126,c_978])).

tff(c_992,plain,(
    ! [D_93] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_93))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_991])).

tff(c_993,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_992])).

tff(c_996,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_993])).

tff(c_1000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_996])).

tff(c_1002,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_238,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( r1_tarski(k2_pre_topc(A_137,k8_relset_1(u1_struct_0(A_137),u1_struct_0(B_138),C_139,D_140)),k8_relset_1(u1_struct_0(A_137),u1_struct_0(B_138),C_139,k2_pre_topc(B_138,D_140)))
      | ~ m1_subset_1(D_140,k1_zfmisc_1(u1_struct_0(B_138)))
      | ~ v5_pre_topc(C_139,A_137,B_138)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_137),u1_struct_0(B_138))))
      | ~ v1_funct_2(C_139,u1_struct_0(A_137),u1_struct_0(B_138))
      | ~ v1_funct_1(C_139)
      | ~ l1_pre_topc(B_138)
      | ~ v2_pre_topc(B_138)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_243,plain,(
    ! [D_93] :
      ( r1_tarski(k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))),k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_93))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_238])).

tff(c_252,plain,(
    ! [D_141] :
      ( r1_tarski(k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_141))),k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_141))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_141),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_141,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_46,c_44,c_225,c_243])).

tff(c_262,plain,(
    ! [D_142] :
      ( r1_tarski(k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_142))),k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_142))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_142),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_142,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_142),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_252])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_377,plain,(
    ! [D_174] :
      ( k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_174))) = k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_174)))
      | ~ r1_tarski(k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_174))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_174))))
      | ~ m1_subset_1(D_174,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_174),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_262,c_2])).

tff(c_380,plain,(
    ! [D_93] :
      ( k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_93))) = k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93)))
      | ~ r1_tarski(k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_377])).

tff(c_385,plain,(
    ! [D_93] :
      ( k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_93))) = k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93)))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_380])).

tff(c_971,plain,(
    ! [D_93] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_93))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ v2_funct_1('#skF_5')
      | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_957])).

tff(c_988,plain,(
    ! [D_93] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_93))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | v2_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_105,c_92,c_52,c_50,c_56,c_54,c_117,c_126,c_971])).

tff(c_989,plain,(
    ! [D_93] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_93))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_988])).

tff(c_1004,plain,(
    ! [D_93] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_93))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_989])).

tff(c_1005,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1004])).

tff(c_1008,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_1005])).

tff(c_1012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1008])).

tff(c_1013,plain,(
    ! [D_93] :
      ( ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_93))),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_93))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_93),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1004])).

tff(c_1015,plain,(
    ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1013])).

tff(c_226,plain,(
    ! [A_134,B_135,C_136] :
      ( m1_subset_1('#skF_2'(A_134,B_135,C_136),k1_zfmisc_1(u1_struct_0(A_134)))
      | v5_pre_topc(C_136,A_134,B_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_134),u1_struct_0(B_135))))
      | ~ v1_funct_2(C_136,u1_struct_0(A_134),u1_struct_0(B_135))
      | ~ v1_funct_1(C_136)
      | ~ l1_pre_topc(B_135)
      | ~ v2_pre_topc(B_135)
      | v2_struct_0(B_135)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_232,plain,(
    ! [A_134,B_135,C_14] :
      ( m1_subset_1('#skF_2'(A_134,B_135,k2_tops_2(u1_struct_0(B_135),u1_struct_0(A_134),C_14)),k1_zfmisc_1(u1_struct_0(A_134)))
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_135),u1_struct_0(A_134),C_14),A_134,B_135)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_135),u1_struct_0(A_134),C_14),u1_struct_0(A_134),u1_struct_0(B_135))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_135),u1_struct_0(A_134),C_14))
      | ~ l1_pre_topc(B_135)
      | ~ v2_pre_topc(B_135)
      | v2_struct_0(B_135)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_135),u1_struct_0(A_134))))
      | ~ v1_funct_2(C_14,u1_struct_0(B_135),u1_struct_0(A_134))
      | ~ v1_funct_1(C_14) ) ),
    inference(resolution,[status(thm)],[c_22,c_226])).

tff(c_1014,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1004])).

tff(c_331,plain,(
    ! [A_161,B_162,C_163] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_161),u1_struct_0(B_162),C_163,k2_pre_topc(A_161,'#skF_2'(A_161,B_162,C_163))),k2_pre_topc(B_162,k7_relset_1(u1_struct_0(A_161),u1_struct_0(B_162),C_163,'#skF_2'(A_161,B_162,C_163))))
      | v5_pre_topc(C_163,A_161,B_162)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_161),u1_struct_0(B_162))))
      | ~ v1_funct_2(C_163,u1_struct_0(A_161),u1_struct_0(B_162))
      | ~ v1_funct_1(C_163)
      | ~ l1_pre_topc(B_162)
      | ~ v2_pre_topc(B_162)
      | v2_struct_0(B_162)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1638,plain,(
    ! [A_234,B_235,C_236] :
      ( ~ r1_tarski(k8_relset_1(u1_struct_0(A_234),u1_struct_0(B_235),C_236,k2_pre_topc(B_235,'#skF_2'(B_235,A_234,k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_235),C_236)))),k2_pre_topc(A_234,k7_relset_1(u1_struct_0(B_235),u1_struct_0(A_234),k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_235),C_236),'#skF_2'(B_235,A_234,k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_235),C_236)))))
      | v5_pre_topc(k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_235),C_236),B_235,A_234)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_235),C_236),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_235),u1_struct_0(A_234))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_235),C_236),u1_struct_0(B_235),u1_struct_0(A_234))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_235),C_236))
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234)
      | ~ l1_pre_topc(B_235)
      | ~ v2_pre_topc(B_235)
      | ~ v2_funct_1(C_236)
      | k2_relset_1(u1_struct_0(A_234),u1_struct_0(B_235),C_236) != k2_struct_0(B_235)
      | ~ m1_subset_1(k2_pre_topc(B_235,'#skF_2'(B_235,A_234,k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_235),C_236))),k1_zfmisc_1(u1_struct_0(B_235)))
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_234),u1_struct_0(B_235))))
      | ~ v1_funct_2(C_236,u1_struct_0(A_234),u1_struct_0(B_235))
      | ~ v1_funct_1(C_236)
      | ~ l1_struct_0(B_235)
      | ~ l1_struct_0(A_234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_331])).

tff(c_1650,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k2_pre_topc('#skF_3',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_1638])).

tff(c_1653,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k2_pre_topc('#skF_3',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_1014,c_48,c_46,c_44,c_105,c_92,c_52,c_50,c_56,c_54,c_117,c_126,c_1650])).

tff(c_1654,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k2_pre_topc('#skF_3',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1015,c_1653])).

tff(c_1655,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1654])).

tff(c_1658,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_232,c_1655])).

tff(c_1661,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_52,c_50,c_56,c_54,c_117,c_126,c_1658])).

tff(c_1663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1015,c_1661])).

tff(c_1665,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1654])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k2_pre_topc(A_10,B_11),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1664,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ r1_tarski(k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k2_pre_topc('#skF_3',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_1654])).

tff(c_1666,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k2_pre_topc('#skF_3',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))))) ),
    inference(splitLeft,[status(thm)],[c_1664])).

tff(c_1669,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))))
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1666])).

tff(c_1672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_1014,c_48,c_46,c_44,c_1665,c_105,c_92,c_6,c_1669])).

tff(c_1673,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1664])).

tff(c_1675,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1673])).

tff(c_1679,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1675])).

tff(c_1683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1665,c_1679])).

tff(c_1684,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_1673])).

tff(c_1688,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1684])).

tff(c_1692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1688])).

tff(c_1694,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1013])).

tff(c_8,plain,(
    ! [C_9,A_3,B_7] :
      ( v3_tops_2(C_9,A_3,B_7)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_3),u1_struct_0(B_7),C_9),B_7,A_3)
      | ~ v5_pre_topc(C_9,A_3,B_7)
      | ~ v2_funct_1(C_9)
      | k2_relset_1(u1_struct_0(A_3),u1_struct_0(B_7),C_9) != k2_struct_0(B_7)
      | k1_relset_1(u1_struct_0(A_3),u1_struct_0(B_7),C_9) != k2_struct_0(A_3)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3),u1_struct_0(B_7))))
      | ~ v1_funct_2(C_9,u1_struct_0(A_3),u1_struct_0(B_7))
      | ~ v1_funct_1(C_9)
      | ~ l1_pre_topc(B_7)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1696,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1694,c_8])).

tff(c_1699,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_44,c_100,c_105,c_92,c_225,c_1696])).

tff(c_1701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_1699])).

tff(c_1703,plain,(
    ~ v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_1702,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_1732,plain,(
    ! [A_247,B_248,C_249] :
      ( ~ r1_tarski(k2_pre_topc(A_247,k8_relset_1(u1_struct_0(A_247),u1_struct_0(B_248),C_249,'#skF_1'(A_247,B_248,C_249))),k8_relset_1(u1_struct_0(A_247),u1_struct_0(B_248),C_249,k2_pre_topc(B_248,'#skF_1'(A_247,B_248,C_249))))
      | v5_pre_topc(C_249,A_247,B_248)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247),u1_struct_0(B_248))))
      | ~ v1_funct_2(C_249,u1_struct_0(A_247),u1_struct_0(B_248))
      | ~ v1_funct_1(C_249)
      | ~ l1_pre_topc(B_248)
      | ~ v2_pre_topc(B_248)
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1740,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))),k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_1732])).

tff(c_1743,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1702,c_56,c_54,c_52,c_50,c_48,c_46,c_44,c_6,c_1740])).

tff(c_1745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1703,c_1743])).

tff(c_1746,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_1747,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_1822,plain,(
    ! [A_271,B_272,C_273] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_271),u1_struct_0(B_272),C_273),B_272,A_271)
      | ~ v3_tops_2(C_273,A_271,B_272)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_271),u1_struct_0(B_272))))
      | ~ v1_funct_2(C_273,u1_struct_0(A_271),u1_struct_0(B_272))
      | ~ v1_funct_1(C_273)
      | ~ l1_pre_topc(B_272)
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1827,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1822])).

tff(c_1831,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_1747,c_1827])).

tff(c_1775,plain,(
    ! [C_259,A_260,B_261] :
      ( v5_pre_topc(C_259,A_260,B_261)
      | ~ v3_tops_2(C_259,A_260,B_261)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_260),u1_struct_0(B_261))))
      | ~ v1_funct_2(C_259,u1_struct_0(A_260),u1_struct_0(B_261))
      | ~ v1_funct_1(C_259)
      | ~ l1_pre_topc(B_261)
      | ~ l1_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1782,plain,
    ( v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1775])).

tff(c_1786,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_1747,c_1782])).

tff(c_1749,plain,(
    ! [A_250,B_251,C_252] :
      ( v1_funct_2(k2_tops_2(A_250,B_251,C_252),B_251,A_250)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ v1_funct_2(C_252,A_250,B_251)
      | ~ v1_funct_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1751,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1749])).

tff(c_1754,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1751])).

tff(c_1872,plain,(
    ! [B_297,A_298,C_299,D_300] :
      ( k7_relset_1(u1_struct_0(B_297),u1_struct_0(A_298),k2_tops_2(u1_struct_0(A_298),u1_struct_0(B_297),C_299),D_300) = k8_relset_1(u1_struct_0(A_298),u1_struct_0(B_297),C_299,D_300)
      | ~ v2_funct_1(C_299)
      | k2_relset_1(u1_struct_0(A_298),u1_struct_0(B_297),C_299) != k2_struct_0(B_297)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(u1_struct_0(B_297)))
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_298),u1_struct_0(B_297))))
      | ~ v1_funct_2(C_299,u1_struct_0(A_298),u1_struct_0(B_297))
      | ~ v1_funct_1(C_299)
      | ~ l1_struct_0(B_297)
      | ~ l1_struct_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    ! [A_38,B_50,C_56,D_59] :
      ( r1_tarski(k7_relset_1(u1_struct_0(A_38),u1_struct_0(B_50),C_56,k2_pre_topc(A_38,D_59)),k2_pre_topc(B_50,k7_relset_1(u1_struct_0(A_38),u1_struct_0(B_50),C_56,D_59)))
      | ~ m1_subset_1(D_59,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ v5_pre_topc(C_56,A_38,B_50)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38),u1_struct_0(B_50))))
      | ~ v1_funct_2(C_56,u1_struct_0(A_38),u1_struct_0(B_50))
      | ~ v1_funct_1(C_56)
      | ~ l1_pre_topc(B_50)
      | ~ v2_pre_topc(B_50)
      | v2_struct_0(B_50)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2000,plain,(
    ! [B_351,A_352,C_353,D_354] :
      ( r1_tarski(k7_relset_1(u1_struct_0(B_351),u1_struct_0(A_352),k2_tops_2(u1_struct_0(A_352),u1_struct_0(B_351),C_353),k2_pre_topc(B_351,D_354)),k2_pre_topc(A_352,k8_relset_1(u1_struct_0(A_352),u1_struct_0(B_351),C_353,D_354)))
      | ~ m1_subset_1(D_354,k1_zfmisc_1(u1_struct_0(B_351)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_352),u1_struct_0(B_351),C_353),B_351,A_352)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_352),u1_struct_0(B_351),C_353),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_351),u1_struct_0(A_352))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_352),u1_struct_0(B_351),C_353),u1_struct_0(B_351),u1_struct_0(A_352))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_352),u1_struct_0(B_351),C_353))
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352)
      | ~ l1_pre_topc(B_351)
      | ~ v2_pre_topc(B_351)
      | ~ v2_funct_1(C_353)
      | k2_relset_1(u1_struct_0(A_352),u1_struct_0(B_351),C_353) != k2_struct_0(B_351)
      | ~ m1_subset_1(D_354,k1_zfmisc_1(u1_struct_0(B_351)))
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_352),u1_struct_0(B_351))))
      | ~ v1_funct_2(C_353,u1_struct_0(A_352),u1_struct_0(B_351))
      | ~ v1_funct_1(C_353)
      | ~ l1_struct_0(B_351)
      | ~ l1_struct_0(A_352) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1872,c_36])).

tff(c_2059,plain,(
    ! [A_387,B_388,C_389,D_390] :
      ( r1_tarski(k8_relset_1(u1_struct_0(A_387),u1_struct_0(B_388),C_389,k2_pre_topc(B_388,D_390)),k2_pre_topc(A_387,k8_relset_1(u1_struct_0(A_387),u1_struct_0(B_388),C_389,D_390)))
      | ~ m1_subset_1(D_390,k1_zfmisc_1(u1_struct_0(B_388)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_387),u1_struct_0(B_388),C_389),B_388,A_387)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_387),u1_struct_0(B_388),C_389),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_388),u1_struct_0(A_387))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_387),u1_struct_0(B_388),C_389),u1_struct_0(B_388),u1_struct_0(A_387))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_387),u1_struct_0(B_388),C_389))
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387)
      | ~ l1_pre_topc(B_388)
      | ~ v2_pre_topc(B_388)
      | ~ v2_funct_1(C_389)
      | k2_relset_1(u1_struct_0(A_387),u1_struct_0(B_388),C_389) != k2_struct_0(B_388)
      | ~ m1_subset_1(D_390,k1_zfmisc_1(u1_struct_0(B_388)))
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_387),u1_struct_0(B_388))))
      | ~ v1_funct_2(C_389,u1_struct_0(A_387),u1_struct_0(B_388))
      | ~ v1_funct_1(C_389)
      | ~ l1_struct_0(B_388)
      | ~ l1_struct_0(A_387)
      | ~ v2_funct_1(C_389)
      | k2_relset_1(u1_struct_0(A_387),u1_struct_0(B_388),C_389) != k2_struct_0(B_388)
      | ~ m1_subset_1(k2_pre_topc(B_388,D_390),k1_zfmisc_1(u1_struct_0(B_388)))
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_387),u1_struct_0(B_388))))
      | ~ v1_funct_2(C_389,u1_struct_0(A_387),u1_struct_0(B_388))
      | ~ v1_funct_1(C_389)
      | ~ l1_struct_0(B_388)
      | ~ l1_struct_0(A_387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2000])).

tff(c_1855,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( r1_tarski(k2_pre_topc(A_283,k8_relset_1(u1_struct_0(A_283),u1_struct_0(B_284),C_285,D_286)),k8_relset_1(u1_struct_0(A_283),u1_struct_0(B_284),C_285,k2_pre_topc(B_284,D_286)))
      | ~ m1_subset_1(D_286,k1_zfmisc_1(u1_struct_0(B_284)))
      | ~ v5_pre_topc(C_285,A_283,B_284)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283),u1_struct_0(B_284))))
      | ~ v1_funct_2(C_285,u1_struct_0(A_283),u1_struct_0(B_284))
      | ~ v1_funct_1(C_285)
      | ~ l1_pre_topc(B_284)
      | ~ v2_pre_topc(B_284)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1858,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( k8_relset_1(u1_struct_0(A_283),u1_struct_0(B_284),C_285,k2_pre_topc(B_284,D_286)) = k2_pre_topc(A_283,k8_relset_1(u1_struct_0(A_283),u1_struct_0(B_284),C_285,D_286))
      | ~ r1_tarski(k8_relset_1(u1_struct_0(A_283),u1_struct_0(B_284),C_285,k2_pre_topc(B_284,D_286)),k2_pre_topc(A_283,k8_relset_1(u1_struct_0(A_283),u1_struct_0(B_284),C_285,D_286)))
      | ~ m1_subset_1(D_286,k1_zfmisc_1(u1_struct_0(B_284)))
      | ~ v5_pre_topc(C_285,A_283,B_284)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283),u1_struct_0(B_284))))
      | ~ v1_funct_2(C_285,u1_struct_0(A_283),u1_struct_0(B_284))
      | ~ v1_funct_1(C_285)
      | ~ l1_pre_topc(B_284)
      | ~ v2_pre_topc(B_284)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283) ) ),
    inference(resolution,[status(thm)],[c_1855,c_2])).

tff(c_2067,plain,(
    ! [A_391,B_392,C_393,D_394] :
      ( k8_relset_1(u1_struct_0(A_391),u1_struct_0(B_392),C_393,k2_pre_topc(B_392,D_394)) = k2_pre_topc(A_391,k8_relset_1(u1_struct_0(A_391),u1_struct_0(B_392),C_393,D_394))
      | ~ v5_pre_topc(C_393,A_391,B_392)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_391),u1_struct_0(B_392),C_393),B_392,A_391)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_391),u1_struct_0(B_392),C_393),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_392),u1_struct_0(A_391))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_391),u1_struct_0(B_392),C_393),u1_struct_0(B_392),u1_struct_0(A_391))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_391),u1_struct_0(B_392),C_393))
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391)
      | ~ l1_pre_topc(B_392)
      | ~ v2_pre_topc(B_392)
      | ~ m1_subset_1(D_394,k1_zfmisc_1(u1_struct_0(B_392)))
      | ~ v2_funct_1(C_393)
      | k2_relset_1(u1_struct_0(A_391),u1_struct_0(B_392),C_393) != k2_struct_0(B_392)
      | ~ m1_subset_1(k2_pre_topc(B_392,D_394),k1_zfmisc_1(u1_struct_0(B_392)))
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_391),u1_struct_0(B_392))))
      | ~ v1_funct_2(C_393,u1_struct_0(A_391),u1_struct_0(B_392))
      | ~ v1_funct_1(C_393)
      | ~ l1_struct_0(B_392)
      | ~ l1_struct_0(A_391) ) ),
    inference(resolution,[status(thm)],[c_2059,c_1858])).

tff(c_2072,plain,(
    ! [A_395,B_396,C_397,D_398] :
      ( k8_relset_1(u1_struct_0(A_395),u1_struct_0(B_396),C_397,k2_pre_topc(B_396,D_398)) = k2_pre_topc(A_395,k8_relset_1(u1_struct_0(A_395),u1_struct_0(B_396),C_397,D_398))
      | ~ v5_pre_topc(C_397,A_395,B_396)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_395),u1_struct_0(B_396),C_397),B_396,A_395)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_395),u1_struct_0(B_396),C_397),u1_struct_0(B_396),u1_struct_0(A_395))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_395),u1_struct_0(B_396),C_397))
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395)
      | ~ l1_pre_topc(B_396)
      | ~ v2_pre_topc(B_396)
      | ~ m1_subset_1(D_398,k1_zfmisc_1(u1_struct_0(B_396)))
      | ~ v2_funct_1(C_397)
      | k2_relset_1(u1_struct_0(A_395),u1_struct_0(B_396),C_397) != k2_struct_0(B_396)
      | ~ m1_subset_1(k2_pre_topc(B_396,D_398),k1_zfmisc_1(u1_struct_0(B_396)))
      | ~ l1_struct_0(B_396)
      | ~ l1_struct_0(A_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),u1_struct_0(B_396))))
      | ~ v1_funct_2(C_397,u1_struct_0(A_395),u1_struct_0(B_396))
      | ~ v1_funct_1(C_397) ) ),
    inference(resolution,[status(thm)],[c_22,c_2067])).

tff(c_2077,plain,(
    ! [D_398] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_398)) = k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_398))
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1(D_398,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_funct_1('#skF_5')
      | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_398),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1754,c_2072])).

tff(c_2081,plain,(
    ! [D_398] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_398)) = k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_398))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(D_398,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_398),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_105,c_92,c_52,c_50,c_56,c_54,c_117,c_1831,c_1786,c_2077])).

tff(c_2082,plain,(
    ! [D_398] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_398)) = k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_398))
      | ~ m1_subset_1(D_398,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_398),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2081])).

tff(c_2083,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2082])).

tff(c_2086,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_2083])).

tff(c_2090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2086])).

tff(c_2091,plain,(
    ! [D_398] :
      ( ~ l1_struct_0('#skF_4')
      | k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_398)) = k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_398))
      | ~ m1_subset_1(D_398,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_398),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_2082])).

tff(c_2093,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2091])).

tff(c_2096,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_2093])).

tff(c_2100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2096])).

tff(c_2103,plain,(
    ! [D_399] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',D_399)) = k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_399))
      | ~ m1_subset_1(D_399,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_399),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_2091])).

tff(c_2107,plain,(
    ! [B_11] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',B_11)) = k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',B_11))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_2103])).

tff(c_2111,plain,(
    ! [B_400] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',B_400)) = k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',B_400))
      | ~ m1_subset_1(B_400,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2107])).

tff(c_62,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4','#skF_6')) != k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'))
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1812,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4','#skF_6')) != k2_pre_topc('#skF_3',k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_100,c_105,c_92,c_62])).

tff(c_2161,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2111,c_1812])).

tff(c_2206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_2161])).

tff(c_2208,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2207,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2270,plain,(
    ! [A_421,B_422,C_423] :
      ( k2_relset_1(u1_struct_0(A_421),u1_struct_0(B_422),C_423) = k2_struct_0(B_422)
      | ~ v3_tops_2(C_423,A_421,B_422)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_421),u1_struct_0(B_422))))
      | ~ v1_funct_2(C_423,u1_struct_0(A_421),u1_struct_0(B_422))
      | ~ v1_funct_1(C_423)
      | ~ l1_pre_topc(B_422)
      | ~ l1_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2277,plain,
    ( k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_2270])).

tff(c_2281,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_2207,c_2277])).

tff(c_2283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2208,c_2281])).

tff(c_2285,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2284,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2340,plain,(
    ! [A_441,B_442,C_443] :
      ( k1_relset_1(u1_struct_0(A_441),u1_struct_0(B_442),C_443) = k2_struct_0(A_441)
      | ~ v3_tops_2(C_443,A_441,B_442)
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_441),u1_struct_0(B_442))))
      | ~ v1_funct_2(C_443,u1_struct_0(A_441),u1_struct_0(B_442))
      | ~ v1_funct_1(C_443)
      | ~ l1_pre_topc(B_442)
      | ~ l1_pre_topc(A_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2347,plain,
    ( k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_2340])).

tff(c_2351,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_2284,c_2347])).

tff(c_2353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2285,c_2351])).

tff(c_2355,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2354,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2387,plain,(
    ! [C_457,A_458,B_459] :
      ( v2_funct_1(C_457)
      | ~ v3_tops_2(C_457,A_458,B_459)
      | ~ m1_subset_1(C_457,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_458),u1_struct_0(B_459))))
      | ~ v1_funct_2(C_457,u1_struct_0(A_458),u1_struct_0(B_459))
      | ~ v1_funct_1(C_457)
      | ~ l1_pre_topc(B_459)
      | ~ l1_pre_topc(A_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2394,plain,
    ( v2_funct_1('#skF_5')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_2387])).

tff(c_2398,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_2354,c_2394])).

tff(c_2400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2355,c_2398])).

%------------------------------------------------------------------------------

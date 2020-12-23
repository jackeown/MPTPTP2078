%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:41 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 345 expanded)
%              Number of leaves         :   40 ( 140 expanded)
%              Depth                    :   18
%              Number of atoms          :  253 (1744 expanded)
%              Number of equality atoms :   27 ( 195 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & v5_pre_topc(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_borsuk_1(C,A,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( D = E
                           => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_44,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_64,plain,(
    ! [B_85,A_86] :
      ( l1_pre_topc(B_85)
      | ~ m1_pre_topc(B_85,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_64])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_67])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_161,plain,(
    ! [A_96,B_97] :
      ( m1_pre_topc(k1_tex_2(A_96,B_97),A_96)
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_163,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_161])).

tff(c_168,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_163])).

tff(c_169,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_168])).

tff(c_146,plain,(
    ! [A_94,B_95] :
      ( ~ v2_struct_0(k1_tex_2(A_94,B_95))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l1_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_149,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_146])).

tff(c_155,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_149])).

tff(c_156,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_155])).

tff(c_131,plain,(
    ! [A_92,B_93] :
      ( v1_pre_topc(k1_tex_2(A_92,B_93))
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l1_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_134,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_131])).

tff(c_140,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_134])).

tff(c_141,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_140])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_88,B_89] :
      ( k6_domain_1(A_88,B_89) = k1_tarski(B_89)
      | ~ m1_subset_1(B_89,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_85,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_91,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_88])).

tff(c_94,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_91])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_94])).

tff(c_99,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_275,plain,(
    ! [A_114,B_115] :
      ( k6_domain_1(u1_struct_0(A_114),B_115) = u1_struct_0(k1_tex_2(A_114,B_115))
      | ~ m1_pre_topc(k1_tex_2(A_114,B_115),A_114)
      | ~ v1_pre_topc(k1_tex_2(A_114,B_115))
      | v2_struct_0(k1_tex_2(A_114,B_115))
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_279,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_169,c_275])).

tff(c_286,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4')
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_32,c_141,c_99,c_279])).

tff(c_287,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_156,c_286])).

tff(c_12,plain,(
    ! [B_17,A_15] :
      ( m1_subset_1(u1_struct_0(B_17),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_pre_topc(B_17,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_744,plain,(
    ! [A_149] :
      ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),A_149)
      | ~ l1_pre_topc(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_12])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_28,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_57,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_84,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_57,c_72])).

tff(c_111,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_114,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_111,c_6])).

tff(c_117,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_114])).

tff(c_120,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_117])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_120])).

tff(c_125,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_26,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_58,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_106,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_58])).

tff(c_186,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_106])).

tff(c_46,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_38,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_34,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_187,plain,(
    ! [C_98,A_99,B_100] :
      ( m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(B_100)))
      | ~ m1_pre_topc(B_100,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_227,plain,(
    ! [B_106,A_107,A_108] :
      ( m1_subset_1(u1_struct_0(B_106),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_pre_topc(A_108,A_107)
      | ~ l1_pre_topc(A_107)
      | ~ m1_pre_topc(B_106,A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_12,c_187])).

tff(c_233,plain,(
    ! [B_106] :
      ( m1_subset_1(u1_struct_0(B_106),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_106,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_227])).

tff(c_242,plain,(
    ! [B_106] :
      ( m1_subset_1(u1_struct_0(B_106),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_106,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_50,c_233])).

tff(c_360,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_242])).

tff(c_389,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_360])).

tff(c_424,plain,(
    ! [A_116,B_117,C_118,E_119] :
      ( k8_relset_1(u1_struct_0(A_116),u1_struct_0(B_117),C_118,E_119) = k2_pre_topc(A_116,E_119)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(E_119,k1_zfmisc_1(u1_struct_0(B_117)))
      | ~ v3_borsuk_1(C_118,A_116,B_117)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116),u1_struct_0(B_117))))
      | ~ v5_pre_topc(C_118,A_116,B_117)
      | ~ v1_funct_2(C_118,u1_struct_0(A_116),u1_struct_0(B_117))
      | ~ v1_funct_1(C_118)
      | ~ m1_pre_topc(B_117,A_116)
      | ~ v4_tex_2(B_117,A_116)
      | v2_struct_0(B_117)
      | ~ l1_pre_topc(A_116)
      | ~ v3_tdlat_3(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_426,plain,(
    ! [B_117,C_118] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_117),C_118,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_117)))
      | ~ v3_borsuk_1(C_118,'#skF_1',B_117)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_117))))
      | ~ v5_pre_topc(C_118,'#skF_1',B_117)
      | ~ v1_funct_2(C_118,u1_struct_0('#skF_1'),u1_struct_0(B_117))
      | ~ v1_funct_1(C_118)
      | ~ m1_pre_topc(B_117,'#skF_1')
      | ~ v4_tex_2(B_117,'#skF_1')
      | v2_struct_0(B_117)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_389,c_424])).

tff(c_443,plain,(
    ! [B_117,C_118] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_117),C_118,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_117)))
      | ~ v3_borsuk_1(C_118,'#skF_1',B_117)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_117))))
      | ~ v5_pre_topc(C_118,'#skF_1',B_117)
      | ~ v1_funct_2(C_118,u1_struct_0('#skF_1'),u1_struct_0(B_117))
      | ~ v1_funct_1(C_118)
      | ~ m1_pre_topc(B_117,'#skF_1')
      | ~ v4_tex_2(B_117,'#skF_1')
      | v2_struct_0(B_117)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_426])).

tff(c_467,plain,(
    ! [B_122,C_123] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_122),C_123,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_122)))
      | ~ v3_borsuk_1(C_123,'#skF_1',B_122)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_122))))
      | ~ v5_pre_topc(C_123,'#skF_1',B_122)
      | ~ v1_funct_2(C_123,u1_struct_0('#skF_1'),u1_struct_0(B_122))
      | ~ v1_funct_1(C_123)
      | ~ m1_pre_topc(B_122,'#skF_1')
      | ~ v4_tex_2(B_122,'#skF_1')
      | v2_struct_0(B_122) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_443])).

tff(c_476,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v4_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_467])).

tff(c_484,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_34,c_476])).

tff(c_485,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_186,c_484])).

tff(c_747,plain,
    ( ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_744,c_485])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_169,c_747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:09:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.51  
% 3.17/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.51  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.17/1.51  
% 3.17/1.51  %Foreground sorts:
% 3.17/1.51  
% 3.17/1.51  
% 3.17/1.51  %Background operators:
% 3.17/1.51  
% 3.17/1.51  
% 3.17/1.51  %Foreground operators:
% 3.17/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.17/1.51  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.17/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.17/1.51  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.17/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.17/1.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.17/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.17/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.51  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.17/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.17/1.51  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.17/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.51  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.17/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.51  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.17/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.17/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.17/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.17/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.17/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.51  
% 3.54/1.53  tff(f_179, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.54/1.53  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.54/1.53  tff(f_102, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.54/1.53  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.54/1.53  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.54/1.53  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.54/1.53  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 3.54/1.53  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.54/1.53  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 3.54/1.53  tff(f_140, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.54/1.53  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_44, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_64, plain, (![B_85, A_86]: (l1_pre_topc(B_85) | ~m1_pre_topc(B_85, A_86) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.54/1.53  tff(c_67, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_64])).
% 3.54/1.53  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_67])).
% 3.54/1.53  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_161, plain, (![A_96, B_97]: (m1_pre_topc(k1_tex_2(A_96, B_97), A_96) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.54/1.53  tff(c_163, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_161])).
% 3.54/1.53  tff(c_168, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_163])).
% 3.54/1.53  tff(c_169, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_168])).
% 3.54/1.53  tff(c_146, plain, (![A_94, B_95]: (~v2_struct_0(k1_tex_2(A_94, B_95)) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l1_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.54/1.53  tff(c_149, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_146])).
% 3.54/1.53  tff(c_155, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_149])).
% 3.54/1.53  tff(c_156, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_155])).
% 3.54/1.53  tff(c_131, plain, (![A_92, B_93]: (v1_pre_topc(k1_tex_2(A_92, B_93)) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l1_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.54/1.53  tff(c_134, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_131])).
% 3.54/1.53  tff(c_140, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_134])).
% 3.54/1.53  tff(c_141, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_140])).
% 3.54/1.53  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.54/1.53  tff(c_72, plain, (![A_88, B_89]: (k6_domain_1(A_88, B_89)=k1_tarski(B_89) | ~m1_subset_1(B_89, A_88) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.53  tff(c_83, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_72])).
% 3.54/1.53  tff(c_85, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_83])).
% 3.54/1.53  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.54/1.53  tff(c_88, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_85, c_6])).
% 3.54/1.53  tff(c_91, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_88])).
% 3.54/1.53  tff(c_94, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_91])).
% 3.54/1.53  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_94])).
% 3.54/1.53  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_83])).
% 3.54/1.53  tff(c_275, plain, (![A_114, B_115]: (k6_domain_1(u1_struct_0(A_114), B_115)=u1_struct_0(k1_tex_2(A_114, B_115)) | ~m1_pre_topc(k1_tex_2(A_114, B_115), A_114) | ~v1_pre_topc(k1_tex_2(A_114, B_115)) | v2_struct_0(k1_tex_2(A_114, B_115)) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.54/1.53  tff(c_279, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_169, c_275])).
% 3.54/1.53  tff(c_286, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4') | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_32, c_141, c_99, c_279])).
% 3.54/1.53  tff(c_287, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_156, c_286])).
% 3.54/1.53  tff(c_12, plain, (![B_17, A_15]: (m1_subset_1(u1_struct_0(B_17), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_pre_topc(B_17, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.54/1.53  tff(c_744, plain, (![A_149]: (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), A_149) | ~l1_pre_topc(A_149))), inference(superposition, [status(thm), theory('equality')], [c_287, c_12])).
% 3.54/1.53  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_28, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_57, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 3.54/1.53  tff(c_84, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_57, c_72])).
% 3.54/1.53  tff(c_111, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_84])).
% 3.54/1.53  tff(c_114, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_111, c_6])).
% 3.54/1.53  tff(c_117, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_114])).
% 3.54/1.53  tff(c_120, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_117])).
% 3.54/1.53  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_120])).
% 3.54/1.53  tff(c_125, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 3.54/1.53  tff(c_26, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_58, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 3.54/1.53  tff(c_106, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_58])).
% 3.54/1.53  tff(c_186, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_106])).
% 3.54/1.53  tff(c_46, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_38, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_34, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_52, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.54/1.53  tff(c_187, plain, (![C_98, A_99, B_100]: (m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(B_100))) | ~m1_pre_topc(B_100, A_99) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.53  tff(c_227, plain, (![B_106, A_107, A_108]: (m1_subset_1(u1_struct_0(B_106), k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_pre_topc(A_108, A_107) | ~l1_pre_topc(A_107) | ~m1_pre_topc(B_106, A_108) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_12, c_187])).
% 3.54/1.53  tff(c_233, plain, (![B_106]: (m1_subset_1(u1_struct_0(B_106), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(B_106, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_227])).
% 3.54/1.53  tff(c_242, plain, (![B_106]: (m1_subset_1(u1_struct_0(B_106), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(B_106, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_50, c_233])).
% 3.54/1.53  tff(c_360, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_287, c_242])).
% 3.54/1.53  tff(c_389, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_360])).
% 3.54/1.53  tff(c_424, plain, (![A_116, B_117, C_118, E_119]: (k8_relset_1(u1_struct_0(A_116), u1_struct_0(B_117), C_118, E_119)=k2_pre_topc(A_116, E_119) | ~m1_subset_1(E_119, k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(E_119, k1_zfmisc_1(u1_struct_0(B_117))) | ~v3_borsuk_1(C_118, A_116, B_117) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116), u1_struct_0(B_117)))) | ~v5_pre_topc(C_118, A_116, B_117) | ~v1_funct_2(C_118, u1_struct_0(A_116), u1_struct_0(B_117)) | ~v1_funct_1(C_118) | ~m1_pre_topc(B_117, A_116) | ~v4_tex_2(B_117, A_116) | v2_struct_0(B_117) | ~l1_pre_topc(A_116) | ~v3_tdlat_3(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.54/1.53  tff(c_426, plain, (![B_117, C_118]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_117), C_118, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_117))) | ~v3_borsuk_1(C_118, '#skF_1', B_117) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_117)))) | ~v5_pre_topc(C_118, '#skF_1', B_117) | ~v1_funct_2(C_118, u1_struct_0('#skF_1'), u1_struct_0(B_117)) | ~v1_funct_1(C_118) | ~m1_pre_topc(B_117, '#skF_1') | ~v4_tex_2(B_117, '#skF_1') | v2_struct_0(B_117) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_389, c_424])).
% 3.54/1.53  tff(c_443, plain, (![B_117, C_118]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_117), C_118, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_117))) | ~v3_borsuk_1(C_118, '#skF_1', B_117) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_117)))) | ~v5_pre_topc(C_118, '#skF_1', B_117) | ~v1_funct_2(C_118, u1_struct_0('#skF_1'), u1_struct_0(B_117)) | ~v1_funct_1(C_118) | ~m1_pre_topc(B_117, '#skF_1') | ~v4_tex_2(B_117, '#skF_1') | v2_struct_0(B_117) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_426])).
% 3.54/1.53  tff(c_467, plain, (![B_122, C_123]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_122), C_123, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_122))) | ~v3_borsuk_1(C_123, '#skF_1', B_122) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_122)))) | ~v5_pre_topc(C_123, '#skF_1', B_122) | ~v1_funct_2(C_123, u1_struct_0('#skF_1'), u1_struct_0(B_122)) | ~v1_funct_1(C_123) | ~m1_pre_topc(B_122, '#skF_1') | ~v4_tex_2(B_122, '#skF_1') | v2_struct_0(B_122))), inference(negUnitSimplification, [status(thm)], [c_56, c_443])).
% 3.54/1.53  tff(c_476, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_467])).
% 3.54/1.53  tff(c_484, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_34, c_476])).
% 3.54/1.53  tff(c_485, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_186, c_484])).
% 3.54/1.53  tff(c_747, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_744, c_485])).
% 3.54/1.53  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_169, c_747])).
% 3.54/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.53  
% 3.54/1.53  Inference rules
% 3.54/1.53  ----------------------
% 3.54/1.53  #Ref     : 0
% 3.54/1.53  #Sup     : 146
% 3.54/1.53  #Fact    : 0
% 3.54/1.53  #Define  : 0
% 3.54/1.53  #Split   : 7
% 3.54/1.53  #Chain   : 0
% 3.54/1.53  #Close   : 0
% 3.54/1.53  
% 3.54/1.53  Ordering : KBO
% 3.54/1.53  
% 3.54/1.53  Simplification rules
% 3.54/1.53  ----------------------
% 3.54/1.53  #Subsume      : 5
% 3.54/1.53  #Demod        : 162
% 3.54/1.53  #Tautology    : 17
% 3.54/1.53  #SimpNegUnit  : 53
% 3.54/1.53  #BackRed      : 1
% 3.54/1.53  
% 3.54/1.53  #Partial instantiations: 0
% 3.54/1.53  #Strategies tried      : 1
% 3.54/1.53  
% 3.54/1.53  Timing (in seconds)
% 3.54/1.53  ----------------------
% 3.54/1.54  Preprocessing        : 0.36
% 3.54/1.54  Parsing              : 0.19
% 3.54/1.54  CNF conversion       : 0.03
% 3.54/1.54  Main loop            : 0.42
% 3.54/1.54  Inferencing          : 0.13
% 3.54/1.54  Reduction            : 0.15
% 3.54/1.54  Demodulation         : 0.10
% 3.54/1.54  BG Simplification    : 0.02
% 3.54/1.54  Subsumption          : 0.08
% 3.54/1.54  Abstraction          : 0.02
% 3.54/1.54  MUC search           : 0.00
% 3.54/1.54  Cooper               : 0.00
% 3.54/1.54  Total                : 0.82
% 3.54/1.54  Index Insertion      : 0.00
% 3.54/1.54  Index Deletion       : 0.00
% 3.54/1.54  Index Matching       : 0.00
% 3.54/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:42 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 773 expanded)
%              Number of leaves         :   40 ( 287 expanded)
%              Depth                    :   15
%              Number of atoms          :  300 (4268 expanded)
%              Number of equality atoms :   46 ( 537 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_181,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_90,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_142,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_28,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_57,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_72,plain,(
    ! [A_88,B_89] :
      ( k6_domain_1(A_88,B_89) = k1_tarski(B_89)
      | ~ m1_subset_1(B_89,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_57,c_72])).

tff(c_111,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

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

tff(c_44,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

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
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_83,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_85,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_83])).

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

tff(c_26,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_58,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_106,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_58])).

tff(c_234,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_106])).

tff(c_146,plain,(
    ! [A_94,B_95] :
      ( ~ v2_struct_0(k1_tex_2(A_94,B_95))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l1_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

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

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_131,plain,(
    ! [A_92,B_93] :
      ( v1_pre_topc(k1_tex_2(A_92,B_93))
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l1_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

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

tff(c_174,plain,(
    ! [A_100,B_101] :
      ( m1_pre_topc(k1_tex_2(A_100,B_101),A_100)
      | ~ m1_subset_1(B_101,u1_struct_0(A_100))
      | ~ l1_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_176,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_174])).

tff(c_181,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_176])).

tff(c_182,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_181])).

tff(c_12,plain,(
    ! [C_17,A_11,B_15] :
      ( m1_pre_topc(C_17,A_11)
      | ~ m1_pre_topc(C_17,B_15)
      | ~ m1_pre_topc(B_15,A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_192,plain,(
    ! [A_11] :
      ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),A_11)
      | ~ m1_pre_topc('#skF_2',A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_182,c_12])).

tff(c_205,plain,(
    ! [A_102,B_103,C_104] :
      ( k1_tex_2(A_102,B_103) = C_104
      | u1_struct_0(C_104) != k6_domain_1(u1_struct_0(A_102),B_103)
      | ~ m1_pre_topc(C_104,A_102)
      | ~ v1_pre_topc(C_104)
      | v2_struct_0(C_104)
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_207,plain,(
    ! [C_104] :
      ( k1_tex_2('#skF_1','#skF_4') = C_104
      | u1_struct_0(C_104) != k1_tarski('#skF_4')
      | ~ m1_pre_topc(C_104,'#skF_1')
      | ~ v1_pre_topc(C_104)
      | v2_struct_0(C_104)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_205])).

tff(c_211,plain,(
    ! [C_104] :
      ( k1_tex_2('#skF_1','#skF_4') = C_104
      | u1_struct_0(C_104) != k1_tarski('#skF_4')
      | ~ m1_pre_topc(C_104,'#skF_1')
      | ~ v1_pre_topc(C_104)
      | v2_struct_0(C_104)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_57,c_207])).

tff(c_235,plain,(
    ! [C_107] :
      ( k1_tex_2('#skF_1','#skF_4') = C_107
      | u1_struct_0(C_107) != k1_tarski('#skF_4')
      | ~ m1_pre_topc(C_107,'#skF_1')
      | ~ v1_pre_topc(C_107)
      | v2_struct_0(C_107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_211])).

tff(c_243,plain,
    ( k1_tex_2('#skF_2','#skF_4') = k1_tex_2('#skF_1','#skF_4')
    | u1_struct_0(k1_tex_2('#skF_2','#skF_4')) != k1_tarski('#skF_4')
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_192,c_235])).

tff(c_261,plain,
    ( k1_tex_2('#skF_2','#skF_4') = k1_tex_2('#skF_1','#skF_4')
    | u1_struct_0(k1_tex_2('#skF_2','#skF_4')) != k1_tarski('#skF_4')
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_44,c_141,c_243])).

tff(c_262,plain,
    ( k1_tex_2('#skF_2','#skF_4') = k1_tex_2('#skF_1','#skF_4')
    | u1_struct_0(k1_tex_2('#skF_2','#skF_4')) != k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_261])).

tff(c_276,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_4')) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_277,plain,(
    ! [A_108,B_109] :
      ( k6_domain_1(u1_struct_0(A_108),B_109) = u1_struct_0(k1_tex_2(A_108,B_109))
      | ~ m1_pre_topc(k1_tex_2(A_108,B_109),A_108)
      | ~ v1_pre_topc(k1_tex_2(A_108,B_109))
      | v2_struct_0(k1_tex_2(A_108,B_109))
      | ~ m1_subset_1(B_109,u1_struct_0(A_108))
      | ~ l1_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_287,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_182,c_277])).

tff(c_302,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4')
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_32,c_141,c_99,c_287])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_156,c_276,c_302])).

tff(c_305,plain,(
    k1_tex_2('#skF_2','#skF_4') = k1_tex_2('#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_309,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_182])).

tff(c_178,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_57,c_174])).

tff(c_185,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_178])).

tff(c_186,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_185])).

tff(c_306,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_327,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_306])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_46,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_38,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_34,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( m1_subset_1(u1_struct_0(B_10),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_494,plain,(
    ! [A_120,B_121,C_122,E_123] :
      ( k8_relset_1(u1_struct_0(A_120),u1_struct_0(B_121),C_122,E_123) = k2_pre_topc(A_120,E_123)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(E_123,k1_zfmisc_1(u1_struct_0(B_121)))
      | ~ v3_borsuk_1(C_122,A_120,B_121)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120),u1_struct_0(B_121))))
      | ~ v5_pre_topc(C_122,A_120,B_121)
      | ~ v1_funct_2(C_122,u1_struct_0(A_120),u1_struct_0(B_121))
      | ~ v1_funct_1(C_122)
      | ~ m1_pre_topc(B_121,A_120)
      | ~ v4_tex_2(B_121,A_120)
      | v2_struct_0(B_121)
      | ~ l1_pre_topc(A_120)
      | ~ v3_tdlat_3(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_574,plain,(
    ! [A_128,B_129,C_130,B_131] :
      ( k8_relset_1(u1_struct_0(A_128),u1_struct_0(B_129),C_130,u1_struct_0(B_131)) = k2_pre_topc(A_128,u1_struct_0(B_131))
      | ~ m1_subset_1(u1_struct_0(B_131),k1_zfmisc_1(u1_struct_0(B_129)))
      | ~ v3_borsuk_1(C_130,A_128,B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_128),u1_struct_0(B_129))))
      | ~ v5_pre_topc(C_130,A_128,B_129)
      | ~ v1_funct_2(C_130,u1_struct_0(A_128),u1_struct_0(B_129))
      | ~ v1_funct_1(C_130)
      | ~ m1_pre_topc(B_129,A_128)
      | ~ v4_tex_2(B_129,A_128)
      | v2_struct_0(B_129)
      | ~ v3_tdlat_3(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128)
      | ~ m1_pre_topc(B_131,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_10,c_494])).

tff(c_677,plain,(
    ! [A_139,A_140,C_141,B_142] :
      ( k8_relset_1(u1_struct_0(A_139),u1_struct_0(A_140),C_141,u1_struct_0(B_142)) = k2_pre_topc(A_139,u1_struct_0(B_142))
      | ~ v3_borsuk_1(C_141,A_139,A_140)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_139),u1_struct_0(A_140))))
      | ~ v5_pre_topc(C_141,A_139,A_140)
      | ~ v1_funct_2(C_141,u1_struct_0(A_139),u1_struct_0(A_140))
      | ~ v1_funct_1(C_141)
      | ~ m1_pre_topc(A_140,A_139)
      | ~ v4_tex_2(A_140,A_139)
      | v2_struct_0(A_140)
      | ~ v3_tdlat_3(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139)
      | ~ m1_pre_topc(B_142,A_139)
      | ~ l1_pre_topc(A_139)
      | ~ m1_pre_topc(B_142,A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_10,c_574])).

tff(c_683,plain,(
    ! [B_142] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(B_142)) = k2_pre_topc('#skF_1',u1_struct_0(B_142))
      | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ v4_tex_2('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(B_142,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_142,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_677])).

tff(c_692,plain,(
    ! [B_142] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(B_142)) = k2_pre_topc('#skF_1',u1_struct_0(B_142))
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(B_142,'#skF_1')
      | ~ m1_pre_topc(B_142,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_50,c_54,c_52,c_46,c_44,c_42,c_40,c_38,c_34,c_683])).

tff(c_694,plain,(
    ! [B_143] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(B_143)) = k2_pre_topc('#skF_1',u1_struct_0(B_143))
      | ~ m1_pre_topc(B_143,'#skF_1')
      | ~ m1_pre_topc(B_143,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_48,c_692])).

tff(c_703,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',u1_struct_0(k1_tex_2('#skF_1','#skF_4')))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_694])).

tff(c_707,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_186,c_327,c_703])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:31:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.55  
% 3.35/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.55  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.35/1.55  
% 3.35/1.55  %Foreground sorts:
% 3.35/1.55  
% 3.35/1.55  
% 3.35/1.55  %Background operators:
% 3.35/1.55  
% 3.35/1.55  
% 3.35/1.55  %Foreground operators:
% 3.35/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.35/1.55  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.35/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.35/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.55  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.35/1.55  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.35/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.35/1.55  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.35/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.35/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.35/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.35/1.55  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.35/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.35/1.55  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.35/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.55  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.35/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.55  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.35/1.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.35/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.35/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.35/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.35/1.55  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.35/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.55  
% 3.35/1.57  tff(f_181, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.35/1.57  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.35/1.57  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.35/1.57  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.35/1.57  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.35/1.57  tff(f_104, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.35/1.57  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 3.35/1.57  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 3.35/1.57  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.35/1.57  tff(f_142, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.35/1.57  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.57  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_28, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_57, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 3.35/1.57  tff(c_72, plain, (![A_88, B_89]: (k6_domain_1(A_88, B_89)=k1_tarski(B_89) | ~m1_subset_1(B_89, A_88) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.35/1.57  tff(c_84, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_57, c_72])).
% 3.35/1.57  tff(c_111, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_84])).
% 3.35/1.57  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.35/1.57  tff(c_114, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_111, c_6])).
% 3.35/1.57  tff(c_117, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_114])).
% 3.35/1.57  tff(c_120, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_117])).
% 3.35/1.57  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_120])).
% 3.35/1.57  tff(c_125, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 3.35/1.57  tff(c_44, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_64, plain, (![B_85, A_86]: (l1_pre_topc(B_85) | ~m1_pre_topc(B_85, A_86) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.35/1.57  tff(c_67, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_64])).
% 3.35/1.57  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_67])).
% 3.35/1.57  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_83, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_72])).
% 3.35/1.57  tff(c_85, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_83])).
% 3.35/1.57  tff(c_88, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_85, c_6])).
% 3.35/1.57  tff(c_91, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_88])).
% 3.35/1.57  tff(c_94, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_91])).
% 3.35/1.57  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_94])).
% 3.35/1.57  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_83])).
% 3.35/1.57  tff(c_26, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_58, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 3.35/1.57  tff(c_106, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_58])).
% 3.35/1.57  tff(c_234, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_106])).
% 3.35/1.57  tff(c_146, plain, (![A_94, B_95]: (~v2_struct_0(k1_tex_2(A_94, B_95)) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l1_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.35/1.57  tff(c_149, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_146])).
% 3.35/1.57  tff(c_155, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_149])).
% 3.35/1.57  tff(c_156, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_155])).
% 3.35/1.57  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_131, plain, (![A_92, B_93]: (v1_pre_topc(k1_tex_2(A_92, B_93)) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l1_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.35/1.57  tff(c_134, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_131])).
% 3.35/1.57  tff(c_140, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_134])).
% 3.35/1.57  tff(c_141, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_140])).
% 3.35/1.57  tff(c_174, plain, (![A_100, B_101]: (m1_pre_topc(k1_tex_2(A_100, B_101), A_100) | ~m1_subset_1(B_101, u1_struct_0(A_100)) | ~l1_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.35/1.57  tff(c_176, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_174])).
% 3.35/1.57  tff(c_181, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_176])).
% 3.35/1.57  tff(c_182, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_181])).
% 3.35/1.57  tff(c_12, plain, (![C_17, A_11, B_15]: (m1_pre_topc(C_17, A_11) | ~m1_pre_topc(C_17, B_15) | ~m1_pre_topc(B_15, A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.35/1.57  tff(c_192, plain, (![A_11]: (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), A_11) | ~m1_pre_topc('#skF_2', A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(resolution, [status(thm)], [c_182, c_12])).
% 3.35/1.57  tff(c_205, plain, (![A_102, B_103, C_104]: (k1_tex_2(A_102, B_103)=C_104 | u1_struct_0(C_104)!=k6_domain_1(u1_struct_0(A_102), B_103) | ~m1_pre_topc(C_104, A_102) | ~v1_pre_topc(C_104) | v2_struct_0(C_104) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.35/1.57  tff(c_207, plain, (![C_104]: (k1_tex_2('#skF_1', '#skF_4')=C_104 | u1_struct_0(C_104)!=k1_tarski('#skF_4') | ~m1_pre_topc(C_104, '#skF_1') | ~v1_pre_topc(C_104) | v2_struct_0(C_104) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_205])).
% 3.35/1.57  tff(c_211, plain, (![C_104]: (k1_tex_2('#skF_1', '#skF_4')=C_104 | u1_struct_0(C_104)!=k1_tarski('#skF_4') | ~m1_pre_topc(C_104, '#skF_1') | ~v1_pre_topc(C_104) | v2_struct_0(C_104) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_57, c_207])).
% 3.35/1.57  tff(c_235, plain, (![C_107]: (k1_tex_2('#skF_1', '#skF_4')=C_107 | u1_struct_0(C_107)!=k1_tarski('#skF_4') | ~m1_pre_topc(C_107, '#skF_1') | ~v1_pre_topc(C_107) | v2_struct_0(C_107))), inference(negUnitSimplification, [status(thm)], [c_56, c_211])).
% 3.35/1.57  tff(c_243, plain, (k1_tex_2('#skF_2', '#skF_4')=k1_tex_2('#skF_1', '#skF_4') | u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))!=k1_tarski('#skF_4') | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_192, c_235])).
% 3.35/1.57  tff(c_261, plain, (k1_tex_2('#skF_2', '#skF_4')=k1_tex_2('#skF_1', '#skF_4') | u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))!=k1_tarski('#skF_4') | v2_struct_0(k1_tex_2('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_44, c_141, c_243])).
% 3.35/1.57  tff(c_262, plain, (k1_tex_2('#skF_2', '#skF_4')=k1_tex_2('#skF_1', '#skF_4') | u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))!=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_156, c_261])).
% 3.35/1.57  tff(c_276, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_262])).
% 3.35/1.57  tff(c_277, plain, (![A_108, B_109]: (k6_domain_1(u1_struct_0(A_108), B_109)=u1_struct_0(k1_tex_2(A_108, B_109)) | ~m1_pre_topc(k1_tex_2(A_108, B_109), A_108) | ~v1_pre_topc(k1_tex_2(A_108, B_109)) | v2_struct_0(k1_tex_2(A_108, B_109)) | ~m1_subset_1(B_109, u1_struct_0(A_108)) | ~l1_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.35/1.57  tff(c_287, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_182, c_277])).
% 3.35/1.57  tff(c_302, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4') | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_32, c_141, c_99, c_287])).
% 3.35/1.57  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_156, c_276, c_302])).
% 3.35/1.57  tff(c_305, plain, (k1_tex_2('#skF_2', '#skF_4')=k1_tex_2('#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_262])).
% 3.35/1.57  tff(c_309, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_182])).
% 3.35/1.57  tff(c_178, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_57, c_174])).
% 3.35/1.57  tff(c_185, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_178])).
% 3.35/1.57  tff(c_186, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_185])).
% 3.35/1.57  tff(c_306, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_262])).
% 3.35/1.57  tff(c_327, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_306])).
% 3.35/1.57  tff(c_52, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_46, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_38, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_34, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.35/1.57  tff(c_10, plain, (![B_10, A_8]: (m1_subset_1(u1_struct_0(B_10), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.35/1.57  tff(c_494, plain, (![A_120, B_121, C_122, E_123]: (k8_relset_1(u1_struct_0(A_120), u1_struct_0(B_121), C_122, E_123)=k2_pre_topc(A_120, E_123) | ~m1_subset_1(E_123, k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(E_123, k1_zfmisc_1(u1_struct_0(B_121))) | ~v3_borsuk_1(C_122, A_120, B_121) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120), u1_struct_0(B_121)))) | ~v5_pre_topc(C_122, A_120, B_121) | ~v1_funct_2(C_122, u1_struct_0(A_120), u1_struct_0(B_121)) | ~v1_funct_1(C_122) | ~m1_pre_topc(B_121, A_120) | ~v4_tex_2(B_121, A_120) | v2_struct_0(B_121) | ~l1_pre_topc(A_120) | ~v3_tdlat_3(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.35/1.57  tff(c_574, plain, (![A_128, B_129, C_130, B_131]: (k8_relset_1(u1_struct_0(A_128), u1_struct_0(B_129), C_130, u1_struct_0(B_131))=k2_pre_topc(A_128, u1_struct_0(B_131)) | ~m1_subset_1(u1_struct_0(B_131), k1_zfmisc_1(u1_struct_0(B_129))) | ~v3_borsuk_1(C_130, A_128, B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_128), u1_struct_0(B_129)))) | ~v5_pre_topc(C_130, A_128, B_129) | ~v1_funct_2(C_130, u1_struct_0(A_128), u1_struct_0(B_129)) | ~v1_funct_1(C_130) | ~m1_pre_topc(B_129, A_128) | ~v4_tex_2(B_129, A_128) | v2_struct_0(B_129) | ~v3_tdlat_3(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128) | ~m1_pre_topc(B_131, A_128) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_10, c_494])).
% 3.35/1.57  tff(c_677, plain, (![A_139, A_140, C_141, B_142]: (k8_relset_1(u1_struct_0(A_139), u1_struct_0(A_140), C_141, u1_struct_0(B_142))=k2_pre_topc(A_139, u1_struct_0(B_142)) | ~v3_borsuk_1(C_141, A_139, A_140) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_139), u1_struct_0(A_140)))) | ~v5_pre_topc(C_141, A_139, A_140) | ~v1_funct_2(C_141, u1_struct_0(A_139), u1_struct_0(A_140)) | ~v1_funct_1(C_141) | ~m1_pre_topc(A_140, A_139) | ~v4_tex_2(A_140, A_139) | v2_struct_0(A_140) | ~v3_tdlat_3(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139) | ~m1_pre_topc(B_142, A_139) | ~l1_pre_topc(A_139) | ~m1_pre_topc(B_142, A_140) | ~l1_pre_topc(A_140))), inference(resolution, [status(thm)], [c_10, c_574])).
% 3.35/1.57  tff(c_683, plain, (![B_142]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(B_142))=k2_pre_topc('#skF_1', u1_struct_0(B_142)) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc(B_142, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(B_142, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_677])).
% 3.35/1.57  tff(c_692, plain, (![B_142]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(B_142))=k2_pre_topc('#skF_1', u1_struct_0(B_142)) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~m1_pre_topc(B_142, '#skF_1') | ~m1_pre_topc(B_142, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_50, c_54, c_52, c_46, c_44, c_42, c_40, c_38, c_34, c_683])).
% 3.35/1.57  tff(c_694, plain, (![B_143]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(B_143))=k2_pre_topc('#skF_1', u1_struct_0(B_143)) | ~m1_pre_topc(B_143, '#skF_1') | ~m1_pre_topc(B_143, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_48, c_692])).
% 3.35/1.57  tff(c_703, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_327, c_694])).
% 3.35/1.57  tff(c_707, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_186, c_327, c_703])).
% 3.35/1.57  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_707])).
% 3.35/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.57  
% 3.35/1.57  Inference rules
% 3.35/1.57  ----------------------
% 3.35/1.58  #Ref     : 0
% 3.35/1.58  #Sup     : 117
% 3.35/1.58  #Fact    : 0
% 3.35/1.58  #Define  : 0
% 3.35/1.58  #Split   : 9
% 3.35/1.58  #Chain   : 0
% 3.35/1.58  #Close   : 0
% 3.35/1.58  
% 3.35/1.58  Ordering : KBO
% 3.35/1.58  
% 3.35/1.58  Simplification rules
% 3.35/1.58  ----------------------
% 3.35/1.58  #Subsume      : 29
% 3.35/1.58  #Demod        : 196
% 3.35/1.58  #Tautology    : 37
% 3.35/1.58  #SimpNegUnit  : 42
% 3.35/1.58  #BackRed      : 6
% 3.35/1.58  
% 3.35/1.58  #Partial instantiations: 0
% 3.35/1.58  #Strategies tried      : 1
% 3.35/1.58  
% 3.35/1.58  Timing (in seconds)
% 3.35/1.58  ----------------------
% 3.35/1.58  Preprocessing        : 0.38
% 3.35/1.58  Parsing              : 0.20
% 3.35/1.58  CNF conversion       : 0.03
% 3.35/1.58  Main loop            : 0.36
% 3.35/1.58  Inferencing          : 0.12
% 3.35/1.58  Reduction            : 0.13
% 3.35/1.58  Demodulation         : 0.09
% 3.35/1.58  BG Simplification    : 0.02
% 3.35/1.58  Subsumption          : 0.07
% 3.35/1.58  Abstraction          : 0.02
% 3.35/1.58  MUC search           : 0.00
% 3.35/1.58  Cooper               : 0.00
% 3.35/1.58  Total                : 0.79
% 3.35/1.58  Index Insertion      : 0.00
% 3.35/1.58  Index Deletion       : 0.00
% 3.35/1.58  Index Matching       : 0.00
% 3.35/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------

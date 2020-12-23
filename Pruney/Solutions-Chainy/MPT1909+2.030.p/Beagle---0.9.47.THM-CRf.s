%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:41 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 444 expanded)
%              Number of leaves         :   40 ( 177 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 (2424 expanded)
%              Number of equality atoms :   29 ( 296 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_171,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_80,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_132,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_44,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_73,plain,(
    ! [B_80,A_81] :
      ( l1_pre_topc(B_80)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_79,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_76])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_169,plain,(
    ! [A_91,B_92] :
      ( m1_pre_topc(k1_tex_2(A_91,B_92),A_91)
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_171,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_169])).

tff(c_176,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_171])).

tff(c_177,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_176])).

tff(c_139,plain,(
    ! [A_87,B_88] :
      ( ~ v2_struct_0(k1_tex_2(A_87,B_88))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_142,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_139])).

tff(c_148,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_142])).

tff(c_149,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_148])).

tff(c_154,plain,(
    ! [A_89,B_90] :
      ( v1_pre_topc(k1_tex_2(A_89,B_90))
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l1_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_157,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_154])).

tff(c_163,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_157])).

tff(c_164,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_163])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_83,B_84] :
      ( k6_domain_1(A_83,B_84) = k1_tarski(B_84)
      | ~ m1_subset_1(B_84,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_92,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_81])).

tff(c_94,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_97,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_8])).

tff(c_100,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_97])).

tff(c_103,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_100])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_103])).

tff(c_108,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_241,plain,(
    ! [A_100,B_101] :
      ( k6_domain_1(u1_struct_0(A_100),B_101) = u1_struct_0(k1_tex_2(A_100,B_101))
      | ~ m1_pre_topc(k1_tex_2(A_100,B_101),A_100)
      | ~ v1_pre_topc(k1_tex_2(A_100,B_101))
      | v2_struct_0(k1_tex_2(A_100,B_101))
      | ~ m1_subset_1(B_101,u1_struct_0(A_100))
      | ~ l1_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_245,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_241])).

tff(c_252,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4')
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_32,c_164,c_108,c_245])).

tff(c_253,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_149,c_252])).

tff(c_12,plain,(
    ! [B_11,A_9] :
      ( m1_subset_1(u1_struct_0(B_11),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_320,plain,(
    ! [A_9] :
      ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_12])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_28,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_57,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_93,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_57,c_81])).

tff(c_119,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_122,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_125,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_122])).

tff(c_128,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_128])).

tff(c_133,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_26,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_58,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_194,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_108,c_58])).

tff(c_173,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_57,c_169])).

tff(c_180,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_173])).

tff(c_181,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_180])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_46,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_38,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_34,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_145,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_57,c_139])).

tff(c_152,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_145])).

tff(c_153,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_152])).

tff(c_160,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_4'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_57,c_154])).

tff(c_167,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_160])).

tff(c_168,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_167])).

tff(c_243,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_181,c_241])).

tff(c_248,plain,
    ( u1_struct_0(k1_tex_2('#skF_1','#skF_4')) = k1_tarski('#skF_4')
    | v2_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_57,c_168,c_133,c_243])).

tff(c_249,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_4')) = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_153,c_248])).

tff(c_348,plain,(
    ! [A_102,B_103,C_104,E_105] :
      ( k8_relset_1(u1_struct_0(A_102),u1_struct_0(B_103),C_104,E_105) = k2_pre_topc(A_102,E_105)
      | ~ m1_subset_1(E_105,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_subset_1(E_105,k1_zfmisc_1(u1_struct_0(B_103)))
      | ~ v3_borsuk_1(C_104,A_102,B_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),u1_struct_0(B_103))))
      | ~ v5_pre_topc(C_104,A_102,B_103)
      | ~ v1_funct_2(C_104,u1_struct_0(A_102),u1_struct_0(B_103))
      | ~ v1_funct_1(C_104)
      | ~ m1_pre_topc(B_103,A_102)
      | ~ v4_tex_2(B_103,A_102)
      | v2_struct_0(B_103)
      | ~ l1_pre_topc(A_102)
      | ~ v3_tdlat_3(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_376,plain,(
    ! [A_110,B_111,C_112,B_113] :
      ( k8_relset_1(u1_struct_0(A_110),u1_struct_0(B_111),C_112,u1_struct_0(B_113)) = k2_pre_topc(A_110,u1_struct_0(B_113))
      | ~ m1_subset_1(u1_struct_0(B_113),k1_zfmisc_1(u1_struct_0(B_111)))
      | ~ v3_borsuk_1(C_112,A_110,B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_111))))
      | ~ v5_pre_topc(C_112,A_110,B_111)
      | ~ v1_funct_2(C_112,u1_struct_0(A_110),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ m1_pre_topc(B_111,A_110)
      | ~ v4_tex_2(B_111,A_110)
      | v2_struct_0(B_111)
      | ~ v3_tdlat_3(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110)
      | ~ m1_pre_topc(B_113,A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_12,c_348])).

tff(c_382,plain,(
    ! [A_110,B_111,C_112] :
      ( k8_relset_1(u1_struct_0(A_110),u1_struct_0(B_111),C_112,u1_struct_0(k1_tex_2('#skF_1','#skF_4'))) = k2_pre_topc(A_110,u1_struct_0(k1_tex_2('#skF_1','#skF_4')))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_111)))
      | ~ v3_borsuk_1(C_112,A_110,B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_111))))
      | ~ v5_pre_topc(C_112,A_110,B_111)
      | ~ v1_funct_2(C_112,u1_struct_0(A_110),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ m1_pre_topc(B_111,A_110)
      | ~ v4_tex_2(B_111,A_110)
      | v2_struct_0(B_111)
      | ~ v3_tdlat_3(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110)
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_376])).

tff(c_671,plain,(
    ! [A_137,B_138,C_139] :
      ( k8_relset_1(u1_struct_0(A_137),u1_struct_0(B_138),C_139,k1_tarski('#skF_4')) = k2_pre_topc(A_137,k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_138)))
      | ~ v3_borsuk_1(C_139,A_137,B_138)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_137),u1_struct_0(B_138))))
      | ~ v5_pre_topc(C_139,A_137,B_138)
      | ~ v1_funct_2(C_139,u1_struct_0(A_137),u1_struct_0(B_138))
      | ~ v1_funct_1(C_139)
      | ~ m1_pre_topc(B_138,A_137)
      | ~ v4_tex_2(B_138,A_137)
      | v2_struct_0(B_138)
      | ~ v3_tdlat_3(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137)
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_249,c_382])).

tff(c_692,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
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
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_671])).

tff(c_705,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_181,c_54,c_52,c_46,c_44,c_42,c_40,c_38,c_34,c_692])).

tff(c_706,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_48,c_194,c_705])).

tff(c_712,plain,
    ( ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_320,c_706])).

tff(c_719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_177,c_712])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n018.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:26:57 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.50  
% 3.43/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.51  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.43/1.51  
% 3.43/1.51  %Foreground sorts:
% 3.43/1.51  
% 3.43/1.51  
% 3.43/1.51  %Background operators:
% 3.43/1.51  
% 3.43/1.51  
% 3.43/1.51  %Foreground operators:
% 3.43/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.43/1.51  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.43/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.43/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.43/1.51  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.43/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.43/1.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.43/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.43/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.51  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.43/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.43/1.51  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.43/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.51  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.43/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.51  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.43/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.43/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.43/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.43/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.43/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.51  
% 3.43/1.52  tff(f_171, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 3.43/1.52  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.43/1.52  tff(f_94, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.43/1.52  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.43/1.52  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.43/1.52  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.43/1.52  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 3.43/1.52  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.43/1.52  tff(f_132, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 3.43/1.52  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_44, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_73, plain, (![B_80, A_81]: (l1_pre_topc(B_80) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.43/1.52  tff(c_76, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_73])).
% 3.43/1.52  tff(c_79, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_76])).
% 3.43/1.52  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_169, plain, (![A_91, B_92]: (m1_pre_topc(k1_tex_2(A_91, B_92), A_91) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.43/1.52  tff(c_171, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_169])).
% 3.43/1.52  tff(c_176, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_171])).
% 3.43/1.52  tff(c_177, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_176])).
% 3.43/1.52  tff(c_139, plain, (![A_87, B_88]: (~v2_struct_0(k1_tex_2(A_87, B_88)) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.43/1.52  tff(c_142, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_139])).
% 3.43/1.52  tff(c_148, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_142])).
% 3.43/1.52  tff(c_149, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_148])).
% 3.43/1.52  tff(c_154, plain, (![A_89, B_90]: (v1_pre_topc(k1_tex_2(A_89, B_90)) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l1_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.43/1.52  tff(c_157, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_154])).
% 3.43/1.52  tff(c_163, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_157])).
% 3.43/1.52  tff(c_164, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_163])).
% 3.43/1.52  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.52  tff(c_81, plain, (![A_83, B_84]: (k6_domain_1(A_83, B_84)=k1_tarski(B_84) | ~m1_subset_1(B_84, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.43/1.52  tff(c_92, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_81])).
% 3.43/1.52  tff(c_94, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_92])).
% 3.43/1.52  tff(c_8, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.43/1.52  tff(c_97, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_94, c_8])).
% 3.43/1.52  tff(c_100, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_97])).
% 3.43/1.52  tff(c_103, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_100])).
% 3.43/1.52  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_103])).
% 3.43/1.52  tff(c_108, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_92])).
% 3.43/1.52  tff(c_241, plain, (![A_100, B_101]: (k6_domain_1(u1_struct_0(A_100), B_101)=u1_struct_0(k1_tex_2(A_100, B_101)) | ~m1_pre_topc(k1_tex_2(A_100, B_101), A_100) | ~v1_pre_topc(k1_tex_2(A_100, B_101)) | v2_struct_0(k1_tex_2(A_100, B_101)) | ~m1_subset_1(B_101, u1_struct_0(A_100)) | ~l1_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.43/1.52  tff(c_245, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_177, c_241])).
% 3.43/1.52  tff(c_252, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4') | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_32, c_164, c_108, c_245])).
% 3.43/1.52  tff(c_253, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_149, c_252])).
% 3.43/1.52  tff(c_12, plain, (![B_11, A_9]: (m1_subset_1(u1_struct_0(B_11), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.43/1.52  tff(c_320, plain, (![A_9]: (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), A_9) | ~l1_pre_topc(A_9))), inference(superposition, [status(thm), theory('equality')], [c_253, c_12])).
% 3.43/1.52  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_28, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_57, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 3.43/1.52  tff(c_93, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_57, c_81])).
% 3.43/1.52  tff(c_119, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_93])).
% 3.43/1.52  tff(c_122, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_119, c_8])).
% 3.43/1.52  tff(c_125, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_122])).
% 3.43/1.52  tff(c_128, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_125])).
% 3.43/1.52  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_128])).
% 3.43/1.52  tff(c_133, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_93])).
% 3.43/1.52  tff(c_26, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_58, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 3.43/1.52  tff(c_194, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_108, c_58])).
% 3.43/1.52  tff(c_173, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_57, c_169])).
% 3.43/1.52  tff(c_180, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_173])).
% 3.43/1.52  tff(c_181, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_180])).
% 3.43/1.52  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_52, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_46, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_38, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_34, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.43/1.52  tff(c_145, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_4')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_57, c_139])).
% 3.43/1.52  tff(c_152, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_145])).
% 3.43/1.52  tff(c_153, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_152])).
% 3.43/1.52  tff(c_160, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_4')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_57, c_154])).
% 3.43/1.52  tff(c_167, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_160])).
% 3.43/1.52  tff(c_168, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_167])).
% 3.43/1.52  tff(c_243, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_1', '#skF_4')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_181, c_241])).
% 3.43/1.52  tff(c_248, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))=k1_tarski('#skF_4') | v2_struct_0(k1_tex_2('#skF_1', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_57, c_168, c_133, c_243])).
% 3.43/1.52  tff(c_249, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_153, c_248])).
% 3.43/1.52  tff(c_348, plain, (![A_102, B_103, C_104, E_105]: (k8_relset_1(u1_struct_0(A_102), u1_struct_0(B_103), C_104, E_105)=k2_pre_topc(A_102, E_105) | ~m1_subset_1(E_105, k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_subset_1(E_105, k1_zfmisc_1(u1_struct_0(B_103))) | ~v3_borsuk_1(C_104, A_102, B_103) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102), u1_struct_0(B_103)))) | ~v5_pre_topc(C_104, A_102, B_103) | ~v1_funct_2(C_104, u1_struct_0(A_102), u1_struct_0(B_103)) | ~v1_funct_1(C_104) | ~m1_pre_topc(B_103, A_102) | ~v4_tex_2(B_103, A_102) | v2_struct_0(B_103) | ~l1_pre_topc(A_102) | ~v3_tdlat_3(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.43/1.52  tff(c_376, plain, (![A_110, B_111, C_112, B_113]: (k8_relset_1(u1_struct_0(A_110), u1_struct_0(B_111), C_112, u1_struct_0(B_113))=k2_pre_topc(A_110, u1_struct_0(B_113)) | ~m1_subset_1(u1_struct_0(B_113), k1_zfmisc_1(u1_struct_0(B_111))) | ~v3_borsuk_1(C_112, A_110, B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_111)))) | ~v5_pre_topc(C_112, A_110, B_111) | ~v1_funct_2(C_112, u1_struct_0(A_110), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~m1_pre_topc(B_111, A_110) | ~v4_tex_2(B_111, A_110) | v2_struct_0(B_111) | ~v3_tdlat_3(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110) | ~m1_pre_topc(B_113, A_110) | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_12, c_348])).
% 3.43/1.52  tff(c_382, plain, (![A_110, B_111, C_112]: (k8_relset_1(u1_struct_0(A_110), u1_struct_0(B_111), C_112, u1_struct_0(k1_tex_2('#skF_1', '#skF_4')))=k2_pre_topc(A_110, u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_111))) | ~v3_borsuk_1(C_112, A_110, B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_111)))) | ~v5_pre_topc(C_112, A_110, B_111) | ~v1_funct_2(C_112, u1_struct_0(A_110), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~m1_pre_topc(B_111, A_110) | ~v4_tex_2(B_111, A_110) | v2_struct_0(B_111) | ~v3_tdlat_3(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), A_110) | ~l1_pre_topc(A_110))), inference(superposition, [status(thm), theory('equality')], [c_249, c_376])).
% 3.43/1.52  tff(c_671, plain, (![A_137, B_138, C_139]: (k8_relset_1(u1_struct_0(A_137), u1_struct_0(B_138), C_139, k1_tarski('#skF_4'))=k2_pre_topc(A_137, k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_138))) | ~v3_borsuk_1(C_139, A_137, B_138) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_137), u1_struct_0(B_138)))) | ~v5_pre_topc(C_139, A_137, B_138) | ~v1_funct_2(C_139, u1_struct_0(A_137), u1_struct_0(B_138)) | ~v1_funct_1(C_139) | ~m1_pre_topc(B_138, A_137) | ~v4_tex_2(B_138, A_137) | v2_struct_0(B_138) | ~v3_tdlat_3(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), A_137) | ~l1_pre_topc(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_249, c_382])).
% 3.43/1.52  tff(c_692, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_671])).
% 3.43/1.52  tff(c_705, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_181, c_54, c_52, c_46, c_44, c_42, c_40, c_38, c_34, c_692])).
% 3.43/1.52  tff(c_706, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_48, c_194, c_705])).
% 3.43/1.52  tff(c_712, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_320, c_706])).
% 3.43/1.52  tff(c_719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_177, c_712])).
% 3.43/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.52  
% 3.43/1.52  Inference rules
% 3.43/1.52  ----------------------
% 3.43/1.52  #Ref     : 0
% 3.43/1.52  #Sup     : 140
% 3.43/1.52  #Fact    : 0
% 3.43/1.52  #Define  : 0
% 3.43/1.52  #Split   : 10
% 3.43/1.52  #Chain   : 0
% 3.43/1.52  #Close   : 0
% 3.43/1.52  
% 3.43/1.52  Ordering : KBO
% 3.43/1.52  
% 3.43/1.52  Simplification rules
% 3.43/1.52  ----------------------
% 3.43/1.52  #Subsume      : 16
% 3.43/1.52  #Demod        : 145
% 3.43/1.52  #Tautology    : 30
% 3.43/1.52  #SimpNegUnit  : 43
% 3.43/1.52  #BackRed      : 0
% 3.43/1.52  
% 3.43/1.52  #Partial instantiations: 0
% 3.43/1.52  #Strategies tried      : 1
% 3.43/1.52  
% 3.43/1.52  Timing (in seconds)
% 3.43/1.52  ----------------------
% 3.43/1.53  Preprocessing        : 0.35
% 3.43/1.53  Parsing              : 0.18
% 3.43/1.53  CNF conversion       : 0.03
% 3.43/1.53  Main loop            : 0.41
% 3.43/1.53  Inferencing          : 0.13
% 3.43/1.53  Reduction            : 0.14
% 3.43/1.53  Demodulation         : 0.10
% 3.43/1.53  BG Simplification    : 0.02
% 3.43/1.53  Subsumption          : 0.09
% 3.43/1.53  Abstraction          : 0.02
% 3.43/1.53  MUC search           : 0.00
% 3.43/1.53  Cooper               : 0.00
% 3.43/1.53  Total                : 0.80
% 3.43/1.53  Index Insertion      : 0.00
% 3.43/1.53  Index Deletion       : 0.00
% 3.43/1.53  Index Matching       : 0.00
% 3.43/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

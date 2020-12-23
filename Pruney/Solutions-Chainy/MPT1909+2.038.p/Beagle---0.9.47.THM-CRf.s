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
% DateTime   : Thu Dec  3 10:30:43 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 190 expanded)
%              Number of leaves         :   35 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  190 ( 900 expanded)
%              Number of equality atoms :   22 ( 133 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_135,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_96,axiom,(
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

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_55])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_60,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_109,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_113,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_109,c_6])).

tff(c_116,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_113])).

tff(c_119,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_119])).

tff(c_124,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_16,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_18,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_45,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_71,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_45,c_60])).

tff(c_73,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_76,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_6])).

tff(c_79,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_76])).

tff(c_82,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_82])).

tff(c_87,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_14,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14])).

tff(c_94,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_46])).

tff(c_160,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_94])).

tff(c_34,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_28,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_26,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_22,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_125,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k6_domain_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_129,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_8])).

tff(c_133,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_129])).

tff(c_134,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_133])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_88,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_140,plain,(
    ! [A_75,B_76,C_77,E_78] :
      ( k8_relset_1(u1_struct_0(A_75),u1_struct_0(B_76),C_77,E_78) = k2_pre_topc(A_75,E_78)
      | ~ m1_subset_1(E_78,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(E_78,k1_zfmisc_1(u1_struct_0(B_76)))
      | ~ v3_borsuk_1(C_77,A_75,B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_75),u1_struct_0(B_76))))
      | ~ v5_pre_topc(C_77,A_75,B_76)
      | ~ v1_funct_2(C_77,u1_struct_0(A_75),u1_struct_0(B_76))
      | ~ v1_funct_1(C_77)
      | ~ m1_pre_topc(B_76,A_75)
      | ~ v4_tex_2(B_76,A_75)
      | v2_struct_0(B_76)
      | ~ l1_pre_topc(A_75)
      | ~ v3_tdlat_3(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_211,plain,(
    ! [A_83,B_84,C_85,B_86] :
      ( k8_relset_1(u1_struct_0(A_83),u1_struct_0(B_84),C_85,k6_domain_1(u1_struct_0(A_83),B_86)) = k2_pre_topc(A_83,k6_domain_1(u1_struct_0(A_83),B_86))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_83),B_86),k1_zfmisc_1(u1_struct_0(B_84)))
      | ~ v3_borsuk_1(C_85,A_83,B_84)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83),u1_struct_0(B_84))))
      | ~ v5_pre_topc(C_85,A_83,B_84)
      | ~ v1_funct_2(C_85,u1_struct_0(A_83),u1_struct_0(B_84))
      | ~ v1_funct_1(C_85)
      | ~ m1_pre_topc(B_84,A_83)
      | ~ v4_tex_2(B_84,A_83)
      | v2_struct_0(B_84)
      | ~ l1_pre_topc(A_83)
      | ~ v3_tdlat_3(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83)
      | ~ m1_subset_1(B_86,u1_struct_0(A_83))
      | v1_xboole_0(u1_struct_0(A_83)) ) ),
    inference(resolution,[status(thm)],[c_8,c_140])).

tff(c_215,plain,(
    ! [B_84,C_85] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_84),C_85,k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) = k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_84)))
      | ~ v3_borsuk_1(C_85,'#skF_1',B_84)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_84))))
      | ~ v5_pre_topc(C_85,'#skF_1',B_84)
      | ~ v1_funct_2(C_85,u1_struct_0('#skF_1'),u1_struct_0(B_84))
      | ~ v1_funct_1(C_85)
      | ~ m1_pre_topc(B_84,'#skF_1')
      | ~ v4_tex_2(B_84,'#skF_1')
      | v2_struct_0(B_84)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_211])).

tff(c_223,plain,(
    ! [B_84,C_85] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_84),C_85,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_84)))
      | ~ v3_borsuk_1(C_85,'#skF_1',B_84)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_84))))
      | ~ v5_pre_topc(C_85,'#skF_1',B_84)
      | ~ v1_funct_2(C_85,u1_struct_0('#skF_1'),u1_struct_0(B_84))
      | ~ v1_funct_1(C_85)
      | ~ m1_pre_topc(B_84,'#skF_1')
      | ~ v4_tex_2(B_84,'#skF_1')
      | v2_struct_0(B_84)
      | v2_struct_0('#skF_1')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_42,c_40,c_38,c_87,c_87,c_215])).

tff(c_316,plain,(
    ! [B_91,C_92] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_91),C_92,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_91)))
      | ~ v3_borsuk_1(C_92,'#skF_1',B_91)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_91))))
      | ~ v5_pre_topc(C_92,'#skF_1',B_91)
      | ~ v1_funct_2(C_92,u1_struct_0('#skF_1'),u1_struct_0(B_91))
      | ~ v1_funct_1(C_92)
      | ~ m1_pre_topc(B_91,'#skF_1')
      | ~ v4_tex_2(B_91,'#skF_1')
      | v2_struct_0(B_91) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_44,c_223])).

tff(c_323,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v4_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_316])).

tff(c_327,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_22,c_134,c_323])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_160,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:40:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.33  
% 2.71/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.33  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.33  
% 2.71/1.33  %Foreground sorts:
% 2.71/1.33  
% 2.71/1.33  
% 2.71/1.33  %Background operators:
% 2.71/1.33  
% 2.71/1.33  
% 2.71/1.33  %Foreground operators:
% 2.71/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.71/1.33  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.71/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.33  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.33  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.71/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.71/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.71/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.71/1.33  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.71/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.33  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.71/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.71/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.71/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.71/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.71/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.33  
% 2.71/1.35  tff(f_135, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 2.71/1.35  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.71/1.35  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.71/1.35  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.71/1.35  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.71/1.35  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.71/1.35  tff(f_96, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 2.71/1.35  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_52, plain, (![B_68, A_69]: (l1_pre_topc(B_68) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.71/1.35  tff(c_55, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_52])).
% 2.71/1.35  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_55])).
% 2.71/1.35  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.71/1.35  tff(c_20, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_60, plain, (![A_71, B_72]: (k6_domain_1(A_71, B_72)=k1_tarski(B_72) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.35  tff(c_72, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_60])).
% 2.71/1.35  tff(c_109, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_72])).
% 2.71/1.35  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.35  tff(c_113, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_109, c_6])).
% 2.71/1.35  tff(c_116, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_113])).
% 2.71/1.35  tff(c_119, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_116])).
% 2.71/1.35  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_119])).
% 2.71/1.35  tff(c_124, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 2.71/1.35  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_16, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_18, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_45, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.71/1.35  tff(c_71, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_45, c_60])).
% 2.71/1.35  tff(c_73, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_71])).
% 2.71/1.35  tff(c_76, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_73, c_6])).
% 2.71/1.35  tff(c_79, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_76])).
% 2.71/1.35  tff(c_82, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_79])).
% 2.71/1.35  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_82])).
% 2.71/1.35  tff(c_87, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_71])).
% 2.71/1.35  tff(c_14, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_46, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14])).
% 2.71/1.35  tff(c_94, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_46])).
% 2.71/1.35  tff(c_160, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_94])).
% 2.71/1.35  tff(c_34, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_28, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_26, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_22, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_125, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_72])).
% 2.71/1.35  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k6_domain_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.35  tff(c_129, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_8])).
% 2.71/1.35  tff(c_133, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_129])).
% 2.71/1.35  tff(c_134, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_125, c_133])).
% 2.71/1.35  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_88, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_71])).
% 2.71/1.35  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_40, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.71/1.35  tff(c_140, plain, (![A_75, B_76, C_77, E_78]: (k8_relset_1(u1_struct_0(A_75), u1_struct_0(B_76), C_77, E_78)=k2_pre_topc(A_75, E_78) | ~m1_subset_1(E_78, k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(E_78, k1_zfmisc_1(u1_struct_0(B_76))) | ~v3_borsuk_1(C_77, A_75, B_76) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_75), u1_struct_0(B_76)))) | ~v5_pre_topc(C_77, A_75, B_76) | ~v1_funct_2(C_77, u1_struct_0(A_75), u1_struct_0(B_76)) | ~v1_funct_1(C_77) | ~m1_pre_topc(B_76, A_75) | ~v4_tex_2(B_76, A_75) | v2_struct_0(B_76) | ~l1_pre_topc(A_75) | ~v3_tdlat_3(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.71/1.35  tff(c_211, plain, (![A_83, B_84, C_85, B_86]: (k8_relset_1(u1_struct_0(A_83), u1_struct_0(B_84), C_85, k6_domain_1(u1_struct_0(A_83), B_86))=k2_pre_topc(A_83, k6_domain_1(u1_struct_0(A_83), B_86)) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_83), B_86), k1_zfmisc_1(u1_struct_0(B_84))) | ~v3_borsuk_1(C_85, A_83, B_84) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83), u1_struct_0(B_84)))) | ~v5_pre_topc(C_85, A_83, B_84) | ~v1_funct_2(C_85, u1_struct_0(A_83), u1_struct_0(B_84)) | ~v1_funct_1(C_85) | ~m1_pre_topc(B_84, A_83) | ~v4_tex_2(B_84, A_83) | v2_struct_0(B_84) | ~l1_pre_topc(A_83) | ~v3_tdlat_3(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83) | ~m1_subset_1(B_86, u1_struct_0(A_83)) | v1_xboole_0(u1_struct_0(A_83)))), inference(resolution, [status(thm)], [c_8, c_140])).
% 2.71/1.35  tff(c_215, plain, (![B_84, C_85]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_84), C_85, k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_84))) | ~v3_borsuk_1(C_85, '#skF_1', B_84) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_84)))) | ~v5_pre_topc(C_85, '#skF_1', B_84) | ~v1_funct_2(C_85, u1_struct_0('#skF_1'), u1_struct_0(B_84)) | ~v1_funct_1(C_85) | ~m1_pre_topc(B_84, '#skF_1') | ~v4_tex_2(B_84, '#skF_1') | v2_struct_0(B_84) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_87, c_211])).
% 2.71/1.35  tff(c_223, plain, (![B_84, C_85]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_84), C_85, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_84))) | ~v3_borsuk_1(C_85, '#skF_1', B_84) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_84)))) | ~v5_pre_topc(C_85, '#skF_1', B_84) | ~v1_funct_2(C_85, u1_struct_0('#skF_1'), u1_struct_0(B_84)) | ~v1_funct_1(C_85) | ~m1_pre_topc(B_84, '#skF_1') | ~v4_tex_2(B_84, '#skF_1') | v2_struct_0(B_84) | v2_struct_0('#skF_1') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_42, c_40, c_38, c_87, c_87, c_215])).
% 2.71/1.35  tff(c_316, plain, (![B_91, C_92]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_91), C_92, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_91))) | ~v3_borsuk_1(C_92, '#skF_1', B_91) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_91)))) | ~v5_pre_topc(C_92, '#skF_1', B_91) | ~v1_funct_2(C_92, u1_struct_0('#skF_1'), u1_struct_0(B_91)) | ~v1_funct_1(C_92) | ~m1_pre_topc(B_91, '#skF_1') | ~v4_tex_2(B_91, '#skF_1') | v2_struct_0(B_91))), inference(negUnitSimplification, [status(thm)], [c_88, c_44, c_223])).
% 2.71/1.35  tff(c_323, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_316])).
% 2.71/1.35  tff(c_327, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_22, c_134, c_323])).
% 2.71/1.35  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_160, c_327])).
% 2.71/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.35  
% 2.71/1.35  Inference rules
% 2.71/1.35  ----------------------
% 2.71/1.35  #Ref     : 0
% 2.71/1.35  #Sup     : 62
% 2.71/1.35  #Fact    : 0
% 2.71/1.35  #Define  : 0
% 2.71/1.35  #Split   : 6
% 2.71/1.35  #Chain   : 0
% 2.71/1.35  #Close   : 0
% 2.71/1.35  
% 2.71/1.35  Ordering : KBO
% 2.71/1.35  
% 2.71/1.35  Simplification rules
% 2.71/1.35  ----------------------
% 2.71/1.35  #Subsume      : 1
% 2.71/1.35  #Demod        : 68
% 2.71/1.35  #Tautology    : 20
% 2.71/1.35  #SimpNegUnit  : 17
% 2.71/1.35  #BackRed      : 1
% 2.71/1.35  
% 2.71/1.35  #Partial instantiations: 0
% 2.71/1.35  #Strategies tried      : 1
% 2.71/1.35  
% 2.71/1.35  Timing (in seconds)
% 2.71/1.35  ----------------------
% 2.71/1.35  Preprocessing        : 0.31
% 2.71/1.35  Parsing              : 0.16
% 2.71/1.35  CNF conversion       : 0.03
% 2.71/1.35  Main loop            : 0.27
% 2.71/1.35  Inferencing          : 0.09
% 2.71/1.35  Reduction            : 0.09
% 2.71/1.35  Demodulation         : 0.07
% 2.71/1.35  BG Simplification    : 0.02
% 2.71/1.35  Subsumption          : 0.05
% 2.71/1.35  Abstraction          : 0.01
% 2.71/1.35  MUC search           : 0.00
% 2.71/1.35  Cooper               : 0.00
% 2.71/1.35  Total                : 0.62
% 2.71/1.35  Index Insertion      : 0.00
% 2.71/1.35  Index Deletion       : 0.00
% 2.71/1.35  Index Matching       : 0.00
% 2.71/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

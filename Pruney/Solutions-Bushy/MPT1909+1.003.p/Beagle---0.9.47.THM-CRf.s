%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1909+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:40 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.81s
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

tff(f_134,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_95,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_53,plain,(
    ! [B_69,A_70] :
      ( l1_pre_topc(B_69)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_59,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_60,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_72,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_109,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_109,c_8])).

tff(c_116,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_113])).

tff(c_119,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_119])).

tff(c_124,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_16,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_18,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

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
    inference(resolution,[status(thm)],[c_73,c_8])).

tff(c_79,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_76])).

tff(c_82,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_79])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_82])).

tff(c_87,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_14,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

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
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_26,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_22,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_125,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k6_domain_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_2])).

tff(c_133,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_129])).

tff(c_134,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_133])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_88,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

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
    inference(cnfTransformation,[status(thm)],[f_95])).

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
    inference(resolution,[status(thm)],[c_2,c_140])).

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

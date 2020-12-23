%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:43 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 223 expanded)
%              Number of leaves         :   38 (  99 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 (1144 expanded)
%              Number of equality atoms :   20 ( 153 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_140,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_101,axiom,(
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

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_20,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_75,plain,(
    ! [A_79,B_80] :
      ( k6_domain_1(A_79,B_80) = k1_tarski(B_80)
      | ~ m1_subset_1(B_80,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_90,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_49,c_75])).

tff(c_92,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_12,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_95,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_92,c_12])).

tff(c_98,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_95])).

tff(c_101,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_101])).

tff(c_107,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_66,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_69])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_91,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_112,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_115,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_112,c_12])).

tff(c_118,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_115])).

tff(c_121,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_121])).

tff(c_127,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_44,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_38,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_32,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_30,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_26,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [A_83,B_84,C_85,E_86] :
      ( k8_relset_1(u1_struct_0(A_83),u1_struct_0(B_84),C_85,E_86) = k2_pre_topc(A_83,E_86)
      | ~ m1_subset_1(E_86,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(E_86,k1_zfmisc_1(u1_struct_0(B_84)))
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
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_148,plain,(
    ! [A_87,B_88,C_89,A_90] :
      ( k8_relset_1(u1_struct_0(A_87),u1_struct_0(B_88),C_89,k1_tarski(A_90)) = k2_pre_topc(A_87,k1_tarski(A_90))
      | ~ m1_subset_1(k1_tarski(A_90),k1_zfmisc_1(u1_struct_0(B_88)))
      | ~ v3_borsuk_1(C_89,A_87,B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_87),u1_struct_0(B_88))))
      | ~ v5_pre_topc(C_89,A_87,B_88)
      | ~ v1_funct_2(C_89,u1_struct_0(A_87),u1_struct_0(B_88))
      | ~ v1_funct_1(C_89)
      | ~ m1_pre_topc(B_88,A_87)
      | ~ v4_tex_2(B_88,A_87)
      | v2_struct_0(B_88)
      | ~ l1_pre_topc(A_87)
      | ~ v3_tdlat_3(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87)
      | ~ r2_hidden(A_90,u1_struct_0(A_87)) ) ),
    inference(resolution,[status(thm)],[c_4,c_143])).

tff(c_153,plain,(
    ! [A_91,B_92,C_93,A_94] :
      ( k8_relset_1(u1_struct_0(A_91),u1_struct_0(B_92),C_93,k1_tarski(A_94)) = k2_pre_topc(A_91,k1_tarski(A_94))
      | ~ v3_borsuk_1(C_93,A_91,B_92)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_91),u1_struct_0(B_92))))
      | ~ v5_pre_topc(C_93,A_91,B_92)
      | ~ v1_funct_2(C_93,u1_struct_0(A_91),u1_struct_0(B_92))
      | ~ v1_funct_1(C_93)
      | ~ m1_pre_topc(B_92,A_91)
      | ~ v4_tex_2(B_92,A_91)
      | v2_struct_0(B_92)
      | ~ l1_pre_topc(A_91)
      | ~ v3_tdlat_3(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91)
      | ~ r2_hidden(A_94,u1_struct_0(A_91))
      | ~ r2_hidden(A_94,u1_struct_0(B_92)) ) ),
    inference(resolution,[status(thm)],[c_4,c_148])).

tff(c_158,plain,(
    ! [A_94] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(A_94)) = k2_pre_topc('#skF_1',k1_tarski(A_94))
      | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ v4_tex_2('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r2_hidden(A_94,u1_struct_0('#skF_1'))
      | ~ r2_hidden(A_94,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_28,c_153])).

tff(c_162,plain,(
    ! [A_94] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(A_94)) = k2_pre_topc('#skF_1',k1_tarski(A_94))
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ r2_hidden(A_94,u1_struct_0('#skF_1'))
      | ~ r2_hidden(A_94,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_38,c_36,c_34,c_32,c_30,c_26,c_158])).

tff(c_164,plain,(
    ! [A_95] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(A_95)) = k2_pre_topc('#skF_1',k1_tarski(A_95))
      | ~ r2_hidden(A_95,u1_struct_0('#skF_1'))
      | ~ r2_hidden(A_95,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_162])).

tff(c_126,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_106,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_18,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_50,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_141,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_106,c_50])).

tff(c_175,plain,
    ( ~ r2_hidden('#skF_4',u1_struct_0('#skF_1'))
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_141])).

tff(c_177,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_180,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_177])).

tff(c_183,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_180])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_183])).

tff(c_186,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_190,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_186])).

tff(c_193,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_190])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.36  
% 2.37/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.36  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.36  
% 2.37/1.36  %Foreground sorts:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Background operators:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Foreground operators:
% 2.37/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.37/1.36  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.37/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.36  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.37/1.36  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.37/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.36  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.37/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.37/1.36  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.36  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.37/1.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.37/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.37/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.37/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.36  
% 2.37/1.38  tff(f_140, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 2.37/1.38  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.37/1.38  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.37/1.38  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.37/1.38  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.37/1.38  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.37/1.38  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.37/1.38  tff(f_101, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 2.37/1.38  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.37/1.38  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_20, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_22, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_49, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.37/1.38  tff(c_75, plain, (![A_79, B_80]: (k6_domain_1(A_79, B_80)=k1_tarski(B_80) | ~m1_subset_1(B_80, A_79) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.37/1.38  tff(c_90, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_49, c_75])).
% 2.37/1.38  tff(c_92, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_90])).
% 2.37/1.38  tff(c_12, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.37/1.38  tff(c_95, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_92, c_12])).
% 2.37/1.38  tff(c_98, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_95])).
% 2.37/1.38  tff(c_101, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_98])).
% 2.37/1.38  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_101])).
% 2.37/1.38  tff(c_107, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_90])).
% 2.37/1.38  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.37/1.38  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_66, plain, (![B_73, A_74]: (l1_pre_topc(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.37/1.38  tff(c_69, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_66])).
% 2.37/1.38  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_69])).
% 2.37/1.38  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_91, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_75])).
% 2.37/1.38  tff(c_112, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_91])).
% 2.37/1.38  tff(c_115, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_112, c_12])).
% 2.37/1.38  tff(c_118, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_115])).
% 2.37/1.38  tff(c_121, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_118])).
% 2.37/1.38  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_121])).
% 2.37/1.38  tff(c_127, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_91])).
% 2.37/1.38  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_44, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_38, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_32, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_30, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_26, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.38  tff(c_143, plain, (![A_83, B_84, C_85, E_86]: (k8_relset_1(u1_struct_0(A_83), u1_struct_0(B_84), C_85, E_86)=k2_pre_topc(A_83, E_86) | ~m1_subset_1(E_86, k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(E_86, k1_zfmisc_1(u1_struct_0(B_84))) | ~v3_borsuk_1(C_85, A_83, B_84) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83), u1_struct_0(B_84)))) | ~v5_pre_topc(C_85, A_83, B_84) | ~v1_funct_2(C_85, u1_struct_0(A_83), u1_struct_0(B_84)) | ~v1_funct_1(C_85) | ~m1_pre_topc(B_84, A_83) | ~v4_tex_2(B_84, A_83) | v2_struct_0(B_84) | ~l1_pre_topc(A_83) | ~v3_tdlat_3(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.37/1.38  tff(c_148, plain, (![A_87, B_88, C_89, A_90]: (k8_relset_1(u1_struct_0(A_87), u1_struct_0(B_88), C_89, k1_tarski(A_90))=k2_pre_topc(A_87, k1_tarski(A_90)) | ~m1_subset_1(k1_tarski(A_90), k1_zfmisc_1(u1_struct_0(B_88))) | ~v3_borsuk_1(C_89, A_87, B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_87), u1_struct_0(B_88)))) | ~v5_pre_topc(C_89, A_87, B_88) | ~v1_funct_2(C_89, u1_struct_0(A_87), u1_struct_0(B_88)) | ~v1_funct_1(C_89) | ~m1_pre_topc(B_88, A_87) | ~v4_tex_2(B_88, A_87) | v2_struct_0(B_88) | ~l1_pre_topc(A_87) | ~v3_tdlat_3(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87) | ~r2_hidden(A_90, u1_struct_0(A_87)))), inference(resolution, [status(thm)], [c_4, c_143])).
% 2.37/1.38  tff(c_153, plain, (![A_91, B_92, C_93, A_94]: (k8_relset_1(u1_struct_0(A_91), u1_struct_0(B_92), C_93, k1_tarski(A_94))=k2_pre_topc(A_91, k1_tarski(A_94)) | ~v3_borsuk_1(C_93, A_91, B_92) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_91), u1_struct_0(B_92)))) | ~v5_pre_topc(C_93, A_91, B_92) | ~v1_funct_2(C_93, u1_struct_0(A_91), u1_struct_0(B_92)) | ~v1_funct_1(C_93) | ~m1_pre_topc(B_92, A_91) | ~v4_tex_2(B_92, A_91) | v2_struct_0(B_92) | ~l1_pre_topc(A_91) | ~v3_tdlat_3(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91) | ~r2_hidden(A_94, u1_struct_0(A_91)) | ~r2_hidden(A_94, u1_struct_0(B_92)))), inference(resolution, [status(thm)], [c_4, c_148])).
% 2.37/1.38  tff(c_158, plain, (![A_94]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(A_94))=k2_pre_topc('#skF_1', k1_tarski(A_94)) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r2_hidden(A_94, u1_struct_0('#skF_1')) | ~r2_hidden(A_94, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_153])).
% 2.37/1.38  tff(c_162, plain, (![A_94]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(A_94))=k2_pre_topc('#skF_1', k1_tarski(A_94)) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~r2_hidden(A_94, u1_struct_0('#skF_1')) | ~r2_hidden(A_94, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_38, c_36, c_34, c_32, c_30, c_26, c_158])).
% 2.37/1.38  tff(c_164, plain, (![A_95]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(A_95))=k2_pre_topc('#skF_1', k1_tarski(A_95)) | ~r2_hidden(A_95, u1_struct_0('#skF_1')) | ~r2_hidden(A_95, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_162])).
% 2.37/1.38  tff(c_126, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_91])).
% 2.37/1.38  tff(c_106, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_90])).
% 2.37/1.38  tff(c_18, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.37/1.38  tff(c_50, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 2.37/1.38  tff(c_141, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_106, c_50])).
% 2.37/1.38  tff(c_175, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_1')) | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_141])).
% 2.37/1.38  tff(c_177, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_175])).
% 2.37/1.38  tff(c_180, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_177])).
% 2.37/1.38  tff(c_183, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_180])).
% 2.37/1.38  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_183])).
% 2.37/1.38  tff(c_186, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_175])).
% 2.37/1.38  tff(c_190, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_186])).
% 2.37/1.38  tff(c_193, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_190])).
% 2.37/1.38  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_193])).
% 2.37/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.38  
% 2.37/1.38  Inference rules
% 2.37/1.38  ----------------------
% 2.37/1.38  #Ref     : 0
% 2.37/1.38  #Sup     : 28
% 2.37/1.38  #Fact    : 0
% 2.37/1.38  #Define  : 0
% 2.37/1.38  #Split   : 4
% 2.37/1.38  #Chain   : 0
% 2.37/1.38  #Close   : 0
% 2.37/1.38  
% 2.37/1.38  Ordering : KBO
% 2.37/1.38  
% 2.37/1.38  Simplification rules
% 2.37/1.38  ----------------------
% 2.37/1.38  #Subsume      : 0
% 2.37/1.38  #Demod        : 18
% 2.37/1.38  #Tautology    : 12
% 2.37/1.38  #SimpNegUnit  : 5
% 2.37/1.38  #BackRed      : 0
% 2.37/1.38  
% 2.37/1.38  #Partial instantiations: 0
% 2.37/1.38  #Strategies tried      : 1
% 2.37/1.38  
% 2.37/1.38  Timing (in seconds)
% 2.37/1.38  ----------------------
% 2.37/1.38  Preprocessing        : 0.36
% 2.37/1.38  Parsing              : 0.19
% 2.37/1.38  CNF conversion       : 0.03
% 2.37/1.38  Main loop            : 0.20
% 2.37/1.38  Inferencing          : 0.08
% 2.37/1.38  Reduction            : 0.06
% 2.37/1.38  Demodulation         : 0.04
% 2.37/1.38  BG Simplification    : 0.01
% 2.37/1.39  Subsumption          : 0.03
% 2.62/1.39  Abstraction          : 0.01
% 2.62/1.39  MUC search           : 0.00
% 2.62/1.39  Cooper               : 0.00
% 2.62/1.39  Total                : 0.60
% 2.62/1.39  Index Insertion      : 0.00
% 2.62/1.39  Index Deletion       : 0.00
% 2.62/1.39  Index Matching       : 0.00
% 2.62/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

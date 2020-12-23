%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:43 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 160 expanded)
%              Number of leaves         :   41 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  210 ( 716 expanded)
%              Number of equality atoms :   22 (  91 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_154,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_115,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_74,plain,(
    ! [B_83,A_84] :
      ( l1_pre_topc(B_83)
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_74])).

tff(c_80,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_77])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_98,plain,(
    ! [A_94,B_95] :
      ( k6_domain_1(A_94,B_95) = k1_tarski(B_95)
      | ~ m1_subset_1(B_95,A_94)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_115,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_18,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_118,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_18])).

tff(c_121,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_118])).

tff(c_124,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_121])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_124])).

tff(c_130,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_38,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_34,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_151,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(B_98)))
      | ~ m1_pre_topc(B_98,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_170,plain,(
    ! [A_101,A_102,B_103] :
      ( m1_subset_1(A_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc(B_103,A_102)
      | ~ l1_pre_topc(A_102)
      | ~ r1_tarski(A_101,u1_struct_0(B_103)) ) ),
    inference(resolution,[status(thm)],[c_12,c_151])).

tff(c_172,plain,(
    ! [A_101] :
      ( m1_subset_1(A_101,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_101,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_170])).

tff(c_175,plain,(
    ! [A_101] :
      ( m1_subset_1(A_101,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_101,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_172])).

tff(c_207,plain,(
    ! [A_108,B_109,C_110,E_111] :
      ( k8_relset_1(u1_struct_0(A_108),u1_struct_0(B_109),C_110,E_111) = k2_pre_topc(A_108,E_111)
      | ~ m1_subset_1(E_111,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(E_111,k1_zfmisc_1(u1_struct_0(B_109)))
      | ~ v3_borsuk_1(C_110,A_108,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),u1_struct_0(B_109))))
      | ~ v5_pre_topc(C_110,A_108,B_109)
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ m1_pre_topc(B_109,A_108)
      | ~ v4_tex_2(B_109,A_108)
      | v2_struct_0(B_109)
      | ~ l1_pre_topc(A_108)
      | ~ v3_tdlat_3(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_209,plain,(
    ! [B_109,C_110,A_101] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_109),C_110,A_101) = k2_pre_topc('#skF_1',A_101)
      | ~ m1_subset_1(A_101,k1_zfmisc_1(u1_struct_0(B_109)))
      | ~ v3_borsuk_1(C_110,'#skF_1',B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_109))))
      | ~ v5_pre_topc(C_110,'#skF_1',B_109)
      | ~ v1_funct_2(C_110,u1_struct_0('#skF_1'),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ m1_pre_topc(B_109,'#skF_1')
      | ~ v4_tex_2(B_109,'#skF_1')
      | v2_struct_0(B_109)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_101,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_175,c_207])).

tff(c_215,plain,(
    ! [B_109,C_110,A_101] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_109),C_110,A_101) = k2_pre_topc('#skF_1',A_101)
      | ~ m1_subset_1(A_101,k1_zfmisc_1(u1_struct_0(B_109)))
      | ~ v3_borsuk_1(C_110,'#skF_1',B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_109))))
      | ~ v5_pre_topc(C_110,'#skF_1',B_109)
      | ~ v1_funct_2(C_110,u1_struct_0('#skF_1'),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ m1_pre_topc(B_109,'#skF_1')
      | ~ v4_tex_2(B_109,'#skF_1')
      | v2_struct_0(B_109)
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_101,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_209])).

tff(c_317,plain,(
    ! [B_132,C_133,A_134] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_132),C_133,A_134) = k2_pre_topc('#skF_1',A_134)
      | ~ m1_subset_1(A_134,k1_zfmisc_1(u1_struct_0(B_132)))
      | ~ v3_borsuk_1(C_133,'#skF_1',B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_132))))
      | ~ v5_pre_topc(C_133,'#skF_1',B_132)
      | ~ v1_funct_2(C_133,u1_struct_0('#skF_1'),u1_struct_0(B_132))
      | ~ v1_funct_1(C_133)
      | ~ m1_pre_topc(B_132,'#skF_1')
      | ~ v4_tex_2(B_132,'#skF_1')
      | v2_struct_0(B_132)
      | ~ r1_tarski(A_134,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_215])).

tff(c_331,plain,(
    ! [B_135,C_136,A_137] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_135),C_136,A_137) = k2_pre_topc('#skF_1',A_137)
      | ~ v3_borsuk_1(C_136,'#skF_1',B_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_135))))
      | ~ v5_pre_topc(C_136,'#skF_1',B_135)
      | ~ v1_funct_2(C_136,u1_struct_0('#skF_1'),u1_struct_0(B_135))
      | ~ v1_funct_1(C_136)
      | ~ m1_pre_topc(B_135,'#skF_1')
      | ~ v4_tex_2(B_135,'#skF_1')
      | v2_struct_0(B_135)
      | ~ r1_tarski(A_137,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_137,u1_struct_0(B_135)) ) ),
    inference(resolution,[status(thm)],[c_12,c_317])).

tff(c_336,plain,(
    ! [A_137] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',A_137) = k2_pre_topc('#skF_1',A_137)
      | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ v4_tex_2('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_137,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_331])).

tff(c_340,plain,(
    ! [A_137] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',A_137) = k2_pre_topc('#skF_1',A_137)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_137,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_34,c_336])).

tff(c_342,plain,(
    ! [A_138] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',A_138) = k2_pre_topc('#skF_1',A_138)
      | ~ r1_tarski(A_138,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_340])).

tff(c_28,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_57,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_114,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_57,c_98])).

tff(c_135,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_138,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_135,c_18])).

tff(c_141,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_138])).

tff(c_144,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_144])).

tff(c_149,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_129,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_26,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_169,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_129,c_58])).

tff(c_353,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_169])).

tff(c_364,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_353])).

tff(c_381,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_364])).

tff(c_387,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_381])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:16:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.35  
% 2.71/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.35  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.35  
% 2.71/1.35  %Foreground sorts:
% 2.71/1.35  
% 2.71/1.35  
% 2.71/1.35  %Background operators:
% 2.71/1.35  
% 2.71/1.35  
% 2.71/1.35  %Foreground operators:
% 2.71/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.71/1.35  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.71/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.35  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.71/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.71/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.71/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.71/1.35  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.71/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.35  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.71/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.71/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.71/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.71/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.71/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.35  
% 2.92/1.37  tff(f_154, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 2.92/1.37  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.92/1.37  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.92/1.37  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.92/1.37  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.92/1.37  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.92/1.37  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.92/1.37  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.92/1.37  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.92/1.37  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 2.92/1.37  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_44, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_74, plain, (![B_83, A_84]: (l1_pre_topc(B_83) | ~m1_pre_topc(B_83, A_84) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.92/1.37  tff(c_77, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_74])).
% 2.92/1.37  tff(c_80, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_77])).
% 2.92/1.37  tff(c_14, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.37  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_98, plain, (![A_94, B_95]: (k6_domain_1(A_94, B_95)=k1_tarski(B_95) | ~m1_subset_1(B_95, A_94) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.92/1.37  tff(c_113, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_98])).
% 2.92/1.37  tff(c_115, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_113])).
% 2.92/1.37  tff(c_18, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.92/1.37  tff(c_118, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_115, c_18])).
% 2.92/1.37  tff(c_121, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_118])).
% 2.92/1.37  tff(c_124, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_121])).
% 2.92/1.37  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_124])).
% 2.92/1.37  tff(c_130, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_113])).
% 2.92/1.37  tff(c_8, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.37  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.37  tff(c_46, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_38, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_34, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.37  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_52, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_151, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(B_98))) | ~m1_pre_topc(B_98, A_97) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.92/1.37  tff(c_170, plain, (![A_101, A_102, B_103]: (m1_subset_1(A_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_pre_topc(B_103, A_102) | ~l1_pre_topc(A_102) | ~r1_tarski(A_101, u1_struct_0(B_103)))), inference(resolution, [status(thm)], [c_12, c_151])).
% 2.92/1.37  tff(c_172, plain, (![A_101]: (m1_subset_1(A_101, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_101, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_170])).
% 2.92/1.37  tff(c_175, plain, (![A_101]: (m1_subset_1(A_101, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_101, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_172])).
% 2.92/1.37  tff(c_207, plain, (![A_108, B_109, C_110, E_111]: (k8_relset_1(u1_struct_0(A_108), u1_struct_0(B_109), C_110, E_111)=k2_pre_topc(A_108, E_111) | ~m1_subset_1(E_111, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(E_111, k1_zfmisc_1(u1_struct_0(B_109))) | ~v3_borsuk_1(C_110, A_108, B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108), u1_struct_0(B_109)))) | ~v5_pre_topc(C_110, A_108, B_109) | ~v1_funct_2(C_110, u1_struct_0(A_108), u1_struct_0(B_109)) | ~v1_funct_1(C_110) | ~m1_pre_topc(B_109, A_108) | ~v4_tex_2(B_109, A_108) | v2_struct_0(B_109) | ~l1_pre_topc(A_108) | ~v3_tdlat_3(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.92/1.37  tff(c_209, plain, (![B_109, C_110, A_101]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_109), C_110, A_101)=k2_pre_topc('#skF_1', A_101) | ~m1_subset_1(A_101, k1_zfmisc_1(u1_struct_0(B_109))) | ~v3_borsuk_1(C_110, '#skF_1', B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_109)))) | ~v5_pre_topc(C_110, '#skF_1', B_109) | ~v1_funct_2(C_110, u1_struct_0('#skF_1'), u1_struct_0(B_109)) | ~v1_funct_1(C_110) | ~m1_pre_topc(B_109, '#skF_1') | ~v4_tex_2(B_109, '#skF_1') | v2_struct_0(B_109) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski(A_101, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_175, c_207])).
% 2.92/1.37  tff(c_215, plain, (![B_109, C_110, A_101]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_109), C_110, A_101)=k2_pre_topc('#skF_1', A_101) | ~m1_subset_1(A_101, k1_zfmisc_1(u1_struct_0(B_109))) | ~v3_borsuk_1(C_110, '#skF_1', B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_109)))) | ~v5_pre_topc(C_110, '#skF_1', B_109) | ~v1_funct_2(C_110, u1_struct_0('#skF_1'), u1_struct_0(B_109)) | ~v1_funct_1(C_110) | ~m1_pre_topc(B_109, '#skF_1') | ~v4_tex_2(B_109, '#skF_1') | v2_struct_0(B_109) | v2_struct_0('#skF_1') | ~r1_tarski(A_101, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_209])).
% 2.92/1.37  tff(c_317, plain, (![B_132, C_133, A_134]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_132), C_133, A_134)=k2_pre_topc('#skF_1', A_134) | ~m1_subset_1(A_134, k1_zfmisc_1(u1_struct_0(B_132))) | ~v3_borsuk_1(C_133, '#skF_1', B_132) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_132)))) | ~v5_pre_topc(C_133, '#skF_1', B_132) | ~v1_funct_2(C_133, u1_struct_0('#skF_1'), u1_struct_0(B_132)) | ~v1_funct_1(C_133) | ~m1_pre_topc(B_132, '#skF_1') | ~v4_tex_2(B_132, '#skF_1') | v2_struct_0(B_132) | ~r1_tarski(A_134, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_215])).
% 2.92/1.37  tff(c_331, plain, (![B_135, C_136, A_137]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_135), C_136, A_137)=k2_pre_topc('#skF_1', A_137) | ~v3_borsuk_1(C_136, '#skF_1', B_135) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_135)))) | ~v5_pre_topc(C_136, '#skF_1', B_135) | ~v1_funct_2(C_136, u1_struct_0('#skF_1'), u1_struct_0(B_135)) | ~v1_funct_1(C_136) | ~m1_pre_topc(B_135, '#skF_1') | ~v4_tex_2(B_135, '#skF_1') | v2_struct_0(B_135) | ~r1_tarski(A_137, u1_struct_0('#skF_2')) | ~r1_tarski(A_137, u1_struct_0(B_135)))), inference(resolution, [status(thm)], [c_12, c_317])).
% 2.92/1.37  tff(c_336, plain, (![A_137]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', A_137)=k2_pre_topc('#skF_1', A_137) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~r1_tarski(A_137, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_331])).
% 2.92/1.37  tff(c_340, plain, (![A_137]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', A_137)=k2_pre_topc('#skF_1', A_137) | v2_struct_0('#skF_2') | ~r1_tarski(A_137, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_34, c_336])).
% 2.92/1.37  tff(c_342, plain, (![A_138]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', A_138)=k2_pre_topc('#skF_1', A_138) | ~r1_tarski(A_138, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_340])).
% 2.92/1.37  tff(c_28, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_57, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 2.92/1.37  tff(c_114, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_57, c_98])).
% 2.92/1.37  tff(c_135, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_114])).
% 2.92/1.37  tff(c_138, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_135, c_18])).
% 2.92/1.37  tff(c_141, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_138])).
% 2.92/1.37  tff(c_144, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_141])).
% 2.92/1.37  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_144])).
% 2.92/1.37  tff(c_149, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_114])).
% 2.92/1.37  tff(c_129, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_113])).
% 2.92/1.37  tff(c_26, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.37  tff(c_58, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 2.92/1.37  tff(c_169, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_129, c_58])).
% 2.92/1.37  tff(c_353, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_169])).
% 2.92/1.37  tff(c_364, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_353])).
% 2.92/1.37  tff(c_381, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_364])).
% 2.92/1.37  tff(c_387, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_381])).
% 2.92/1.37  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_387])).
% 2.92/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.37  
% 2.92/1.37  Inference rules
% 2.92/1.37  ----------------------
% 2.92/1.37  #Ref     : 0
% 2.92/1.37  #Sup     : 65
% 2.92/1.37  #Fact    : 0
% 2.92/1.37  #Define  : 0
% 2.92/1.37  #Split   : 5
% 2.92/1.37  #Chain   : 0
% 2.92/1.37  #Close   : 0
% 2.92/1.37  
% 2.92/1.37  Ordering : KBO
% 2.92/1.37  
% 2.92/1.37  Simplification rules
% 2.92/1.37  ----------------------
% 2.92/1.37  #Subsume      : 6
% 2.92/1.37  #Demod        : 36
% 2.92/1.37  #Tautology    : 18
% 2.92/1.37  #SimpNegUnit  : 10
% 2.92/1.37  #BackRed      : 0
% 2.92/1.37  
% 2.92/1.37  #Partial instantiations: 0
% 2.92/1.37  #Strategies tried      : 1
% 2.92/1.37  
% 2.92/1.37  Timing (in seconds)
% 2.92/1.37  ----------------------
% 2.92/1.37  Preprocessing        : 0.33
% 2.92/1.37  Parsing              : 0.18
% 2.92/1.37  CNF conversion       : 0.02
% 2.92/1.37  Main loop            : 0.28
% 2.92/1.37  Inferencing          : 0.10
% 2.92/1.37  Reduction            : 0.08
% 2.92/1.37  Demodulation         : 0.06
% 2.92/1.37  BG Simplification    : 0.02
% 2.92/1.38  Subsumption          : 0.06
% 2.92/1.38  Abstraction          : 0.01
% 2.92/1.38  MUC search           : 0.00
% 2.92/1.38  Cooper               : 0.00
% 2.92/1.38  Total                : 0.65
% 2.92/1.38  Index Insertion      : 0.00
% 2.92/1.38  Index Deletion       : 0.00
% 2.92/1.38  Index Matching       : 0.00
% 2.92/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

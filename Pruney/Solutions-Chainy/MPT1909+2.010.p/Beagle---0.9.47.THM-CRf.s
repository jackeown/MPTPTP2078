%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:38 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 200 expanded)
%              Number of leaves         :   39 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  236 ( 986 expanded)
%              Number of equality atoms :   20 ( 128 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

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

tff(f_174,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_135,axiom,(
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

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_24,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_53,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_87,plain,(
    ! [A_92,B_93] :
      ( k6_domain_1(A_92,B_93) = k1_tarski(B_93)
      | ~ m1_subset_1(B_93,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_98,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_53,c_87])).

tff(c_100,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_18,plain,(
    ! [B_26,A_24] :
      ( r2_hidden(B_26,k1_connsp_2(A_24,B_26))
      | ~ m1_subset_1(B_26,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_116,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1(k1_connsp_2(A_101,B_102),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [C_4,B_3,A_2] :
      ( ~ v1_xboole_0(C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(C_4))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_154,plain,(
    ! [A_109,A_110,B_111] :
      ( ~ v1_xboole_0(u1_struct_0(A_109))
      | ~ r2_hidden(A_110,k1_connsp_2(A_109,B_111))
      | ~ m1_subset_1(B_111,u1_struct_0(A_109))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_116,c_4])).

tff(c_159,plain,(
    ! [A_112,B_113] :
      ( ~ v1_xboole_0(u1_struct_0(A_112))
      | ~ m1_subset_1(B_113,u1_struct_0(A_112))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_18,c_154])).

tff(c_162,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_53,c_159])).

tff(c_168,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_100,c_162])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_168])).

tff(c_171,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_40,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_80,plain,(
    ! [B_90,A_91] :
      ( v2_pre_topc(B_90)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,
    ( v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_86,plain,(
    v2_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_83])).

tff(c_68,plain,(
    ! [B_85,A_86] :
      ( l1_pre_topc(B_85)
      | ~ m1_pre_topc(B_85,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_71,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_71])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_99,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_173,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_235,plain,(
    ! [A_125,B_126] :
      ( m1_subset_1(k1_connsp_2(A_125,B_126),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_286,plain,(
    ! [A_130,A_131,B_132] :
      ( ~ v1_xboole_0(u1_struct_0(A_130))
      | ~ r2_hidden(A_131,k1_connsp_2(A_130,B_132))
      | ~ m1_subset_1(B_132,u1_struct_0(A_130))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_235,c_4])).

tff(c_291,plain,(
    ! [A_133,B_134] :
      ( ~ v1_xboole_0(u1_struct_0(A_133))
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_18,c_286])).

tff(c_297,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_291])).

tff(c_304,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_74,c_173,c_297])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_304])).

tff(c_307,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_22,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_54,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_351,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_307,c_54])).

tff(c_42,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_34,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_30,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_308,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_313,plain,(
    ! [A_135,B_136] :
      ( m1_subset_1(k6_domain_1(A_135,B_136),k1_zfmisc_1(A_135))
      | ~ m1_subset_1(B_136,A_135)
      | v1_xboole_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_321,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_313])).

tff(c_325,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_321])).

tff(c_326,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_325])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_48,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_172,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_12,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k6_domain_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_330,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_334,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_330])).

tff(c_335,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_334])).

tff(c_539,plain,(
    ! [A_171,B_172,C_173,E_174] :
      ( k8_relset_1(u1_struct_0(A_171),u1_struct_0(B_172),C_173,E_174) = k2_pre_topc(A_171,E_174)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ m1_subset_1(E_174,k1_zfmisc_1(u1_struct_0(B_172)))
      | ~ v3_borsuk_1(C_173,A_171,B_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),u1_struct_0(B_172))))
      | ~ v5_pre_topc(C_173,A_171,B_172)
      | ~ v1_funct_2(C_173,u1_struct_0(A_171),u1_struct_0(B_172))
      | ~ v1_funct_1(C_173)
      | ~ m1_pre_topc(B_172,A_171)
      | ~ v4_tex_2(B_172,A_171)
      | v2_struct_0(B_172)
      | ~ l1_pre_topc(A_171)
      | ~ v3_tdlat_3(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_551,plain,(
    ! [B_172,C_173] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_172),C_173,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_172)))
      | ~ v3_borsuk_1(C_173,'#skF_1',B_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_172))))
      | ~ v5_pre_topc(C_173,'#skF_1',B_172)
      | ~ v1_funct_2(C_173,u1_struct_0('#skF_1'),u1_struct_0(B_172))
      | ~ v1_funct_1(C_173)
      | ~ m1_pre_topc(B_172,'#skF_1')
      | ~ v4_tex_2(B_172,'#skF_1')
      | v2_struct_0(B_172)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_335,c_539])).

tff(c_564,plain,(
    ! [B_172,C_173] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_172),C_173,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_172)))
      | ~ v3_borsuk_1(C_173,'#skF_1',B_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_172))))
      | ~ v5_pre_topc(C_173,'#skF_1',B_172)
      | ~ v1_funct_2(C_173,u1_struct_0('#skF_1'),u1_struct_0(B_172))
      | ~ v1_funct_1(C_173)
      | ~ m1_pre_topc(B_172,'#skF_1')
      | ~ v4_tex_2(B_172,'#skF_1')
      | v2_struct_0(B_172)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_551])).

tff(c_593,plain,(
    ! [B_185,C_186] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_185),C_186,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_185)))
      | ~ v3_borsuk_1(C_186,'#skF_1',B_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_185))))
      | ~ v5_pre_topc(C_186,'#skF_1',B_185)
      | ~ v1_funct_2(C_186,u1_struct_0('#skF_1'),u1_struct_0(B_185))
      | ~ v1_funct_1(C_186)
      | ~ m1_pre_topc(B_185,'#skF_1')
      | ~ v4_tex_2(B_185,'#skF_1')
      | v2_struct_0(B_185) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_564])).

tff(c_600,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v4_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_593])).

tff(c_604,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_30,c_326,c_600])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_351,c_604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.48  
% 3.11/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.49  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.11/1.49  
% 3.11/1.49  %Foreground sorts:
% 3.11/1.49  
% 3.11/1.49  
% 3.11/1.49  %Background operators:
% 3.11/1.49  
% 3.11/1.49  
% 3.11/1.49  %Foreground operators:
% 3.11/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.11/1.49  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.11/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.49  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.11/1.49  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.11/1.49  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.11/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.49  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.11/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.11/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.49  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.11/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.49  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.11/1.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.11/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.11/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.49  
% 3.11/1.50  tff(f_174, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.11/1.50  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.11/1.50  tff(f_97, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.11/1.50  tff(f_85, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.11/1.50  tff(f_34, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.11/1.50  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.11/1.50  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.11/1.50  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.11/1.50  tff(f_135, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.11/1.50  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_24, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_26, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_53, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 3.11/1.50  tff(c_87, plain, (![A_92, B_93]: (k6_domain_1(A_92, B_93)=k1_tarski(B_93) | ~m1_subset_1(B_93, A_92) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.11/1.50  tff(c_98, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_53, c_87])).
% 3.11/1.50  tff(c_100, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_98])).
% 3.11/1.50  tff(c_18, plain, (![B_26, A_24]: (r2_hidden(B_26, k1_connsp_2(A_24, B_26)) | ~m1_subset_1(B_26, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.11/1.50  tff(c_116, plain, (![A_101, B_102]: (m1_subset_1(k1_connsp_2(A_101, B_102), k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.11/1.50  tff(c_4, plain, (![C_4, B_3, A_2]: (~v1_xboole_0(C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(C_4)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.11/1.50  tff(c_154, plain, (![A_109, A_110, B_111]: (~v1_xboole_0(u1_struct_0(A_109)) | ~r2_hidden(A_110, k1_connsp_2(A_109, B_111)) | ~m1_subset_1(B_111, u1_struct_0(A_109)) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_116, c_4])).
% 3.11/1.50  tff(c_159, plain, (![A_112, B_113]: (~v1_xboole_0(u1_struct_0(A_112)) | ~m1_subset_1(B_113, u1_struct_0(A_112)) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(resolution, [status(thm)], [c_18, c_154])).
% 3.11/1.50  tff(c_162, plain, (~v1_xboole_0(u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_53, c_159])).
% 3.11/1.50  tff(c_168, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_100, c_162])).
% 3.11/1.50  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_168])).
% 3.11/1.50  tff(c_171, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 3.11/1.50  tff(c_40, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_80, plain, (![B_90, A_91]: (v2_pre_topc(B_90) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.11/1.50  tff(c_83, plain, (v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_80])).
% 3.11/1.50  tff(c_86, plain, (v2_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_83])).
% 3.11/1.50  tff(c_68, plain, (![B_85, A_86]: (l1_pre_topc(B_85) | ~m1_pre_topc(B_85, A_86) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.11/1.50  tff(c_71, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_68])).
% 3.11/1.50  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_71])).
% 3.11/1.50  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_87])).
% 3.11/1.50  tff(c_173, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_99])).
% 3.11/1.50  tff(c_235, plain, (![A_125, B_126]: (m1_subset_1(k1_connsp_2(A_125, B_126), k1_zfmisc_1(u1_struct_0(A_125))) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.11/1.50  tff(c_286, plain, (![A_130, A_131, B_132]: (~v1_xboole_0(u1_struct_0(A_130)) | ~r2_hidden(A_131, k1_connsp_2(A_130, B_132)) | ~m1_subset_1(B_132, u1_struct_0(A_130)) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_235, c_4])).
% 3.11/1.50  tff(c_291, plain, (![A_133, B_134]: (~v1_xboole_0(u1_struct_0(A_133)) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(resolution, [status(thm)], [c_18, c_286])).
% 3.11/1.50  tff(c_297, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_291])).
% 3.11/1.50  tff(c_304, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_74, c_173, c_297])).
% 3.11/1.50  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_304])).
% 3.11/1.50  tff(c_307, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_99])).
% 3.11/1.50  tff(c_22, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_54, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 3.11/1.50  tff(c_351, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_307, c_54])).
% 3.11/1.50  tff(c_42, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_36, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_34, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_30, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_308, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_99])).
% 3.11/1.50  tff(c_313, plain, (![A_135, B_136]: (m1_subset_1(k6_domain_1(A_135, B_136), k1_zfmisc_1(A_135)) | ~m1_subset_1(B_136, A_135) | v1_xboole_0(A_135))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.11/1.50  tff(c_321, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_313])).
% 3.11/1.50  tff(c_325, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_321])).
% 3.11/1.50  tff(c_326, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_308, c_325])).
% 3.11/1.50  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_48, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.11/1.50  tff(c_172, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_98])).
% 3.11/1.50  tff(c_12, plain, (![A_18, B_19]: (m1_subset_1(k6_domain_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.11/1.50  tff(c_330, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_12])).
% 3.11/1.50  tff(c_334, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_330])).
% 3.11/1.50  tff(c_335, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_172, c_334])).
% 3.11/1.50  tff(c_539, plain, (![A_171, B_172, C_173, E_174]: (k8_relset_1(u1_struct_0(A_171), u1_struct_0(B_172), C_173, E_174)=k2_pre_topc(A_171, E_174) | ~m1_subset_1(E_174, k1_zfmisc_1(u1_struct_0(A_171))) | ~m1_subset_1(E_174, k1_zfmisc_1(u1_struct_0(B_172))) | ~v3_borsuk_1(C_173, A_171, B_172) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), u1_struct_0(B_172)))) | ~v5_pre_topc(C_173, A_171, B_172) | ~v1_funct_2(C_173, u1_struct_0(A_171), u1_struct_0(B_172)) | ~v1_funct_1(C_173) | ~m1_pre_topc(B_172, A_171) | ~v4_tex_2(B_172, A_171) | v2_struct_0(B_172) | ~l1_pre_topc(A_171) | ~v3_tdlat_3(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.11/1.50  tff(c_551, plain, (![B_172, C_173]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_172), C_173, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_172))) | ~v3_borsuk_1(C_173, '#skF_1', B_172) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_172)))) | ~v5_pre_topc(C_173, '#skF_1', B_172) | ~v1_funct_2(C_173, u1_struct_0('#skF_1'), u1_struct_0(B_172)) | ~v1_funct_1(C_173) | ~m1_pre_topc(B_172, '#skF_1') | ~v4_tex_2(B_172, '#skF_1') | v2_struct_0(B_172) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_335, c_539])).
% 3.11/1.50  tff(c_564, plain, (![B_172, C_173]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_172), C_173, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_172))) | ~v3_borsuk_1(C_173, '#skF_1', B_172) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_172)))) | ~v5_pre_topc(C_173, '#skF_1', B_172) | ~v1_funct_2(C_173, u1_struct_0('#skF_1'), u1_struct_0(B_172)) | ~v1_funct_1(C_173) | ~m1_pre_topc(B_172, '#skF_1') | ~v4_tex_2(B_172, '#skF_1') | v2_struct_0(B_172) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_551])).
% 3.11/1.50  tff(c_593, plain, (![B_185, C_186]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_185), C_186, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_185))) | ~v3_borsuk_1(C_186, '#skF_1', B_185) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_185)))) | ~v5_pre_topc(C_186, '#skF_1', B_185) | ~v1_funct_2(C_186, u1_struct_0('#skF_1'), u1_struct_0(B_185)) | ~v1_funct_1(C_186) | ~m1_pre_topc(B_185, '#skF_1') | ~v4_tex_2(B_185, '#skF_1') | v2_struct_0(B_185))), inference(negUnitSimplification, [status(thm)], [c_52, c_564])).
% 3.11/1.50  tff(c_600, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_593])).
% 3.11/1.50  tff(c_604, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_30, c_326, c_600])).
% 3.11/1.50  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_351, c_604])).
% 3.11/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.50  
% 3.11/1.50  Inference rules
% 3.11/1.50  ----------------------
% 3.11/1.50  #Ref     : 0
% 3.11/1.50  #Sup     : 125
% 3.11/1.50  #Fact    : 0
% 3.11/1.50  #Define  : 0
% 3.11/1.50  #Split   : 13
% 3.11/1.50  #Chain   : 0
% 3.11/1.50  #Close   : 0
% 3.11/1.50  
% 3.11/1.50  Ordering : KBO
% 3.11/1.50  
% 3.11/1.50  Simplification rules
% 3.11/1.50  ----------------------
% 3.11/1.50  #Subsume      : 12
% 3.11/1.50  #Demod        : 58
% 3.11/1.50  #Tautology    : 34
% 3.11/1.50  #SimpNegUnit  : 16
% 3.11/1.50  #BackRed      : 0
% 3.11/1.50  
% 3.11/1.50  #Partial instantiations: 0
% 3.11/1.50  #Strategies tried      : 1
% 3.11/1.50  
% 3.11/1.50  Timing (in seconds)
% 3.11/1.50  ----------------------
% 3.11/1.51  Preprocessing        : 0.34
% 3.11/1.51  Parsing              : 0.18
% 3.11/1.51  CNF conversion       : 0.03
% 3.11/1.51  Main loop            : 0.38
% 3.11/1.51  Inferencing          : 0.14
% 3.11/1.51  Reduction            : 0.11
% 3.11/1.51  Demodulation         : 0.08
% 3.11/1.51  BG Simplification    : 0.02
% 3.11/1.51  Subsumption          : 0.07
% 3.11/1.51  Abstraction          : 0.02
% 3.11/1.51  MUC search           : 0.00
% 3.11/1.51  Cooper               : 0.00
% 3.11/1.51  Total                : 0.76
% 3.11/1.51  Index Insertion      : 0.00
% 3.11/1.51  Index Deletion       : 0.00
% 3.11/1.51  Index Matching       : 0.00
% 3.11/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

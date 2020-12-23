%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:38 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 296 expanded)
%              Number of leaves         :   42 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  253 (1447 expanded)
%              Number of equality atoms :   25 ( 183 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v4_pre_topc > v3_pre_topc > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_169,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_130,axiom,(
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
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_417,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k8_relset_1(A_135,B_136,C_137,D_138) = k10_relat_1(C_137,D_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_424,plain,(
    ! [D_138] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_138) = k10_relat_1('#skF_4',D_138) ),
    inference(resolution,[status(thm)],[c_38,c_417])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_88,plain,(
    ! [B_87,A_88] :
      ( v2_pre_topc(B_87)
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_88])).

tff(c_94,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_91])).

tff(c_74,plain,(
    ! [B_82,A_83] :
      ( l1_pre_topc(B_82)
      | ~ m1_pre_topc(B_82,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_80,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77])).

tff(c_30,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_59,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_95,plain,(
    ! [A_89,B_90] :
      ( k6_domain_1(A_89,B_90) = k1_tarski(B_90)
      | ~ m1_subset_1(B_90,A_89)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_59,c_95])).

tff(c_266,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_314,plain,(
    ! [A_123] :
      ( m1_subset_1('#skF_1'(A_123),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v1_xboole_0(B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_2))
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_329,plain,(
    ! [A_126] :
      ( v1_xboole_0('#skF_1'(A_126))
      | ~ v1_xboole_0(u1_struct_0(A_126))
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_314,c_4])).

tff(c_335,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_266,c_329])).

tff(c_339,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_80,c_335])).

tff(c_340,plain,(
    v1_xboole_0('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_339])).

tff(c_20,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0('#skF_1'(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_343,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_340,c_20])).

tff(c_346,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_80,c_343])).

tff(c_348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_346])).

tff(c_349,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_106,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_95])).

tff(c_109,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_209,plain,(
    ! [B_108,A_109] :
      ( m1_subset_1(u1_struct_0(B_108),k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_242,plain,(
    ! [B_112,A_113] :
      ( v1_xboole_0(u1_struct_0(B_112))
      | ~ v1_xboole_0(u1_struct_0(A_113))
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_209,c_4])).

tff(c_244,plain,(
    ! [B_112] :
      ( v1_xboole_0(u1_struct_0(B_112))
      | ~ m1_pre_topc(B_112,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_109,c_242])).

tff(c_248,plain,(
    ! [B_114] :
      ( v1_xboole_0(u1_struct_0(B_114))
      | ~ m1_pre_topc(B_114,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_244])).

tff(c_110,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_141,plain,(
    ! [A_99] :
      ( m1_subset_1('#skF_1'(A_99),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_171,plain,(
    ! [A_106] :
      ( v1_xboole_0('#skF_1'(A_106))
      | ~ v1_xboole_0(u1_struct_0(A_106))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_141,c_4])).

tff(c_180,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_171])).

tff(c_188,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_80,c_180])).

tff(c_189,plain,(
    v1_xboole_0('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_188])).

tff(c_196,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_189,c_20])).

tff(c_199,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_80,c_196])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_199])).

tff(c_203,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_253,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_248,c_203])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_253])).

tff(c_259,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_28,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_60,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_351,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_60])).

tff(c_352,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_351])).

tff(c_425,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_6')) != k10_relat_1('#skF_4',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_352])).

tff(c_48,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_40,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_36,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_350,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_366,plain,(
    ! [A_129,B_130] :
      ( m1_subset_1(k6_domain_1(A_129,B_130),k1_zfmisc_1(A_129))
      | ~ m1_subset_1(B_130,A_129)
      | v1_xboole_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_375,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_366])).

tff(c_382,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_375])).

tff(c_383,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_382])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_54,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_260,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_378,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_366])).

tff(c_385,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_378])).

tff(c_386,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_385])).

tff(c_435,plain,(
    ! [A_140,B_141,C_142,E_143] :
      ( k8_relset_1(u1_struct_0(A_140),u1_struct_0(B_141),C_142,E_143) = k2_pre_topc(A_140,E_143)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(u1_struct_0(B_141)))
      | ~ v3_borsuk_1(C_142,A_140,B_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140),u1_struct_0(B_141))))
      | ~ v5_pre_topc(C_142,A_140,B_141)
      | ~ v1_funct_2(C_142,u1_struct_0(A_140),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ m1_pre_topc(B_141,A_140)
      | ~ v4_tex_2(B_141,A_140)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_140)
      | ~ v3_tdlat_3(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_437,plain,(
    ! [B_141,C_142] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_141),C_142,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_141)))
      | ~ v3_borsuk_1(C_142,'#skF_2',B_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(C_142,'#skF_2',B_141)
      | ~ v1_funct_2(C_142,u1_struct_0('#skF_2'),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ m1_pre_topc(B_141,'#skF_2')
      | ~ v4_tex_2(B_141,'#skF_2')
      | v2_struct_0(B_141)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_386,c_435])).

tff(c_449,plain,(
    ! [B_141,C_142] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_141),C_142,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_141)))
      | ~ v3_borsuk_1(C_142,'#skF_2',B_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(C_142,'#skF_2',B_141)
      | ~ v1_funct_2(C_142,u1_struct_0('#skF_2'),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ m1_pre_topc(B_141,'#skF_2')
      | ~ v4_tex_2(B_141,'#skF_2')
      | v2_struct_0(B_141)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_437])).

tff(c_578,plain,(
    ! [B_160,C_161] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_160),C_161,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_160)))
      | ~ v3_borsuk_1(C_161,'#skF_2',B_160)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_160))))
      | ~ v5_pre_topc(C_161,'#skF_2',B_160)
      | ~ v1_funct_2(C_161,u1_struct_0('#skF_2'),u1_struct_0(B_160))
      | ~ v1_funct_1(C_161)
      | ~ m1_pre_topc(B_160,'#skF_2')
      | ~ v4_tex_2(B_160,'#skF_2')
      | v2_struct_0(B_160) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_449])).

tff(c_585,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_578])).

tff(c_589,plain,
    ( k2_pre_topc('#skF_2',k1_tarski('#skF_6')) = k10_relat_1('#skF_4',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_36,c_383,c_424,c_585])).

tff(c_591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_425,c_589])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:41:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.48  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v4_pre_topc > v3_pre_topc > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.12/1.48  
% 3.12/1.48  %Foreground sorts:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Background operators:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Foreground operators:
% 3.12/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.12/1.48  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.12/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.12/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.48  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.12/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.12/1.48  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.12/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.12/1.48  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.12/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.12/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.12/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.48  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.12/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.12/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.48  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.12/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.12/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.12/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.12/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.12/1.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.12/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.48  
% 3.28/1.50  tff(f_169, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.28/1.50  tff(f_38, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.28/1.50  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.28/1.50  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.28/1.50  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.28/1.50  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 3.28/1.50  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.28/1.50  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.28/1.50  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.28/1.50  tff(f_130, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.28/1.50  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_417, plain, (![A_135, B_136, C_137, D_138]: (k8_relset_1(A_135, B_136, C_137, D_138)=k10_relat_1(C_137, D_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.28/1.50  tff(c_424, plain, (![D_138]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_138)=k10_relat_1('#skF_4', D_138))), inference(resolution, [status(thm)], [c_38, c_417])).
% 3.28/1.50  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_88, plain, (![B_87, A_88]: (v2_pre_topc(B_87) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.50  tff(c_91, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_88])).
% 3.28/1.50  tff(c_94, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_91])).
% 3.28/1.50  tff(c_74, plain, (![B_82, A_83]: (l1_pre_topc(B_82) | ~m1_pre_topc(B_82, A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.50  tff(c_77, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_74])).
% 3.28/1.50  tff(c_80, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_77])).
% 3.28/1.50  tff(c_30, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_59, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 3.28/1.50  tff(c_95, plain, (![A_89, B_90]: (k6_domain_1(A_89, B_90)=k1_tarski(B_90) | ~m1_subset_1(B_90, A_89) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.28/1.50  tff(c_107, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_59, c_95])).
% 3.28/1.50  tff(c_266, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_107])).
% 3.28/1.50  tff(c_314, plain, (![A_123]: (m1_subset_1('#skF_1'(A_123), k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.28/1.50  tff(c_4, plain, (![B_4, A_2]: (v1_xboole_0(B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_2)) | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.50  tff(c_329, plain, (![A_126]: (v1_xboole_0('#skF_1'(A_126)) | ~v1_xboole_0(u1_struct_0(A_126)) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(resolution, [status(thm)], [c_314, c_4])).
% 3.28/1.50  tff(c_335, plain, (v1_xboole_0('#skF_1'('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_266, c_329])).
% 3.28/1.50  tff(c_339, plain, (v1_xboole_0('#skF_1'('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_80, c_335])).
% 3.28/1.50  tff(c_340, plain, (v1_xboole_0('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_339])).
% 3.28/1.50  tff(c_20, plain, (![A_19]: (~v1_xboole_0('#skF_1'(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.28/1.50  tff(c_343, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_340, c_20])).
% 3.28/1.50  tff(c_346, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_80, c_343])).
% 3.28/1.50  tff(c_348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_346])).
% 3.28/1.50  tff(c_349, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_107])).
% 3.28/1.50  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_106, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_95])).
% 3.28/1.50  tff(c_109, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_106])).
% 3.28/1.50  tff(c_209, plain, (![B_108, A_109]: (m1_subset_1(u1_struct_0(B_108), k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_pre_topc(B_108, A_109) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.28/1.50  tff(c_242, plain, (![B_112, A_113]: (v1_xboole_0(u1_struct_0(B_112)) | ~v1_xboole_0(u1_struct_0(A_113)) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_209, c_4])).
% 3.28/1.50  tff(c_244, plain, (![B_112]: (v1_xboole_0(u1_struct_0(B_112)) | ~m1_pre_topc(B_112, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_109, c_242])).
% 3.28/1.50  tff(c_248, plain, (![B_114]: (v1_xboole_0(u1_struct_0(B_114)) | ~m1_pre_topc(B_114, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_244])).
% 3.28/1.50  tff(c_110, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_107])).
% 3.28/1.50  tff(c_141, plain, (![A_99]: (m1_subset_1('#skF_1'(A_99), k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.28/1.50  tff(c_171, plain, (![A_106]: (v1_xboole_0('#skF_1'(A_106)) | ~v1_xboole_0(u1_struct_0(A_106)) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_141, c_4])).
% 3.28/1.50  tff(c_180, plain, (v1_xboole_0('#skF_1'('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_110, c_171])).
% 3.28/1.50  tff(c_188, plain, (v1_xboole_0('#skF_1'('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_80, c_180])).
% 3.28/1.50  tff(c_189, plain, (v1_xboole_0('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_188])).
% 3.28/1.50  tff(c_196, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_189, c_20])).
% 3.28/1.50  tff(c_199, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_80, c_196])).
% 3.28/1.50  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_199])).
% 3.28/1.50  tff(c_203, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_107])).
% 3.28/1.50  tff(c_253, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_248, c_203])).
% 3.28/1.50  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_253])).
% 3.28/1.50  tff(c_259, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_106])).
% 3.28/1.50  tff(c_28, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_60, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 3.28/1.50  tff(c_351, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_60])).
% 3.28/1.50  tff(c_352, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_351])).
% 3.28/1.50  tff(c_425, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_6'))!=k10_relat_1('#skF_4', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_352])).
% 3.28/1.50  tff(c_48, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_42, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_40, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_36, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_350, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_107])).
% 3.28/1.50  tff(c_366, plain, (![A_129, B_130]: (m1_subset_1(k6_domain_1(A_129, B_130), k1_zfmisc_1(A_129)) | ~m1_subset_1(B_130, A_129) | v1_xboole_0(A_129))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.28/1.50  tff(c_375, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_349, c_366])).
% 3.28/1.50  tff(c_382, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_375])).
% 3.28/1.50  tff(c_383, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_350, c_382])).
% 3.28/1.50  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_54, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.28/1.50  tff(c_260, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_106])).
% 3.28/1.50  tff(c_378, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_366])).
% 3.28/1.50  tff(c_385, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_378])).
% 3.28/1.50  tff(c_386, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_260, c_385])).
% 3.28/1.50  tff(c_435, plain, (![A_140, B_141, C_142, E_143]: (k8_relset_1(u1_struct_0(A_140), u1_struct_0(B_141), C_142, E_143)=k2_pre_topc(A_140, E_143) | ~m1_subset_1(E_143, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(E_143, k1_zfmisc_1(u1_struct_0(B_141))) | ~v3_borsuk_1(C_142, A_140, B_141) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140), u1_struct_0(B_141)))) | ~v5_pre_topc(C_142, A_140, B_141) | ~v1_funct_2(C_142, u1_struct_0(A_140), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~m1_pre_topc(B_141, A_140) | ~v4_tex_2(B_141, A_140) | v2_struct_0(B_141) | ~l1_pre_topc(A_140) | ~v3_tdlat_3(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.28/1.50  tff(c_437, plain, (![B_141, C_142]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_141), C_142, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_141))) | ~v3_borsuk_1(C_142, '#skF_2', B_141) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_141)))) | ~v5_pre_topc(C_142, '#skF_2', B_141) | ~v1_funct_2(C_142, u1_struct_0('#skF_2'), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~m1_pre_topc(B_141, '#skF_2') | ~v4_tex_2(B_141, '#skF_2') | v2_struct_0(B_141) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_386, c_435])).
% 3.28/1.50  tff(c_449, plain, (![B_141, C_142]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_141), C_142, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_141))) | ~v3_borsuk_1(C_142, '#skF_2', B_141) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_141)))) | ~v5_pre_topc(C_142, '#skF_2', B_141) | ~v1_funct_2(C_142, u1_struct_0('#skF_2'), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~m1_pre_topc(B_141, '#skF_2') | ~v4_tex_2(B_141, '#skF_2') | v2_struct_0(B_141) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_437])).
% 3.28/1.50  tff(c_578, plain, (![B_160, C_161]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_160), C_161, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_160))) | ~v3_borsuk_1(C_161, '#skF_2', B_160) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_160)))) | ~v5_pre_topc(C_161, '#skF_2', B_160) | ~v1_funct_2(C_161, u1_struct_0('#skF_2'), u1_struct_0(B_160)) | ~v1_funct_1(C_161) | ~m1_pre_topc(B_160, '#skF_2') | ~v4_tex_2(B_160, '#skF_2') | v2_struct_0(B_160))), inference(negUnitSimplification, [status(thm)], [c_58, c_449])).
% 3.28/1.50  tff(c_585, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_578])).
% 3.28/1.50  tff(c_589, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_6'))=k10_relat_1('#skF_4', k1_tarski('#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_36, c_383, c_424, c_585])).
% 3.28/1.50  tff(c_591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_425, c_589])).
% 3.28/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.50  
% 3.28/1.50  Inference rules
% 3.28/1.50  ----------------------
% 3.28/1.50  #Ref     : 0
% 3.28/1.50  #Sup     : 110
% 3.28/1.50  #Fact    : 0
% 3.28/1.50  #Define  : 0
% 3.28/1.50  #Split   : 9
% 3.28/1.50  #Chain   : 0
% 3.28/1.50  #Close   : 0
% 3.28/1.50  
% 3.28/1.50  Ordering : KBO
% 3.28/1.50  
% 3.28/1.50  Simplification rules
% 3.28/1.50  ----------------------
% 3.28/1.50  #Subsume      : 5
% 3.28/1.50  #Demod        : 74
% 3.28/1.50  #Tautology    : 32
% 3.28/1.50  #SimpNegUnit  : 17
% 3.28/1.50  #BackRed      : 2
% 3.28/1.50  
% 3.28/1.50  #Partial instantiations: 0
% 3.28/1.50  #Strategies tried      : 1
% 3.28/1.50  
% 3.28/1.50  Timing (in seconds)
% 3.28/1.50  ----------------------
% 3.28/1.50  Preprocessing        : 0.35
% 3.28/1.50  Parsing              : 0.19
% 3.28/1.50  CNF conversion       : 0.03
% 3.28/1.50  Main loop            : 0.35
% 3.28/1.50  Inferencing          : 0.13
% 3.28/1.50  Reduction            : 0.11
% 3.28/1.50  Demodulation         : 0.08
% 3.28/1.50  BG Simplification    : 0.02
% 3.28/1.50  Subsumption          : 0.06
% 3.28/1.50  Abstraction          : 0.02
% 3.28/1.50  MUC search           : 0.00
% 3.28/1.50  Cooper               : 0.00
% 3.28/1.50  Total                : 0.75
% 3.28/1.50  Index Insertion      : 0.00
% 3.28/1.50  Index Deletion       : 0.00
% 3.28/1.50  Index Matching       : 0.00
% 3.28/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

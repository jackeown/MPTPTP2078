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
% DateTime   : Thu Dec  3 10:30:37 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 292 expanded)
%              Number of leaves         :   42 ( 123 expanded)
%              Depth                    :   12
%              Number of atoms          :  324 (1541 expanded)
%              Number of equality atoms :   21 ( 172 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

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

tff(f_210,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tdlat_3(B)
           => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc18_tex_2)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A) )
           => ( ~ v2_struct_0(B)
              & v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc35_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_171,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_89,plain,(
    ! [B_95,A_96] :
      ( v2_pre_topc(B_95)
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_89])).

tff(c_95,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_92])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_233,plain,(
    ! [B_120,A_121] :
      ( v3_tdlat_3(B_120)
      | ~ v1_tdlat_3(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_236,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_233])).

tff(c_239,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_236])).

tff(c_240,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v1_tdlat_3('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_239])).

tff(c_241,plain,(
    ~ v1_tdlat_3('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_50,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_262,plain,(
    ! [B_124,A_125] :
      ( v1_tdlat_3(B_124)
      | ~ v4_tex_2(B_124,A_125)
      | v2_struct_0(B_124)
      | ~ m1_pre_topc(B_124,A_125)
      | ~ l1_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_265,plain,
    ( v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_262])).

tff(c_268,plain,
    ( v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_265])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_52,c_241,c_268])).

tff(c_271,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_76,plain,(
    ! [B_91,A_92] :
      ( l1_pre_topc(B_91)
      | ~ m1_pre_topc(B_91,A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_82,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_79])).

tff(c_32,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_61,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_96,plain,(
    ! [A_97,B_98] :
      ( k6_domain_1(A_97,B_98) = k1_tarski(B_98)
      | ~ m1_subset_1(B_98,A_97)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_108,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_61,c_96])).

tff(c_217,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_284,plain,(
    ! [A_127] :
      ( m1_subset_1('#skF_1'(A_127),k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v3_tdlat_3(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v1_xboole_0(B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_2))
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_301,plain,(
    ! [A_130] :
      ( v1_xboole_0('#skF_1'(A_130))
      | ~ v1_xboole_0(u1_struct_0(A_130))
      | ~ l1_pre_topc(A_130)
      | ~ v3_tdlat_3(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_284,c_4])).

tff(c_304,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_217,c_301])).

tff(c_307,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_271,c_82,c_304])).

tff(c_308,plain,(
    v1_xboole_0('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_307])).

tff(c_24,plain,(
    ! [A_31] :
      ( v3_tex_2('#skF_1'(A_31),A_31)
      | ~ l1_pre_topc(A_31)
      | ~ v3_tdlat_3(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_26,plain,(
    ! [A_31] :
      ( m1_subset_1('#skF_1'(A_31),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v3_tdlat_3(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_340,plain,(
    ! [B_136,A_137] :
      ( ~ v3_tex_2(B_136,A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ v1_xboole_0(B_136)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_379,plain,(
    ! [A_142] :
      ( ~ v3_tex_2('#skF_1'(A_142),A_142)
      | ~ v1_xboole_0('#skF_1'(A_142))
      | ~ l1_pre_topc(A_142)
      | ~ v3_tdlat_3(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_26,c_340])).

tff(c_397,plain,(
    ! [A_145] :
      ( ~ v1_xboole_0('#skF_1'(A_145))
      | ~ l1_pre_topc(A_145)
      | ~ v3_tdlat_3(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_24,c_379])).

tff(c_400,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_308,c_397])).

tff(c_403,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_271,c_82,c_400])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_403])).

tff(c_406,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_56,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_107,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_96])).

tff(c_109,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_142,plain,(
    ! [A_107] :
      ( m1_subset_1('#skF_1'(A_107),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v3_tdlat_3(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_160,plain,(
    ! [A_110] :
      ( v1_xboole_0('#skF_1'(A_110))
      | ~ v1_xboole_0(u1_struct_0(A_110))
      | ~ l1_pre_topc(A_110)
      | ~ v3_tdlat_3(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_166,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_109,c_160])).

tff(c_173,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_166])).

tff(c_174,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_173])).

tff(c_183,plain,(
    ! [B_114,A_115] :
      ( ~ v3_tex_2(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v1_xboole_0(B_114)
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_193,plain,(
    ! [A_116] :
      ( ~ v3_tex_2('#skF_1'(A_116),A_116)
      | ~ v1_xboole_0('#skF_1'(A_116))
      | ~ l1_pre_topc(A_116)
      | ~ v3_tdlat_3(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_26,c_183])).

tff(c_198,plain,(
    ! [A_117] :
      ( ~ v1_xboole_0('#skF_1'(A_117))
      | ~ l1_pre_topc(A_117)
      | ~ v3_tdlat_3(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_24,c_193])).

tff(c_201,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_174,c_198])).

tff(c_207,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_201])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_207])).

tff(c_210,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_30,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_62,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_212,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_62])).

tff(c_502,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_212])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_42,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_38,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_407,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_412,plain,(
    ! [A_146,B_147] :
      ( m1_subset_1(k6_domain_1(A_146,B_147),k1_zfmisc_1(A_146))
      | ~ m1_subset_1(B_147,A_146)
      | v1_xboole_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_421,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_412])).

tff(c_428,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_421])).

tff(c_429,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_428])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_211,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_424,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_412])).

tff(c_431,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_424])).

tff(c_432,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_431])).

tff(c_597,plain,(
    ! [A_173,B_174,C_175,E_176] :
      ( k8_relset_1(u1_struct_0(A_173),u1_struct_0(B_174),C_175,E_176) = k2_pre_topc(A_173,E_176)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ m1_subset_1(E_176,k1_zfmisc_1(u1_struct_0(B_174)))
      | ~ v3_borsuk_1(C_175,A_173,B_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_173),u1_struct_0(B_174))))
      | ~ v5_pre_topc(C_175,A_173,B_174)
      | ~ v1_funct_2(C_175,u1_struct_0(A_173),u1_struct_0(B_174))
      | ~ v1_funct_1(C_175)
      | ~ m1_pre_topc(B_174,A_173)
      | ~ v4_tex_2(B_174,A_173)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_173)
      | ~ v3_tdlat_3(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_605,plain,(
    ! [B_174,C_175] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_174),C_175,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_174)))
      | ~ v3_borsuk_1(C_175,'#skF_2',B_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_174))))
      | ~ v5_pre_topc(C_175,'#skF_2',B_174)
      | ~ v1_funct_2(C_175,u1_struct_0('#skF_2'),u1_struct_0(B_174))
      | ~ v1_funct_1(C_175)
      | ~ m1_pre_topc(B_174,'#skF_2')
      | ~ v4_tex_2(B_174,'#skF_2')
      | v2_struct_0(B_174)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_432,c_597])).

tff(c_616,plain,(
    ! [B_174,C_175] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_174),C_175,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_174)))
      | ~ v3_borsuk_1(C_175,'#skF_2',B_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_174))))
      | ~ v5_pre_topc(C_175,'#skF_2',B_174)
      | ~ v1_funct_2(C_175,u1_struct_0('#skF_2'),u1_struct_0(B_174))
      | ~ v1_funct_1(C_175)
      | ~ m1_pre_topc(B_174,'#skF_2')
      | ~ v4_tex_2(B_174,'#skF_2')
      | v2_struct_0(B_174)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_605])).

tff(c_783,plain,(
    ! [B_199,C_200] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_199),C_200,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_199)))
      | ~ v3_borsuk_1(C_200,'#skF_2',B_199)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_199))))
      | ~ v5_pre_topc(C_200,'#skF_2',B_199)
      | ~ v1_funct_2(C_200,u1_struct_0('#skF_2'),u1_struct_0(B_199))
      | ~ v1_funct_1(C_200)
      | ~ m1_pre_topc(B_199,'#skF_2')
      | ~ v4_tex_2(B_199,'#skF_2')
      | v2_struct_0(B_199) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_616])).

tff(c_790,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_783])).

tff(c_794,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_38,c_429,c_790])).

tff(c_796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_502,c_794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.61  
% 3.51/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.61  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.51/1.61  
% 3.51/1.61  %Foreground sorts:
% 3.51/1.61  
% 3.51/1.61  
% 3.51/1.61  %Background operators:
% 3.51/1.61  
% 3.51/1.61  
% 3.51/1.61  %Foreground operators:
% 3.51/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.51/1.61  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.51/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.51/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.51/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.51/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.51/1.61  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.51/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.51/1.61  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.51/1.61  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.51/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.51/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.51/1.61  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.51/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.51/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.51/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.61  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.51/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.51/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.61  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.51/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.51/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.51/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.51/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.51/1.61  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.51/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.61  
% 3.96/1.64  tff(f_210, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.96/1.64  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.96/1.64  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v1_tdlat_3(B) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc18_tex_2)).
% 3.96/1.64  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & v4_tex_2(B, A)) => (~v2_struct_0(B) & v1_tdlat_3(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc35_tex_2)).
% 3.96/1.64  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.96/1.64  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.96/1.64  tff(f_133, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 3.96/1.64  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.96/1.64  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 3.96/1.64  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.96/1.64  tff(f_171, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.96/1.64  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_89, plain, (![B_95, A_96]: (v2_pre_topc(B_95) | ~m1_pre_topc(B_95, A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.96/1.64  tff(c_92, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_89])).
% 3.96/1.64  tff(c_95, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_92])).
% 3.96/1.64  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_233, plain, (![B_120, A_121]: (v3_tdlat_3(B_120) | ~v1_tdlat_3(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.96/1.64  tff(c_236, plain, (v3_tdlat_3('#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_233])).
% 3.96/1.64  tff(c_239, plain, (v3_tdlat_3('#skF_3') | ~v1_tdlat_3('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_236])).
% 3.96/1.64  tff(c_240, plain, (v3_tdlat_3('#skF_3') | ~v1_tdlat_3('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_239])).
% 3.96/1.64  tff(c_241, plain, (~v1_tdlat_3('#skF_3')), inference(splitLeft, [status(thm)], [c_240])).
% 3.96/1.64  tff(c_50, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_262, plain, (![B_124, A_125]: (v1_tdlat_3(B_124) | ~v4_tex_2(B_124, A_125) | v2_struct_0(B_124) | ~m1_pre_topc(B_124, A_125) | ~l1_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.96/1.64  tff(c_265, plain, (v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_262])).
% 3.96/1.64  tff(c_268, plain, (v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_265])).
% 3.96/1.64  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_52, c_241, c_268])).
% 3.96/1.64  tff(c_271, plain, (v3_tdlat_3('#skF_3')), inference(splitRight, [status(thm)], [c_240])).
% 3.96/1.64  tff(c_76, plain, (![B_91, A_92]: (l1_pre_topc(B_91) | ~m1_pre_topc(B_91, A_92) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.96/1.64  tff(c_79, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_76])).
% 3.96/1.64  tff(c_82, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_79])).
% 3.96/1.64  tff(c_32, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_61, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 3.96/1.64  tff(c_96, plain, (![A_97, B_98]: (k6_domain_1(A_97, B_98)=k1_tarski(B_98) | ~m1_subset_1(B_98, A_97) | v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.96/1.64  tff(c_108, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_61, c_96])).
% 3.96/1.64  tff(c_217, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_108])).
% 3.96/1.64  tff(c_284, plain, (![A_127]: (m1_subset_1('#skF_1'(A_127), k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v3_tdlat_3(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.96/1.64  tff(c_4, plain, (![B_4, A_2]: (v1_xboole_0(B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_2)) | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.96/1.64  tff(c_301, plain, (![A_130]: (v1_xboole_0('#skF_1'(A_130)) | ~v1_xboole_0(u1_struct_0(A_130)) | ~l1_pre_topc(A_130) | ~v3_tdlat_3(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_284, c_4])).
% 3.96/1.64  tff(c_304, plain, (v1_xboole_0('#skF_1'('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_217, c_301])).
% 3.96/1.64  tff(c_307, plain, (v1_xboole_0('#skF_1'('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_271, c_82, c_304])).
% 3.96/1.64  tff(c_308, plain, (v1_xboole_0('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_307])).
% 3.96/1.64  tff(c_24, plain, (![A_31]: (v3_tex_2('#skF_1'(A_31), A_31) | ~l1_pre_topc(A_31) | ~v3_tdlat_3(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.96/1.64  tff(c_26, plain, (![A_31]: (m1_subset_1('#skF_1'(A_31), k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v3_tdlat_3(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.96/1.64  tff(c_340, plain, (![B_136, A_137]: (~v3_tex_2(B_136, A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~v1_xboole_0(B_136) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.96/1.64  tff(c_379, plain, (![A_142]: (~v3_tex_2('#skF_1'(A_142), A_142) | ~v1_xboole_0('#skF_1'(A_142)) | ~l1_pre_topc(A_142) | ~v3_tdlat_3(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_26, c_340])).
% 3.96/1.64  tff(c_397, plain, (![A_145]: (~v1_xboole_0('#skF_1'(A_145)) | ~l1_pre_topc(A_145) | ~v3_tdlat_3(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(resolution, [status(thm)], [c_24, c_379])).
% 3.96/1.64  tff(c_400, plain, (~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_308, c_397])).
% 3.96/1.64  tff(c_403, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_271, c_82, c_400])).
% 3.96/1.64  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_403])).
% 3.96/1.64  tff(c_406, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_108])).
% 3.96/1.64  tff(c_56, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_34, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_107, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_96])).
% 3.96/1.64  tff(c_109, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_107])).
% 3.96/1.64  tff(c_142, plain, (![A_107]: (m1_subset_1('#skF_1'(A_107), k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~v3_tdlat_3(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.96/1.64  tff(c_160, plain, (![A_110]: (v1_xboole_0('#skF_1'(A_110)) | ~v1_xboole_0(u1_struct_0(A_110)) | ~l1_pre_topc(A_110) | ~v3_tdlat_3(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_142, c_4])).
% 3.96/1.64  tff(c_166, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_109, c_160])).
% 3.96/1.64  tff(c_173, plain, (v1_xboole_0('#skF_1'('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_166])).
% 3.96/1.64  tff(c_174, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_173])).
% 3.96/1.64  tff(c_183, plain, (![B_114, A_115]: (~v3_tex_2(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~v1_xboole_0(B_114) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.96/1.64  tff(c_193, plain, (![A_116]: (~v3_tex_2('#skF_1'(A_116), A_116) | ~v1_xboole_0('#skF_1'(A_116)) | ~l1_pre_topc(A_116) | ~v3_tdlat_3(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_26, c_183])).
% 3.96/1.64  tff(c_198, plain, (![A_117]: (~v1_xboole_0('#skF_1'(A_117)) | ~l1_pre_topc(A_117) | ~v3_tdlat_3(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_24, c_193])).
% 3.96/1.64  tff(c_201, plain, (~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_174, c_198])).
% 3.96/1.64  tff(c_207, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_201])).
% 3.96/1.64  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_207])).
% 3.96/1.64  tff(c_210, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_107])).
% 3.96/1.64  tff(c_30, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_62, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 3.96/1.64  tff(c_212, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_62])).
% 3.96/1.64  tff(c_502, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_212])).
% 3.96/1.64  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_44, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_42, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_38, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_407, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_108])).
% 3.96/1.64  tff(c_412, plain, (![A_146, B_147]: (m1_subset_1(k6_domain_1(A_146, B_147), k1_zfmisc_1(A_146)) | ~m1_subset_1(B_147, A_146) | v1_xboole_0(A_146))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.96/1.64  tff(c_421, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_412])).
% 3.96/1.64  tff(c_428, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_421])).
% 3.96/1.64  tff(c_429, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_407, c_428])).
% 3.96/1.64  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.96/1.64  tff(c_211, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_107])).
% 3.96/1.64  tff(c_424, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_210, c_412])).
% 3.96/1.64  tff(c_431, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_424])).
% 3.96/1.64  tff(c_432, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_211, c_431])).
% 3.96/1.64  tff(c_597, plain, (![A_173, B_174, C_175, E_176]: (k8_relset_1(u1_struct_0(A_173), u1_struct_0(B_174), C_175, E_176)=k2_pre_topc(A_173, E_176) | ~m1_subset_1(E_176, k1_zfmisc_1(u1_struct_0(A_173))) | ~m1_subset_1(E_176, k1_zfmisc_1(u1_struct_0(B_174))) | ~v3_borsuk_1(C_175, A_173, B_174) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_173), u1_struct_0(B_174)))) | ~v5_pre_topc(C_175, A_173, B_174) | ~v1_funct_2(C_175, u1_struct_0(A_173), u1_struct_0(B_174)) | ~v1_funct_1(C_175) | ~m1_pre_topc(B_174, A_173) | ~v4_tex_2(B_174, A_173) | v2_struct_0(B_174) | ~l1_pre_topc(A_173) | ~v3_tdlat_3(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.96/1.64  tff(c_605, plain, (![B_174, C_175]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_174), C_175, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_174))) | ~v3_borsuk_1(C_175, '#skF_2', B_174) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_174)))) | ~v5_pre_topc(C_175, '#skF_2', B_174) | ~v1_funct_2(C_175, u1_struct_0('#skF_2'), u1_struct_0(B_174)) | ~v1_funct_1(C_175) | ~m1_pre_topc(B_174, '#skF_2') | ~v4_tex_2(B_174, '#skF_2') | v2_struct_0(B_174) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_432, c_597])).
% 3.96/1.64  tff(c_616, plain, (![B_174, C_175]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_174), C_175, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_174))) | ~v3_borsuk_1(C_175, '#skF_2', B_174) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_174)))) | ~v5_pre_topc(C_175, '#skF_2', B_174) | ~v1_funct_2(C_175, u1_struct_0('#skF_2'), u1_struct_0(B_174)) | ~v1_funct_1(C_175) | ~m1_pre_topc(B_174, '#skF_2') | ~v4_tex_2(B_174, '#skF_2') | v2_struct_0(B_174) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_605])).
% 3.96/1.64  tff(c_783, plain, (![B_199, C_200]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_199), C_200, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_199))) | ~v3_borsuk_1(C_200, '#skF_2', B_199) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_199)))) | ~v5_pre_topc(C_200, '#skF_2', B_199) | ~v1_funct_2(C_200, u1_struct_0('#skF_2'), u1_struct_0(B_199)) | ~v1_funct_1(C_200) | ~m1_pre_topc(B_199, '#skF_2') | ~v4_tex_2(B_199, '#skF_2') | v2_struct_0(B_199))), inference(negUnitSimplification, [status(thm)], [c_60, c_616])).
% 3.96/1.64  tff(c_790, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_783])).
% 3.96/1.64  tff(c_794, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_38, c_429, c_790])).
% 3.96/1.64  tff(c_796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_502, c_794])).
% 3.96/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.64  
% 3.96/1.64  Inference rules
% 3.96/1.64  ----------------------
% 3.96/1.64  #Ref     : 0
% 3.96/1.64  #Sup     : 143
% 3.96/1.64  #Fact    : 0
% 3.96/1.64  #Define  : 0
% 3.96/1.64  #Split   : 23
% 3.96/1.64  #Chain   : 0
% 3.96/1.64  #Close   : 0
% 3.96/1.64  
% 3.96/1.64  Ordering : KBO
% 3.96/1.64  
% 3.96/1.64  Simplification rules
% 3.96/1.64  ----------------------
% 3.96/1.64  #Subsume      : 16
% 3.96/1.64  #Demod        : 96
% 3.96/1.64  #Tautology    : 29
% 3.96/1.64  #SimpNegUnit  : 31
% 3.96/1.64  #BackRed      : 1
% 3.96/1.64  
% 3.96/1.64  #Partial instantiations: 0
% 3.96/1.64  #Strategies tried      : 1
% 3.96/1.64  
% 3.96/1.64  Timing (in seconds)
% 3.96/1.64  ----------------------
% 3.96/1.64  Preprocessing        : 0.38
% 3.96/1.64  Parsing              : 0.20
% 3.96/1.64  CNF conversion       : 0.03
% 3.96/1.64  Main loop            : 0.42
% 3.96/1.64  Inferencing          : 0.15
% 3.96/1.64  Reduction            : 0.13
% 3.96/1.64  Demodulation         : 0.09
% 3.96/1.64  BG Simplification    : 0.02
% 3.96/1.64  Subsumption          : 0.08
% 3.96/1.64  Abstraction          : 0.02
% 3.96/1.64  MUC search           : 0.00
% 3.96/1.64  Cooper               : 0.00
% 3.96/1.64  Total                : 0.85
% 3.96/1.64  Index Insertion      : 0.00
% 3.96/1.64  Index Deletion       : 0.00
% 3.96/1.64  Index Matching       : 0.00
% 3.96/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------

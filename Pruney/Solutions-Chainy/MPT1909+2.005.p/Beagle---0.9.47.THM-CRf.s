%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:38 EST 2020

% Result     : Theorem 8.87s
% Output     : CNFRefutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 468 expanded)
%              Number of leaves         :   52 ( 193 expanded)
%              Depth                    :   16
%              Number of atoms          :  303 (2500 expanded)
%              Number of equality atoms :   25 ( 288 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_244,negated_conjecture,(
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

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & v3_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc9_tdlat_3)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_205,axiom,(
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

tff(c_80,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_76,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_82,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_204,plain,(
    ! [A_165,B_166] :
      ( k6_domain_1(A_165,B_166) = k1_tarski(B_166)
      | ~ m1_subset_1(B_166,A_165)
      | v1_xboole_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_220,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_204])).

tff(c_2735,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_2739,plain,(
    ! [B_387,A_388] :
      ( m1_subset_1(u1_struct_0(B_387),k1_zfmisc_1(u1_struct_0(A_388)))
      | ~ m1_pre_topc(B_387,A_388)
      | ~ l1_pre_topc(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    ! [B_42,A_40] :
      ( v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_40))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2852,plain,(
    ! [B_400,A_401] :
      ( v1_xboole_0(u1_struct_0(B_400))
      | ~ v1_xboole_0(u1_struct_0(A_401))
      | ~ m1_pre_topc(B_400,A_401)
      | ~ l1_pre_topc(A_401) ) ),
    inference(resolution,[status(thm)],[c_2739,c_28])).

tff(c_2854,plain,(
    ! [B_400] :
      ( v1_xboole_0(u1_struct_0(B_400))
      | ~ m1_pre_topc(B_400,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2735,c_2852])).

tff(c_2858,plain,(
    ! [B_402] :
      ( v1_xboole_0(u1_struct_0(B_402))
      | ~ m1_pre_topc(B_402,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2854])).

tff(c_86,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_189,plain,(
    ! [B_161,A_162] :
      ( v2_pre_topc(B_161)
      | ~ m1_pre_topc(B_161,A_162)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_192,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_189])).

tff(c_195,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_192])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_84,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_2109,plain,(
    ! [B_339,A_340] :
      ( v3_tdlat_3(B_339)
      | v2_struct_0(B_339)
      | ~ m1_pre_topc(B_339,A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v3_tdlat_3(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2112,plain,
    ( v3_tdlat_3('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2109])).

tff(c_2115,plain,
    ( v3_tdlat_3('#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_2112])).

tff(c_2116,plain,(
    v3_tdlat_3('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_80,c_2115])).

tff(c_111,plain,(
    ! [B_136,A_137] :
      ( l1_pre_topc(B_136)
      | ~ m1_pre_topc(B_136,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_114,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_111])).

tff(c_117,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_114])).

tff(c_52,plain,(
    ! [A_71] :
      ( v3_tex_2('#skF_3'(A_71),A_71)
      | ~ l1_pre_topc(A_71)
      | ~ v3_tdlat_3(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_60,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_89,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64])).

tff(c_219,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_89,c_204])).

tff(c_221,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_1990,plain,(
    ! [A_327] :
      ( m1_subset_1('#skF_3'(A_327),k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ l1_pre_topc(A_327)
      | ~ v3_tdlat_3(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2379,plain,(
    ! [A_367] :
      ( v1_xboole_0('#skF_3'(A_367))
      | ~ v1_xboole_0(u1_struct_0(A_367))
      | ~ l1_pre_topc(A_367)
      | ~ v3_tdlat_3(A_367)
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(resolution,[status(thm)],[c_1990,c_28])).

tff(c_2385,plain,
    ( v1_xboole_0('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_221,c_2379])).

tff(c_2389,plain,
    ( v1_xboole_0('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_2116,c_117,c_2385])).

tff(c_2390,plain,(
    v1_xboole_0('#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2389])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_224,plain,(
    ! [A_10] :
      ( u1_struct_0('#skF_5') = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_221,c_12])).

tff(c_2399,plain,(
    u1_struct_0('#skF_5') = '#skF_3'('#skF_5') ),
    inference(resolution,[status(thm)],[c_2390,c_224])).

tff(c_54,plain,(
    ! [A_71] :
      ( m1_subset_1('#skF_3'(A_71),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v3_tdlat_3(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2450,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1('#skF_3'('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2399,c_54])).

tff(c_2481,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1('#skF_3'('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_2116,c_117,c_2450])).

tff(c_2482,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1('#skF_3'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2481])).

tff(c_2520,plain,(
    ! [B_369,A_370] :
      ( ~ v3_tex_2(B_369,A_370)
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ v1_xboole_0(B_369)
      | ~ l1_pre_topc(A_370)
      | ~ v2_pre_topc(A_370)
      | v2_struct_0(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2523,plain,(
    ! [B_369] :
      ( ~ v3_tex_2(B_369,'#skF_5')
      | ~ m1_subset_1(B_369,k1_zfmisc_1('#skF_3'('#skF_5')))
      | ~ v1_xboole_0(B_369)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2399,c_2520])).

tff(c_2539,plain,(
    ! [B_369] :
      ( ~ v3_tex_2(B_369,'#skF_5')
      | ~ m1_subset_1(B_369,k1_zfmisc_1('#skF_3'('#skF_5')))
      | ~ v1_xboole_0(B_369)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_117,c_2523])).

tff(c_2702,plain,(
    ! [B_386] :
      ( ~ v3_tex_2(B_386,'#skF_5')
      | ~ m1_subset_1(B_386,k1_zfmisc_1('#skF_3'('#skF_5')))
      | ~ v1_xboole_0(B_386) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2539])).

tff(c_2705,plain,
    ( ~ v3_tex_2('#skF_3'('#skF_5'),'#skF_5')
    | ~ v1_xboole_0('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2482,c_2702])).

tff(c_2716,plain,(
    ~ v3_tex_2('#skF_3'('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2390,c_2705])).

tff(c_2722,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2716])).

tff(c_2725,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_2116,c_117,c_2722])).

tff(c_2727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2725])).

tff(c_2729,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_2866,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2858,c_2729])).

tff(c_2874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2866])).

tff(c_2875,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_2728,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_58,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_90,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58])).

tff(c_2730,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2728,c_90])).

tff(c_3028,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) != k2_pre_topc('#skF_4',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_2730])).

tff(c_78,plain,(
    v4_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_72,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_70,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_66,plain,(
    v3_borsuk_1('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_2899,plain,(
    ! [A_407,B_408] :
      ( m1_subset_1(k6_domain_1(A_407,B_408),k1_zfmisc_1(A_407))
      | ~ m1_subset_1(B_408,A_407)
      | v1_xboole_0(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2914,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2728,c_2899])).

tff(c_2922,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2914])).

tff(c_2923,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2729,c_2922])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_2876,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_2911,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2875,c_2899])).

tff(c_2919,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2911])).

tff(c_2920,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2876,c_2919])).

tff(c_13174,plain,(
    ! [A_1019,B_1020,C_1021,E_1022] :
      ( k8_relset_1(u1_struct_0(A_1019),u1_struct_0(B_1020),C_1021,E_1022) = k2_pre_topc(A_1019,E_1022)
      | ~ m1_subset_1(E_1022,k1_zfmisc_1(u1_struct_0(A_1019)))
      | ~ m1_subset_1(E_1022,k1_zfmisc_1(u1_struct_0(B_1020)))
      | ~ v3_borsuk_1(C_1021,A_1019,B_1020)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1019),u1_struct_0(B_1020))))
      | ~ v5_pre_topc(C_1021,A_1019,B_1020)
      | ~ v1_funct_2(C_1021,u1_struct_0(A_1019),u1_struct_0(B_1020))
      | ~ v1_funct_1(C_1021)
      | ~ m1_pre_topc(B_1020,A_1019)
      | ~ v4_tex_2(B_1020,A_1019)
      | v2_struct_0(B_1020)
      | ~ l1_pre_topc(A_1019)
      | ~ v3_tdlat_3(A_1019)
      | ~ v2_pre_topc(A_1019)
      | v2_struct_0(A_1019) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_13192,plain,(
    ! [B_1020,C_1021] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_1020),C_1021,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_1020)))
      | ~ v3_borsuk_1(C_1021,'#skF_4',B_1020)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1020))))
      | ~ v5_pre_topc(C_1021,'#skF_4',B_1020)
      | ~ v1_funct_2(C_1021,u1_struct_0('#skF_4'),u1_struct_0(B_1020))
      | ~ v1_funct_1(C_1021)
      | ~ m1_pre_topc(B_1020,'#skF_4')
      | ~ v4_tex_2(B_1020,'#skF_4')
      | v2_struct_0(B_1020)
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2920,c_13174])).

tff(c_13215,plain,(
    ! [B_1020,C_1021] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_1020),C_1021,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_1020)))
      | ~ v3_borsuk_1(C_1021,'#skF_4',B_1020)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1020))))
      | ~ v5_pre_topc(C_1021,'#skF_4',B_1020)
      | ~ v1_funct_2(C_1021,u1_struct_0('#skF_4'),u1_struct_0(B_1020))
      | ~ v1_funct_1(C_1021)
      | ~ m1_pre_topc(B_1020,'#skF_4')
      | ~ v4_tex_2(B_1020,'#skF_4')
      | v2_struct_0(B_1020)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_13192])).

tff(c_13329,plain,(
    ! [B_1026,C_1027] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_1026),C_1027,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_1026)))
      | ~ v3_borsuk_1(C_1027,'#skF_4',B_1026)
      | ~ m1_subset_1(C_1027,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1026))))
      | ~ v5_pre_topc(C_1027,'#skF_4',B_1026)
      | ~ v1_funct_2(C_1027,u1_struct_0('#skF_4'),u1_struct_0(B_1026))
      | ~ v1_funct_1(C_1027)
      | ~ m1_pre_topc(B_1026,'#skF_4')
      | ~ v4_tex_2(B_1026,'#skF_4')
      | v2_struct_0(B_1026) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_13215])).

tff(c_13348,plain,
    ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
    | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v3_borsuk_1('#skF_6','#skF_4','#skF_5')
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v4_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_13329])).

tff(c_13359,plain,
    ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_66,c_2923,c_13348])).

tff(c_13361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3028,c_13359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.87/3.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/3.40  
% 8.87/3.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/3.40  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_2
% 8.87/3.40  
% 8.87/3.40  %Foreground sorts:
% 8.87/3.40  
% 8.87/3.40  
% 8.87/3.40  %Background operators:
% 8.87/3.40  
% 8.87/3.40  
% 8.87/3.40  %Foreground operators:
% 8.87/3.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.87/3.40  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 8.87/3.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.87/3.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.87/3.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.87/3.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.87/3.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 8.87/3.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.87/3.40  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 8.87/3.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.87/3.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.87/3.40  tff('#skF_7', type, '#skF_7': $i).
% 8.87/3.40  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.87/3.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.87/3.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.87/3.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.87/3.40  tff('#skF_5', type, '#skF_5': $i).
% 8.87/3.40  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 8.87/3.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.87/3.40  tff('#skF_6', type, '#skF_6': $i).
% 8.87/3.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.87/3.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.87/3.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.87/3.40  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 8.87/3.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.87/3.40  tff('#skF_8', type, '#skF_8': $i).
% 8.87/3.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.87/3.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.87/3.40  tff('#skF_4', type, '#skF_4': $i).
% 8.87/3.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.87/3.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.87/3.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.87/3.40  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 8.87/3.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.87/3.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.87/3.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.87/3.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.87/3.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.87/3.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.87/3.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.87/3.40  
% 8.87/3.42  tff(f_244, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 8.87/3.42  tff(f_111, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 8.87/3.42  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 8.87/3.42  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.87/3.42  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 8.87/3.42  tff(f_138, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & v3_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc9_tdlat_3)).
% 8.87/3.42  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.87/3.42  tff(f_167, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 8.87/3.42  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 8.87/3.42  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 8.87/3.42  tff(f_104, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 8.87/3.42  tff(f_205, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 8.87/3.42  tff(c_80, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_76, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_82, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_62, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_204, plain, (![A_165, B_166]: (k6_domain_1(A_165, B_166)=k1_tarski(B_166) | ~m1_subset_1(B_166, A_165) | v1_xboole_0(A_165))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.87/3.42  tff(c_220, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_204])).
% 8.87/3.42  tff(c_2735, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_220])).
% 8.87/3.42  tff(c_2739, plain, (![B_387, A_388]: (m1_subset_1(u1_struct_0(B_387), k1_zfmisc_1(u1_struct_0(A_388))) | ~m1_pre_topc(B_387, A_388) | ~l1_pre_topc(A_388))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.87/3.42  tff(c_28, plain, (![B_42, A_40]: (v1_xboole_0(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_40)) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.87/3.42  tff(c_2852, plain, (![B_400, A_401]: (v1_xboole_0(u1_struct_0(B_400)) | ~v1_xboole_0(u1_struct_0(A_401)) | ~m1_pre_topc(B_400, A_401) | ~l1_pre_topc(A_401))), inference(resolution, [status(thm)], [c_2739, c_28])).
% 8.87/3.42  tff(c_2854, plain, (![B_400]: (v1_xboole_0(u1_struct_0(B_400)) | ~m1_pre_topc(B_400, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_2735, c_2852])).
% 8.87/3.42  tff(c_2858, plain, (![B_402]: (v1_xboole_0(u1_struct_0(B_402)) | ~m1_pre_topc(B_402, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2854])).
% 8.87/3.42  tff(c_86, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_189, plain, (![B_161, A_162]: (v2_pre_topc(B_161) | ~m1_pre_topc(B_161, A_162) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.87/3.42  tff(c_192, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_189])).
% 8.87/3.42  tff(c_195, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_192])).
% 8.87/3.42  tff(c_88, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_84, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_2109, plain, (![B_339, A_340]: (v3_tdlat_3(B_339) | v2_struct_0(B_339) | ~m1_pre_topc(B_339, A_340) | ~l1_pre_topc(A_340) | ~v3_tdlat_3(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.87/3.42  tff(c_2112, plain, (v3_tdlat_3('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2109])).
% 8.87/3.42  tff(c_2115, plain, (v3_tdlat_3('#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_2112])).
% 8.87/3.42  tff(c_2116, plain, (v3_tdlat_3('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_88, c_80, c_2115])).
% 8.87/3.42  tff(c_111, plain, (![B_136, A_137]: (l1_pre_topc(B_136) | ~m1_pre_topc(B_136, A_137) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.87/3.42  tff(c_114, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_111])).
% 8.87/3.42  tff(c_117, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_114])).
% 8.87/3.42  tff(c_52, plain, (![A_71]: (v3_tex_2('#skF_3'(A_71), A_71) | ~l1_pre_topc(A_71) | ~v3_tdlat_3(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.87/3.42  tff(c_60, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_64, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_89, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64])).
% 8.87/3.42  tff(c_219, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_89, c_204])).
% 8.87/3.42  tff(c_221, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_219])).
% 8.87/3.42  tff(c_1990, plain, (![A_327]: (m1_subset_1('#skF_3'(A_327), k1_zfmisc_1(u1_struct_0(A_327))) | ~l1_pre_topc(A_327) | ~v3_tdlat_3(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.87/3.42  tff(c_2379, plain, (![A_367]: (v1_xboole_0('#skF_3'(A_367)) | ~v1_xboole_0(u1_struct_0(A_367)) | ~l1_pre_topc(A_367) | ~v3_tdlat_3(A_367) | ~v2_pre_topc(A_367) | v2_struct_0(A_367))), inference(resolution, [status(thm)], [c_1990, c_28])).
% 8.87/3.42  tff(c_2385, plain, (v1_xboole_0('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_221, c_2379])).
% 8.87/3.42  tff(c_2389, plain, (v1_xboole_0('#skF_3'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_2116, c_117, c_2385])).
% 8.87/3.42  tff(c_2390, plain, (v1_xboole_0('#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_2389])).
% 8.87/3.42  tff(c_12, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | B_11=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.87/3.42  tff(c_224, plain, (![A_10]: (u1_struct_0('#skF_5')=A_10 | ~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_221, c_12])).
% 8.87/3.42  tff(c_2399, plain, (u1_struct_0('#skF_5')='#skF_3'('#skF_5')), inference(resolution, [status(thm)], [c_2390, c_224])).
% 8.87/3.42  tff(c_54, plain, (![A_71]: (m1_subset_1('#skF_3'(A_71), k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v3_tdlat_3(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.87/3.42  tff(c_2450, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1('#skF_3'('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2399, c_54])).
% 8.87/3.42  tff(c_2481, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1('#skF_3'('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_2116, c_117, c_2450])).
% 8.87/3.42  tff(c_2482, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1('#skF_3'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_80, c_2481])).
% 8.87/3.42  tff(c_2520, plain, (![B_369, A_370]: (~v3_tex_2(B_369, A_370) | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0(A_370))) | ~v1_xboole_0(B_369) | ~l1_pre_topc(A_370) | ~v2_pre_topc(A_370) | v2_struct_0(A_370))), inference(cnfTransformation, [status(thm)], [f_153])).
% 8.87/3.42  tff(c_2523, plain, (![B_369]: (~v3_tex_2(B_369, '#skF_5') | ~m1_subset_1(B_369, k1_zfmisc_1('#skF_3'('#skF_5'))) | ~v1_xboole_0(B_369) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2399, c_2520])).
% 8.87/3.42  tff(c_2539, plain, (![B_369]: (~v3_tex_2(B_369, '#skF_5') | ~m1_subset_1(B_369, k1_zfmisc_1('#skF_3'('#skF_5'))) | ~v1_xboole_0(B_369) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_117, c_2523])).
% 8.87/3.42  tff(c_2702, plain, (![B_386]: (~v3_tex_2(B_386, '#skF_5') | ~m1_subset_1(B_386, k1_zfmisc_1('#skF_3'('#skF_5'))) | ~v1_xboole_0(B_386))), inference(negUnitSimplification, [status(thm)], [c_80, c_2539])).
% 8.87/3.42  tff(c_2705, plain, (~v3_tex_2('#skF_3'('#skF_5'), '#skF_5') | ~v1_xboole_0('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_2482, c_2702])).
% 8.87/3.42  tff(c_2716, plain, (~v3_tex_2('#skF_3'('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2390, c_2705])).
% 8.87/3.42  tff(c_2722, plain, (~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_2716])).
% 8.87/3.42  tff(c_2725, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_2116, c_117, c_2722])).
% 8.87/3.42  tff(c_2727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2725])).
% 8.87/3.42  tff(c_2729, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_219])).
% 8.87/3.42  tff(c_2866, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2858, c_2729])).
% 8.87/3.42  tff(c_2874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2866])).
% 8.87/3.42  tff(c_2875, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_220])).
% 8.87/3.42  tff(c_2728, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_219])).
% 8.87/3.42  tff(c_58, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_90, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58])).
% 8.87/3.42  tff(c_2730, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2728, c_90])).
% 8.87/3.42  tff(c_3028, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))!=k2_pre_topc('#skF_4', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2875, c_2730])).
% 8.87/3.42  tff(c_78, plain, (v4_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_72, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_70, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_66, plain, (v3_borsuk_1('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_2899, plain, (![A_407, B_408]: (m1_subset_1(k6_domain_1(A_407, B_408), k1_zfmisc_1(A_407)) | ~m1_subset_1(B_408, A_407) | v1_xboole_0(A_407))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.87/3.42  tff(c_2914, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2728, c_2899])).
% 8.87/3.42  tff(c_2922, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_2914])).
% 8.87/3.42  tff(c_2923, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2729, c_2922])).
% 8.87/3.42  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.87/3.42  tff(c_2876, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_220])).
% 8.87/3.42  tff(c_2911, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2875, c_2899])).
% 8.87/3.42  tff(c_2919, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2911])).
% 8.87/3.42  tff(c_2920, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_2876, c_2919])).
% 8.87/3.42  tff(c_13174, plain, (![A_1019, B_1020, C_1021, E_1022]: (k8_relset_1(u1_struct_0(A_1019), u1_struct_0(B_1020), C_1021, E_1022)=k2_pre_topc(A_1019, E_1022) | ~m1_subset_1(E_1022, k1_zfmisc_1(u1_struct_0(A_1019))) | ~m1_subset_1(E_1022, k1_zfmisc_1(u1_struct_0(B_1020))) | ~v3_borsuk_1(C_1021, A_1019, B_1020) | ~m1_subset_1(C_1021, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1019), u1_struct_0(B_1020)))) | ~v5_pre_topc(C_1021, A_1019, B_1020) | ~v1_funct_2(C_1021, u1_struct_0(A_1019), u1_struct_0(B_1020)) | ~v1_funct_1(C_1021) | ~m1_pre_topc(B_1020, A_1019) | ~v4_tex_2(B_1020, A_1019) | v2_struct_0(B_1020) | ~l1_pre_topc(A_1019) | ~v3_tdlat_3(A_1019) | ~v2_pre_topc(A_1019) | v2_struct_0(A_1019))), inference(cnfTransformation, [status(thm)], [f_205])).
% 8.87/3.42  tff(c_13192, plain, (![B_1020, C_1021]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_1020), C_1021, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_1020))) | ~v3_borsuk_1(C_1021, '#skF_4', B_1020) | ~m1_subset_1(C_1021, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1020)))) | ~v5_pre_topc(C_1021, '#skF_4', B_1020) | ~v1_funct_2(C_1021, u1_struct_0('#skF_4'), u1_struct_0(B_1020)) | ~v1_funct_1(C_1021) | ~m1_pre_topc(B_1020, '#skF_4') | ~v4_tex_2(B_1020, '#skF_4') | v2_struct_0(B_1020) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2920, c_13174])).
% 8.87/3.42  tff(c_13215, plain, (![B_1020, C_1021]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_1020), C_1021, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_1020))) | ~v3_borsuk_1(C_1021, '#skF_4', B_1020) | ~m1_subset_1(C_1021, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1020)))) | ~v5_pre_topc(C_1021, '#skF_4', B_1020) | ~v1_funct_2(C_1021, u1_struct_0('#skF_4'), u1_struct_0(B_1020)) | ~v1_funct_1(C_1021) | ~m1_pre_topc(B_1020, '#skF_4') | ~v4_tex_2(B_1020, '#skF_4') | v2_struct_0(B_1020) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_13192])).
% 8.87/3.42  tff(c_13329, plain, (![B_1026, C_1027]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_1026), C_1027, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_1026))) | ~v3_borsuk_1(C_1027, '#skF_4', B_1026) | ~m1_subset_1(C_1027, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1026)))) | ~v5_pre_topc(C_1027, '#skF_4', B_1026) | ~v1_funct_2(C_1027, u1_struct_0('#skF_4'), u1_struct_0(B_1026)) | ~v1_funct_1(C_1027) | ~m1_pre_topc(B_1026, '#skF_4') | ~v4_tex_2(B_1026, '#skF_4') | v2_struct_0(B_1026))), inference(negUnitSimplification, [status(thm)], [c_88, c_13215])).
% 8.87/3.42  tff(c_13348, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_borsuk_1('#skF_6', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | ~v4_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_13329])).
% 8.87/3.42  tff(c_13359, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_66, c_2923, c_13348])).
% 8.87/3.42  tff(c_13361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_3028, c_13359])).
% 8.87/3.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/3.42  
% 8.87/3.42  Inference rules
% 8.87/3.42  ----------------------
% 8.87/3.42  #Ref     : 0
% 8.87/3.42  #Sup     : 2998
% 8.87/3.42  #Fact    : 0
% 8.87/3.42  #Define  : 0
% 8.87/3.42  #Split   : 63
% 8.87/3.42  #Chain   : 0
% 8.87/3.42  #Close   : 0
% 8.87/3.42  
% 8.87/3.42  Ordering : KBO
% 8.87/3.42  
% 8.87/3.42  Simplification rules
% 8.87/3.42  ----------------------
% 8.87/3.42  #Subsume      : 1060
% 8.87/3.42  #Demod        : 1275
% 8.87/3.42  #Tautology    : 623
% 8.87/3.42  #SimpNegUnit  : 485
% 8.87/3.42  #BackRed      : 131
% 8.87/3.42  
% 8.87/3.42  #Partial instantiations: 0
% 8.87/3.42  #Strategies tried      : 1
% 8.87/3.42  
% 8.87/3.42  Timing (in seconds)
% 8.87/3.42  ----------------------
% 8.87/3.42  Preprocessing        : 0.44
% 8.87/3.42  Parsing              : 0.25
% 8.87/3.42  CNF conversion       : 0.04
% 8.87/3.42  Main loop            : 2.13
% 8.87/3.42  Inferencing          : 0.67
% 8.87/3.42  Reduction            : 0.75
% 8.87/3.42  Demodulation         : 0.53
% 8.87/3.42  BG Simplification    : 0.07
% 8.87/3.42  Subsumption          : 0.49
% 8.87/3.42  Abstraction          : 0.09
% 8.87/3.42  MUC search           : 0.00
% 8.87/3.42  Cooper               : 0.00
% 8.87/3.42  Total                : 2.62
% 8.87/3.42  Index Insertion      : 0.00
% 8.87/3.42  Index Deletion       : 0.00
% 8.87/3.42  Index Matching       : 0.00
% 8.87/3.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

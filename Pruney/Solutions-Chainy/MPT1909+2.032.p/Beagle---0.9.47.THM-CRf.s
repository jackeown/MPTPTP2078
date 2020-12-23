%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:42 EST 2020

% Result     : Theorem 5.23s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 923 expanded)
%              Number of leaves         :   44 ( 340 expanded)
%              Depth                    :   15
%              Number of atoms          :  348 (5114 expanded)
%              Number of equality atoms :   43 ( 628 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_204,negated_conjecture,(
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

tff(f_127,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_113,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_165,axiom,(
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

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_38,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_67,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_225,plain,(
    ! [A_121,B_122] :
      ( m1_pre_topc(k1_tex_2(A_121,B_122),A_121)
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l1_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_227,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_67,c_225])).

tff(c_232,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_227])).

tff(c_233,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_232])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_54,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_94,plain,(
    ! [B_105,A_106] :
      ( l1_pre_topc(B_105)
      | ~ m1_pre_topc(B_105,A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_94])).

tff(c_100,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_97])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_188,plain,(
    ! [A_113,B_114] :
      ( ~ v2_struct_0(k1_tex_2(A_113,B_114))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_194,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_188])).

tff(c_201,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_194])).

tff(c_202,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_201])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_173,plain,(
    ! [A_111,B_112] :
      ( v1_pre_topc(k1_tex_2(A_111,B_112))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_179,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_173])).

tff(c_186,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_179])).

tff(c_187,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_186])).

tff(c_229,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_225])).

tff(c_236,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_229])).

tff(c_237,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_236])).

tff(c_22,plain,(
    ! [C_31,A_25,B_29] :
      ( m1_pre_topc(C_31,A_25)
      | ~ m1_pre_topc(C_31,B_29)
      | ~ m1_pre_topc(B_29,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_257,plain,(
    ! [A_25] :
      ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),A_25)
      | ~ m1_pre_topc('#skF_2',A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_237,c_22])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_107,B_108] :
      ( k6_domain_1(A_107,B_108) = k1_tarski(B_108)
      | ~ m1_subset_1(B_108,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_116,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_67,c_101])).

tff(c_118,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_12,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_136,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_118,c_12])).

tff(c_139,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_136])).

tff(c_142,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_139])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_142])).

tff(c_147,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_433,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_tex_2(A_152,B_153) = C_154
      | u1_struct_0(C_154) != k6_domain_1(u1_struct_0(A_152),B_153)
      | ~ m1_pre_topc(C_154,A_152)
      | ~ v1_pre_topc(C_154)
      | v2_struct_0(C_154)
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_437,plain,(
    ! [C_154] :
      ( k1_tex_2('#skF_1','#skF_4') = C_154
      | u1_struct_0(C_154) != k1_tarski('#skF_4')
      | ~ m1_pre_topc(C_154,'#skF_1')
      | ~ v1_pre_topc(C_154)
      | v2_struct_0(C_154)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_433])).

tff(c_442,plain,(
    ! [C_154] :
      ( k1_tex_2('#skF_1','#skF_4') = C_154
      | u1_struct_0(C_154) != k1_tarski('#skF_4')
      | ~ m1_pre_topc(C_154,'#skF_1')
      | ~ v1_pre_topc(C_154)
      | v2_struct_0(C_154)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_67,c_437])).

tff(c_477,plain,(
    ! [C_156] :
      ( k1_tex_2('#skF_1','#skF_4') = C_156
      | u1_struct_0(C_156) != k1_tarski('#skF_4')
      | ~ m1_pre_topc(C_156,'#skF_1')
      | ~ v1_pre_topc(C_156)
      | v2_struct_0(C_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_442])).

tff(c_485,plain,
    ( k1_tex_2('#skF_2','#skF_4') = k1_tex_2('#skF_1','#skF_4')
    | u1_struct_0(k1_tex_2('#skF_2','#skF_4')) != k1_tarski('#skF_4')
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_257,c_477])).

tff(c_503,plain,
    ( k1_tex_2('#skF_2','#skF_4') = k1_tex_2('#skF_1','#skF_4')
    | u1_struct_0(k1_tex_2('#skF_2','#skF_4')) != k1_tarski('#skF_4')
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_54,c_187,c_485])).

tff(c_504,plain,
    ( k1_tex_2('#skF_2','#skF_4') = k1_tex_2('#skF_1','#skF_4')
    | u1_struct_0(k1_tex_2('#skF_2','#skF_4')) != k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_503])).

tff(c_519,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_4')) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_117,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_149,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_152,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_149,c_12])).

tff(c_155,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_152])).

tff(c_158,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_155])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_158])).

tff(c_163,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_551,plain,(
    ! [A_159,B_160] :
      ( k6_domain_1(u1_struct_0(A_159),B_160) = u1_struct_0(k1_tex_2(A_159,B_160))
      | ~ m1_pre_topc(k1_tex_2(A_159,B_160),A_159)
      | ~ v1_pre_topc(k1_tex_2(A_159,B_160))
      | v2_struct_0(k1_tex_2(A_159,B_160))
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l1_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_559,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_237,c_551])).

tff(c_572,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4')
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_42,c_187,c_163,c_559])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_202,c_519,c_572])).

tff(c_575,plain,(
    k1_tex_2('#skF_2','#skF_4') = k1_tex_2('#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_581,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_237])).

tff(c_576,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_609,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_576])).

tff(c_336,plain,(
    ! [B_142,C_143,A_144] :
      ( r1_tarski(u1_struct_0(B_142),u1_struct_0(C_143))
      | ~ m1_pre_topc(B_142,C_143)
      | ~ m1_pre_topc(C_143,A_144)
      | ~ m1_pre_topc(B_142,A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_348,plain,(
    ! [B_142] :
      ( r1_tarski(u1_struct_0(B_142),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_142,'#skF_2')
      | ~ m1_pre_topc(B_142,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_336])).

tff(c_360,plain,(
    ! [B_142] :
      ( r1_tarski(u1_struct_0(B_142),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_142,'#skF_2')
      | ~ m1_pre_topc(B_142,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_348])).

tff(c_632,plain,
    ( r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_360])).

tff(c_669,plain,(
    r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_581,c_632])).

tff(c_361,plain,(
    ! [B_145] :
      ( r1_tarski(u1_struct_0(B_145),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_145,'#skF_2')
      | ~ m1_pre_topc(B_145,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_348])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_238,plain,(
    ! [C_123,A_124,B_125] :
      ( m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(B_125)))
      | ~ m1_pre_topc(B_125,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_280,plain,(
    ! [A_128,A_129,B_130] :
      ( m1_subset_1(A_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_pre_topc(B_130,A_129)
      | ~ l1_pre_topc(A_129)
      | ~ r1_tarski(A_128,u1_struct_0(B_130)) ) ),
    inference(resolution,[status(thm)],[c_6,c_238])).

tff(c_292,plain,(
    ! [A_128] :
      ( m1_subset_1(A_128,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_128,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_280])).

tff(c_305,plain,(
    ! [A_131] :
      ( m1_subset_1(A_131,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_131,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_292])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,B_3)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_316,plain,(
    ! [A_131] :
      ( r1_tarski(A_131,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_131,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_305,c_4])).

tff(c_370,plain,(
    ! [B_145] :
      ( r1_tarski(u1_struct_0(B_145),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_145,'#skF_2')
      | ~ m1_pre_topc(B_145,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_361,c_316])).

tff(c_629,plain,
    ( r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_1'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_370])).

tff(c_667,plain,(
    r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_581,c_629])).

tff(c_62,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_56,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_48,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_44,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_760,plain,(
    ! [A_168,B_169,C_170,E_171] :
      ( k8_relset_1(u1_struct_0(A_168),u1_struct_0(B_169),C_170,E_171) = k2_pre_topc(A_168,E_171)
      | ~ m1_subset_1(E_171,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ m1_subset_1(E_171,k1_zfmisc_1(u1_struct_0(B_169)))
      | ~ v3_borsuk_1(C_170,A_168,B_169)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168),u1_struct_0(B_169))))
      | ~ v5_pre_topc(C_170,A_168,B_169)
      | ~ v1_funct_2(C_170,u1_struct_0(A_168),u1_struct_0(B_169))
      | ~ v1_funct_1(C_170)
      | ~ m1_pre_topc(B_169,A_168)
      | ~ v4_tex_2(B_169,A_168)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc(A_168)
      | ~ v3_tdlat_3(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_895,plain,(
    ! [A_179,B_180,C_181,A_182] :
      ( k8_relset_1(u1_struct_0(A_179),u1_struct_0(B_180),C_181,A_182) = k2_pre_topc(A_179,A_182)
      | ~ m1_subset_1(A_182,k1_zfmisc_1(u1_struct_0(B_180)))
      | ~ v3_borsuk_1(C_181,A_179,B_180)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_179),u1_struct_0(B_180))))
      | ~ v5_pre_topc(C_181,A_179,B_180)
      | ~ v1_funct_2(C_181,u1_struct_0(A_179),u1_struct_0(B_180))
      | ~ v1_funct_1(C_181)
      | ~ m1_pre_topc(B_180,A_179)
      | ~ v4_tex_2(B_180,A_179)
      | v2_struct_0(B_180)
      | ~ l1_pre_topc(A_179)
      | ~ v3_tdlat_3(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179)
      | ~ r1_tarski(A_182,u1_struct_0(A_179)) ) ),
    inference(resolution,[status(thm)],[c_6,c_760])).

tff(c_1329,plain,(
    ! [A_214,B_215,C_216,A_217] :
      ( k8_relset_1(u1_struct_0(A_214),u1_struct_0(B_215),C_216,A_217) = k2_pre_topc(A_214,A_217)
      | ~ v3_borsuk_1(C_216,A_214,B_215)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214),u1_struct_0(B_215))))
      | ~ v5_pre_topc(C_216,A_214,B_215)
      | ~ v1_funct_2(C_216,u1_struct_0(A_214),u1_struct_0(B_215))
      | ~ v1_funct_1(C_216)
      | ~ m1_pre_topc(B_215,A_214)
      | ~ v4_tex_2(B_215,A_214)
      | v2_struct_0(B_215)
      | ~ l1_pre_topc(A_214)
      | ~ v3_tdlat_3(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214)
      | ~ r1_tarski(A_217,u1_struct_0(A_214))
      | ~ r1_tarski(A_217,u1_struct_0(B_215)) ) ),
    inference(resolution,[status(thm)],[c_6,c_895])).

tff(c_1335,plain,(
    ! [A_217] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',A_217) = k2_pre_topc('#skF_1',A_217)
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
      | ~ r1_tarski(A_217,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_217,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_46,c_1329])).

tff(c_1346,plain,(
    ! [A_217] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',A_217) = k2_pre_topc('#skF_1',A_217)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_217,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_217,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_56,c_54,c_52,c_50,c_48,c_44,c_1335])).

tff(c_1350,plain,(
    ! [A_218] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',A_218) = k2_pre_topc('#skF_1',A_218)
      | ~ r1_tarski(A_218,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_218,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_1346])).

tff(c_36,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_68,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_261,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_147,c_68])).

tff(c_1359,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_1'))
    | ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_261])).

tff(c_1371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_667,c_1359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.23/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.18  
% 5.23/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.18  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.23/2.18  
% 5.23/2.18  %Foreground sorts:
% 5.23/2.18  
% 5.23/2.18  
% 5.23/2.18  %Background operators:
% 5.23/2.18  
% 5.23/2.18  
% 5.23/2.18  %Foreground operators:
% 5.23/2.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.23/2.18  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 5.23/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.23/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.23/2.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.23/2.18  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 5.23/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.23/2.18  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.23/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.23/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.23/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.23/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.23/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.23/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.23/2.18  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.23/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.23/2.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.23/2.18  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 5.23/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.23/2.18  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 5.23/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.23/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/2.18  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.23/2.18  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.23/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.23/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.23/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.23/2.18  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.23/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.23/2.18  
% 5.23/2.20  tff(f_204, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 5.23/2.20  tff(f_127, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 5.23/2.20  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.23/2.20  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 5.23/2.20  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.23/2.20  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.23/2.20  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.23/2.20  tff(f_113, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 5.23/2.21  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 5.23/2.21  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.23/2.21  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 5.23/2.21  tff(f_165, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 5.23/2.21  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_38, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_67, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 5.23/2.21  tff(c_225, plain, (![A_121, B_122]: (m1_pre_topc(k1_tex_2(A_121, B_122), A_121) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l1_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/2.21  tff(c_227, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_67, c_225])).
% 5.23/2.21  tff(c_232, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_227])).
% 5.23/2.21  tff(c_233, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_232])).
% 5.23/2.21  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_54, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_94, plain, (![B_105, A_106]: (l1_pre_topc(B_105) | ~m1_pre_topc(B_105, A_106) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.23/2.21  tff(c_97, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_94])).
% 5.23/2.21  tff(c_100, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_97])).
% 5.23/2.21  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_188, plain, (![A_113, B_114]: (~v2_struct_0(k1_tex_2(A_113, B_114)) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/2.21  tff(c_194, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_188])).
% 5.23/2.21  tff(c_201, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_194])).
% 5.23/2.21  tff(c_202, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_201])).
% 5.23/2.21  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_173, plain, (![A_111, B_112]: (v1_pre_topc(k1_tex_2(A_111, B_112)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/2.21  tff(c_179, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_173])).
% 5.23/2.21  tff(c_186, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_179])).
% 5.23/2.21  tff(c_187, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_186])).
% 5.23/2.21  tff(c_229, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_225])).
% 5.23/2.21  tff(c_236, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_229])).
% 5.23/2.21  tff(c_237, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_236])).
% 5.23/2.21  tff(c_22, plain, (![C_31, A_25, B_29]: (m1_pre_topc(C_31, A_25) | ~m1_pre_topc(C_31, B_29) | ~m1_pre_topc(B_29, A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.23/2.21  tff(c_257, plain, (![A_25]: (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), A_25) | ~m1_pre_topc('#skF_2', A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(resolution, [status(thm)], [c_237, c_22])).
% 5.23/2.21  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.23/2.21  tff(c_101, plain, (![A_107, B_108]: (k6_domain_1(A_107, B_108)=k1_tarski(B_108) | ~m1_subset_1(B_108, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.23/2.21  tff(c_116, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_67, c_101])).
% 5.23/2.21  tff(c_118, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_116])).
% 5.23/2.21  tff(c_12, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.23/2.21  tff(c_136, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_118, c_12])).
% 5.23/2.21  tff(c_139, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_136])).
% 5.23/2.21  tff(c_142, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_139])).
% 5.23/2.21  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_142])).
% 5.23/2.21  tff(c_147, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_116])).
% 5.23/2.21  tff(c_433, plain, (![A_152, B_153, C_154]: (k1_tex_2(A_152, B_153)=C_154 | u1_struct_0(C_154)!=k6_domain_1(u1_struct_0(A_152), B_153) | ~m1_pre_topc(C_154, A_152) | ~v1_pre_topc(C_154) | v2_struct_0(C_154) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_pre_topc(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.23/2.21  tff(c_437, plain, (![C_154]: (k1_tex_2('#skF_1', '#skF_4')=C_154 | u1_struct_0(C_154)!=k1_tarski('#skF_4') | ~m1_pre_topc(C_154, '#skF_1') | ~v1_pre_topc(C_154) | v2_struct_0(C_154) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_433])).
% 5.23/2.21  tff(c_442, plain, (![C_154]: (k1_tex_2('#skF_1', '#skF_4')=C_154 | u1_struct_0(C_154)!=k1_tarski('#skF_4') | ~m1_pre_topc(C_154, '#skF_1') | ~v1_pre_topc(C_154) | v2_struct_0(C_154) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_67, c_437])).
% 5.23/2.21  tff(c_477, plain, (![C_156]: (k1_tex_2('#skF_1', '#skF_4')=C_156 | u1_struct_0(C_156)!=k1_tarski('#skF_4') | ~m1_pre_topc(C_156, '#skF_1') | ~v1_pre_topc(C_156) | v2_struct_0(C_156))), inference(negUnitSimplification, [status(thm)], [c_66, c_442])).
% 5.23/2.21  tff(c_485, plain, (k1_tex_2('#skF_2', '#skF_4')=k1_tex_2('#skF_1', '#skF_4') | u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))!=k1_tarski('#skF_4') | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_257, c_477])).
% 5.23/2.21  tff(c_503, plain, (k1_tex_2('#skF_2', '#skF_4')=k1_tex_2('#skF_1', '#skF_4') | u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))!=k1_tarski('#skF_4') | v2_struct_0(k1_tex_2('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_54, c_187, c_485])).
% 5.23/2.21  tff(c_504, plain, (k1_tex_2('#skF_2', '#skF_4')=k1_tex_2('#skF_1', '#skF_4') | u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))!=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_202, c_503])).
% 5.23/2.21  tff(c_519, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_504])).
% 5.23/2.21  tff(c_117, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_101])).
% 5.23/2.21  tff(c_149, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_117])).
% 5.23/2.21  tff(c_152, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_149, c_12])).
% 5.23/2.21  tff(c_155, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_152])).
% 5.23/2.21  tff(c_158, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_155])).
% 5.23/2.21  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_158])).
% 5.23/2.21  tff(c_163, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_117])).
% 5.23/2.21  tff(c_551, plain, (![A_159, B_160]: (k6_domain_1(u1_struct_0(A_159), B_160)=u1_struct_0(k1_tex_2(A_159, B_160)) | ~m1_pre_topc(k1_tex_2(A_159, B_160), A_159) | ~v1_pre_topc(k1_tex_2(A_159, B_160)) | v2_struct_0(k1_tex_2(A_159, B_160)) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l1_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.23/2.21  tff(c_559, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_237, c_551])).
% 5.23/2.21  tff(c_572, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4') | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_42, c_187, c_163, c_559])).
% 5.23/2.21  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_202, c_519, c_572])).
% 5.23/2.21  tff(c_575, plain, (k1_tex_2('#skF_2', '#skF_4')=k1_tex_2('#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_504])).
% 5.23/2.21  tff(c_581, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_575, c_237])).
% 5.23/2.21  tff(c_576, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_504])).
% 5.23/2.21  tff(c_609, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_575, c_576])).
% 5.23/2.21  tff(c_336, plain, (![B_142, C_143, A_144]: (r1_tarski(u1_struct_0(B_142), u1_struct_0(C_143)) | ~m1_pre_topc(B_142, C_143) | ~m1_pre_topc(C_143, A_144) | ~m1_pre_topc(B_142, A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.23/2.21  tff(c_348, plain, (![B_142]: (r1_tarski(u1_struct_0(B_142), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_142, '#skF_2') | ~m1_pre_topc(B_142, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_336])).
% 5.23/2.21  tff(c_360, plain, (![B_142]: (r1_tarski(u1_struct_0(B_142), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_142, '#skF_2') | ~m1_pre_topc(B_142, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_348])).
% 5.23/2.21  tff(c_632, plain, (r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_609, c_360])).
% 5.23/2.21  tff(c_669, plain, (r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_581, c_632])).
% 5.23/2.21  tff(c_361, plain, (![B_145]: (r1_tarski(u1_struct_0(B_145), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_145, '#skF_2') | ~m1_pre_topc(B_145, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_348])).
% 5.23/2.21  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/2.21  tff(c_238, plain, (![C_123, A_124, B_125]: (m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(B_125))) | ~m1_pre_topc(B_125, A_124) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.23/2.21  tff(c_280, plain, (![A_128, A_129, B_130]: (m1_subset_1(A_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_pre_topc(B_130, A_129) | ~l1_pre_topc(A_129) | ~r1_tarski(A_128, u1_struct_0(B_130)))), inference(resolution, [status(thm)], [c_6, c_238])).
% 5.23/2.21  tff(c_292, plain, (![A_128]: (m1_subset_1(A_128, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_128, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_54, c_280])).
% 5.23/2.21  tff(c_305, plain, (![A_131]: (m1_subset_1(A_131, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_131, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_292])).
% 5.23/2.21  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, B_3) | ~m1_subset_1(A_2, k1_zfmisc_1(B_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/2.21  tff(c_316, plain, (![A_131]: (r1_tarski(A_131, u1_struct_0('#skF_1')) | ~r1_tarski(A_131, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_305, c_4])).
% 5.23/2.21  tff(c_370, plain, (![B_145]: (r1_tarski(u1_struct_0(B_145), u1_struct_0('#skF_1')) | ~m1_pre_topc(B_145, '#skF_2') | ~m1_pre_topc(B_145, '#skF_1'))), inference(resolution, [status(thm)], [c_361, c_316])).
% 5.23/2.21  tff(c_629, plain, (r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_1')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_609, c_370])).
% 5.23/2.21  tff(c_667, plain, (r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_581, c_629])).
% 5.23/2.21  tff(c_62, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_56, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_48, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_44, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_760, plain, (![A_168, B_169, C_170, E_171]: (k8_relset_1(u1_struct_0(A_168), u1_struct_0(B_169), C_170, E_171)=k2_pre_topc(A_168, E_171) | ~m1_subset_1(E_171, k1_zfmisc_1(u1_struct_0(A_168))) | ~m1_subset_1(E_171, k1_zfmisc_1(u1_struct_0(B_169))) | ~v3_borsuk_1(C_170, A_168, B_169) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168), u1_struct_0(B_169)))) | ~v5_pre_topc(C_170, A_168, B_169) | ~v1_funct_2(C_170, u1_struct_0(A_168), u1_struct_0(B_169)) | ~v1_funct_1(C_170) | ~m1_pre_topc(B_169, A_168) | ~v4_tex_2(B_169, A_168) | v2_struct_0(B_169) | ~l1_pre_topc(A_168) | ~v3_tdlat_3(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.23/2.21  tff(c_895, plain, (![A_179, B_180, C_181, A_182]: (k8_relset_1(u1_struct_0(A_179), u1_struct_0(B_180), C_181, A_182)=k2_pre_topc(A_179, A_182) | ~m1_subset_1(A_182, k1_zfmisc_1(u1_struct_0(B_180))) | ~v3_borsuk_1(C_181, A_179, B_180) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_179), u1_struct_0(B_180)))) | ~v5_pre_topc(C_181, A_179, B_180) | ~v1_funct_2(C_181, u1_struct_0(A_179), u1_struct_0(B_180)) | ~v1_funct_1(C_181) | ~m1_pre_topc(B_180, A_179) | ~v4_tex_2(B_180, A_179) | v2_struct_0(B_180) | ~l1_pre_topc(A_179) | ~v3_tdlat_3(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179) | ~r1_tarski(A_182, u1_struct_0(A_179)))), inference(resolution, [status(thm)], [c_6, c_760])).
% 5.23/2.21  tff(c_1329, plain, (![A_214, B_215, C_216, A_217]: (k8_relset_1(u1_struct_0(A_214), u1_struct_0(B_215), C_216, A_217)=k2_pre_topc(A_214, A_217) | ~v3_borsuk_1(C_216, A_214, B_215) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214), u1_struct_0(B_215)))) | ~v5_pre_topc(C_216, A_214, B_215) | ~v1_funct_2(C_216, u1_struct_0(A_214), u1_struct_0(B_215)) | ~v1_funct_1(C_216) | ~m1_pre_topc(B_215, A_214) | ~v4_tex_2(B_215, A_214) | v2_struct_0(B_215) | ~l1_pre_topc(A_214) | ~v3_tdlat_3(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214) | ~r1_tarski(A_217, u1_struct_0(A_214)) | ~r1_tarski(A_217, u1_struct_0(B_215)))), inference(resolution, [status(thm)], [c_6, c_895])).
% 5.23/2.21  tff(c_1335, plain, (![A_217]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', A_217)=k2_pre_topc('#skF_1', A_217) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski(A_217, u1_struct_0('#skF_1')) | ~r1_tarski(A_217, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_46, c_1329])).
% 5.23/2.21  tff(c_1346, plain, (![A_217]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', A_217)=k2_pre_topc('#skF_1', A_217) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~r1_tarski(A_217, u1_struct_0('#skF_1')) | ~r1_tarski(A_217, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_56, c_54, c_52, c_50, c_48, c_44, c_1335])).
% 5.23/2.21  tff(c_1350, plain, (![A_218]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', A_218)=k2_pre_topc('#skF_1', A_218) | ~r1_tarski(A_218, u1_struct_0('#skF_1')) | ~r1_tarski(A_218, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_1346])).
% 5.23/2.21  tff(c_36, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.23/2.21  tff(c_68, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 5.23/2.21  tff(c_261, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_147, c_68])).
% 5.23/2.21  tff(c_1359, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_1')) | ~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1350, c_261])).
% 5.23/2.21  tff(c_1371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_669, c_667, c_1359])).
% 5.23/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.21  
% 5.23/2.21  Inference rules
% 5.23/2.21  ----------------------
% 5.23/2.21  #Ref     : 0
% 5.23/2.21  #Sup     : 256
% 5.23/2.21  #Fact    : 0
% 5.23/2.21  #Define  : 0
% 5.23/2.21  #Split   : 14
% 5.23/2.21  #Chain   : 0
% 5.23/2.21  #Close   : 0
% 5.23/2.21  
% 5.23/2.21  Ordering : KBO
% 5.23/2.21  
% 5.23/2.21  Simplification rules
% 5.23/2.21  ----------------------
% 5.23/2.21  #Subsume      : 67
% 5.23/2.21  #Demod        : 277
% 5.23/2.21  #Tautology    : 48
% 5.23/2.21  #SimpNegUnit  : 62
% 5.23/2.21  #BackRed      : 9
% 5.23/2.21  
% 5.23/2.21  #Partial instantiations: 0
% 5.23/2.21  #Strategies tried      : 1
% 5.23/2.21  
% 5.23/2.21  Timing (in seconds)
% 5.23/2.21  ----------------------
% 5.23/2.21  Preprocessing        : 0.58
% 5.23/2.21  Parsing              : 0.29
% 5.23/2.21  CNF conversion       : 0.05
% 5.23/2.21  Main loop            : 0.71
% 5.23/2.21  Inferencing          : 0.22
% 5.23/2.21  Reduction            : 0.25
% 5.23/2.21  Demodulation         : 0.18
% 5.23/2.21  BG Simplification    : 0.04
% 5.23/2.21  Subsumption          : 0.15
% 5.23/2.21  Abstraction          : 0.03
% 5.23/2.21  MUC search           : 0.00
% 5.23/2.21  Cooper               : 0.00
% 5.23/2.21  Total                : 1.35
% 5.23/2.21  Index Insertion      : 0.00
% 5.23/2.21  Index Deletion       : 0.00
% 5.23/2.21  Index Matching       : 0.00
% 5.23/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

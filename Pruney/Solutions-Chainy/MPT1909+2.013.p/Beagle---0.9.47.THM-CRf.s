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
% DateTime   : Thu Dec  3 10:30:39 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 193 expanded)
%              Number of leaves         :   38 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  230 ( 926 expanded)
%              Number of equality atoms :   22 ( 127 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_125,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_76,plain,(
    ! [A_85,B_86] :
      ( k6_domain_1(A_85,B_86) = k1_tarski(B_86)
      | ~ m1_subset_1(B_86,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_212,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_198,plain,(
    ! [B_114,A_115] :
      ( m1_subset_1(u1_struct_0(B_114),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_pre_topc(B_114,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v1_xboole_0(B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_2))
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_237,plain,(
    ! [B_118,A_119] :
      ( v1_xboole_0(u1_struct_0(B_118))
      | ~ v1_xboole_0(u1_struct_0(A_119))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_198,c_4])).

tff(c_239,plain,(
    ! [B_118] :
      ( v1_xboole_0(u1_struct_0(B_118))
      | ~ m1_pre_topc(B_118,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_212,c_237])).

tff(c_243,plain,(
    ! [B_120] :
      ( v1_xboole_0(u1_struct_0(B_120))
      | ~ m1_pre_topc(B_120,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_239])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_44,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_26,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_55,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_87,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_55,c_76])).

tff(c_89,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_10,plain,(
    ! [B_11,A_9] :
      ( m1_subset_1(u1_struct_0(B_11),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [B_106,A_107] :
      ( v3_tex_2(u1_struct_0(B_106),A_107)
      | ~ m1_subset_1(u1_struct_0(B_106),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ v4_tex_2(B_106,A_107)
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_161,plain,(
    ! [B_108,A_109] :
      ( v3_tex_2(u1_struct_0(B_108),A_109)
      | ~ v4_tex_2(B_108,A_109)
      | v2_struct_0(A_109)
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_10,c_156])).

tff(c_132,plain,(
    ! [B_100,A_101] :
      ( ~ v3_tex_2(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ v1_xboole_0(B_100)
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_141,plain,(
    ! [B_11,A_9] :
      ( ~ v3_tex_2(u1_struct_0(B_11),A_9)
      | ~ v1_xboole_0(u1_struct_0(B_11))
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_166,plain,(
    ! [B_110,A_111] :
      ( ~ v1_xboole_0(u1_struct_0(B_110))
      | ~ v2_pre_topc(A_111)
      | ~ v4_tex_2(B_110,A_111)
      | v2_struct_0(A_111)
      | ~ m1_pre_topc(B_110,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_161,c_141])).

tff(c_182,plain,(
    ! [A_113] :
      ( ~ v2_pre_topc(A_113)
      | ~ v4_tex_2('#skF_3',A_113)
      | v2_struct_0(A_113)
      | ~ m1_pre_topc('#skF_3',A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_89,c_166])).

tff(c_189,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_193,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_52,c_189])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_193])).

tff(c_197,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_248,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_243,c_197])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_248])).

tff(c_254,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_196,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_24,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_56,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_207,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_56])).

tff(c_302,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_207])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_36,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_32,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_256,plain,(
    ! [A_121,B_122] :
      ( m1_subset_1(k6_domain_1(A_121,B_122),k1_zfmisc_1(A_121))
      | ~ m1_subset_1(B_122,A_121)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_265,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_256])).

tff(c_269,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_265])).

tff(c_270,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_269])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_50,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_255,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k6_domain_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_274,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_6])).

tff(c_278,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_274])).

tff(c_279,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_278])).

tff(c_457,plain,(
    ! [A_153,B_154,C_155,E_156] :
      ( k8_relset_1(u1_struct_0(A_153),u1_struct_0(B_154),C_155,E_156) = k2_pre_topc(A_153,E_156)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_subset_1(E_156,k1_zfmisc_1(u1_struct_0(B_154)))
      | ~ v3_borsuk_1(C_155,A_153,B_154)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153),u1_struct_0(B_154))))
      | ~ v5_pre_topc(C_155,A_153,B_154)
      | ~ v1_funct_2(C_155,u1_struct_0(A_153),u1_struct_0(B_154))
      | ~ v1_funct_1(C_155)
      | ~ m1_pre_topc(B_154,A_153)
      | ~ v4_tex_2(B_154,A_153)
      | v2_struct_0(B_154)
      | ~ l1_pre_topc(A_153)
      | ~ v3_tdlat_3(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_461,plain,(
    ! [B_154,C_155] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_154),C_155,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_154)))
      | ~ v3_borsuk_1(C_155,'#skF_2',B_154)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_154))))
      | ~ v5_pre_topc(C_155,'#skF_2',B_154)
      | ~ v1_funct_2(C_155,u1_struct_0('#skF_2'),u1_struct_0(B_154))
      | ~ v1_funct_1(C_155)
      | ~ m1_pre_topc(B_154,'#skF_2')
      | ~ v4_tex_2(B_154,'#skF_2')
      | v2_struct_0(B_154)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_279,c_457])).

tff(c_472,plain,(
    ! [B_154,C_155] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_154),C_155,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_154)))
      | ~ v3_borsuk_1(C_155,'#skF_2',B_154)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_154))))
      | ~ v5_pre_topc(C_155,'#skF_2',B_154)
      | ~ v1_funct_2(C_155,u1_struct_0('#skF_2'),u1_struct_0(B_154))
      | ~ v1_funct_1(C_155)
      | ~ m1_pre_topc(B_154,'#skF_2')
      | ~ v4_tex_2(B_154,'#skF_2')
      | v2_struct_0(B_154)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_461])).

tff(c_554,plain,(
    ! [B_163,C_164] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_163),C_164,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_163)))
      | ~ v3_borsuk_1(C_164,'#skF_2',B_163)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_163))))
      | ~ v5_pre_topc(C_164,'#skF_2',B_163)
      | ~ v1_funct_2(C_164,u1_struct_0('#skF_2'),u1_struct_0(B_163))
      | ~ v1_funct_1(C_164)
      | ~ m1_pre_topc(B_163,'#skF_2')
      | ~ v4_tex_2(B_163,'#skF_2')
      | v2_struct_0(B_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_472])).

tff(c_561,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_554])).

tff(c_565,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_32,c_270,c_561])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_302,c_565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.48  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.16/1.48  
% 3.16/1.48  %Foreground sorts:
% 3.16/1.48  
% 3.16/1.48  
% 3.16/1.48  %Background operators:
% 3.16/1.48  
% 3.16/1.48  
% 3.16/1.48  %Foreground operators:
% 3.16/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.16/1.48  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.16/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.48  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.16/1.48  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.16/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.16/1.48  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.16/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.48  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.16/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.48  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.16/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.48  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.16/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.16/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.16/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.16/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.16/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.48  
% 3.16/1.50  tff(f_164, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.16/1.50  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.16/1.50  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.16/1.50  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.16/1.50  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 3.16/1.50  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 3.16/1.50  tff(f_41, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.16/1.50  tff(f_125, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.16/1.50  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_28, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_76, plain, (![A_85, B_86]: (k6_domain_1(A_85, B_86)=k1_tarski(B_86) | ~m1_subset_1(B_86, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.16/1.50  tff(c_88, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_76])).
% 3.16/1.50  tff(c_212, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_88])).
% 3.16/1.50  tff(c_198, plain, (![B_114, A_115]: (m1_subset_1(u1_struct_0(B_114), k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_pre_topc(B_114, A_115) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.50  tff(c_4, plain, (![B_4, A_2]: (v1_xboole_0(B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_2)) | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.50  tff(c_237, plain, (![B_118, A_119]: (v1_xboole_0(u1_struct_0(B_118)) | ~v1_xboole_0(u1_struct_0(A_119)) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_198, c_4])).
% 3.16/1.50  tff(c_239, plain, (![B_118]: (v1_xboole_0(u1_struct_0(B_118)) | ~m1_pre_topc(B_118, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_212, c_237])).
% 3.16/1.50  tff(c_243, plain, (![B_120]: (v1_xboole_0(u1_struct_0(B_120)) | ~m1_pre_topc(B_120, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_239])).
% 3.16/1.50  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_44, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_26, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_55, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 3.16/1.50  tff(c_87, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_55, c_76])).
% 3.16/1.50  tff(c_89, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_87])).
% 3.16/1.50  tff(c_10, plain, (![B_11, A_9]: (m1_subset_1(u1_struct_0(B_11), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.50  tff(c_156, plain, (![B_106, A_107]: (v3_tex_2(u1_struct_0(B_106), A_107) | ~m1_subset_1(u1_struct_0(B_106), k1_zfmisc_1(u1_struct_0(A_107))) | ~v4_tex_2(B_106, A_107) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.16/1.50  tff(c_161, plain, (![B_108, A_109]: (v3_tex_2(u1_struct_0(B_108), A_109) | ~v4_tex_2(B_108, A_109) | v2_struct_0(A_109) | ~m1_pre_topc(B_108, A_109) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_10, c_156])).
% 3.16/1.50  tff(c_132, plain, (![B_100, A_101]: (~v3_tex_2(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~v1_xboole_0(B_100) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.16/1.50  tff(c_141, plain, (![B_11, A_9]: (~v3_tex_2(u1_struct_0(B_11), A_9) | ~v1_xboole_0(u1_struct_0(B_11)) | ~v2_pre_topc(A_9) | v2_struct_0(A_9) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_10, c_132])).
% 3.16/1.50  tff(c_166, plain, (![B_110, A_111]: (~v1_xboole_0(u1_struct_0(B_110)) | ~v2_pre_topc(A_111) | ~v4_tex_2(B_110, A_111) | v2_struct_0(A_111) | ~m1_pre_topc(B_110, A_111) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_161, c_141])).
% 3.16/1.50  tff(c_182, plain, (![A_113]: (~v2_pre_topc(A_113) | ~v4_tex_2('#skF_3', A_113) | v2_struct_0(A_113) | ~m1_pre_topc('#skF_3', A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_89, c_166])).
% 3.16/1.50  tff(c_189, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_182])).
% 3.16/1.50  tff(c_193, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_52, c_189])).
% 3.16/1.50  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_193])).
% 3.16/1.50  tff(c_197, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_87])).
% 3.16/1.50  tff(c_248, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_243, c_197])).
% 3.16/1.50  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_248])).
% 3.16/1.50  tff(c_254, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_88])).
% 3.16/1.50  tff(c_196, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_87])).
% 3.16/1.50  tff(c_24, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_56, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24])).
% 3.16/1.50  tff(c_207, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_56])).
% 3.16/1.50  tff(c_302, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_207])).
% 3.16/1.50  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_36, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_32, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_256, plain, (![A_121, B_122]: (m1_subset_1(k6_domain_1(A_121, B_122), k1_zfmisc_1(A_121)) | ~m1_subset_1(B_122, A_121) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.50  tff(c_265, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_256])).
% 3.16/1.50  tff(c_269, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_265])).
% 3.16/1.50  tff(c_270, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_197, c_269])).
% 3.16/1.50  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_50, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.16/1.50  tff(c_255, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_88])).
% 3.16/1.50  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k6_domain_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.50  tff(c_274, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_254, c_6])).
% 3.16/1.50  tff(c_278, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_274])).
% 3.16/1.50  tff(c_279, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_255, c_278])).
% 3.16/1.50  tff(c_457, plain, (![A_153, B_154, C_155, E_156]: (k8_relset_1(u1_struct_0(A_153), u1_struct_0(B_154), C_155, E_156)=k2_pre_topc(A_153, E_156) | ~m1_subset_1(E_156, k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_subset_1(E_156, k1_zfmisc_1(u1_struct_0(B_154))) | ~v3_borsuk_1(C_155, A_153, B_154) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153), u1_struct_0(B_154)))) | ~v5_pre_topc(C_155, A_153, B_154) | ~v1_funct_2(C_155, u1_struct_0(A_153), u1_struct_0(B_154)) | ~v1_funct_1(C_155) | ~m1_pre_topc(B_154, A_153) | ~v4_tex_2(B_154, A_153) | v2_struct_0(B_154) | ~l1_pre_topc(A_153) | ~v3_tdlat_3(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.50  tff(c_461, plain, (![B_154, C_155]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_154), C_155, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_154))) | ~v3_borsuk_1(C_155, '#skF_2', B_154) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_154)))) | ~v5_pre_topc(C_155, '#skF_2', B_154) | ~v1_funct_2(C_155, u1_struct_0('#skF_2'), u1_struct_0(B_154)) | ~v1_funct_1(C_155) | ~m1_pre_topc(B_154, '#skF_2') | ~v4_tex_2(B_154, '#skF_2') | v2_struct_0(B_154) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_279, c_457])).
% 3.16/1.50  tff(c_472, plain, (![B_154, C_155]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_154), C_155, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_154))) | ~v3_borsuk_1(C_155, '#skF_2', B_154) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_154)))) | ~v5_pre_topc(C_155, '#skF_2', B_154) | ~v1_funct_2(C_155, u1_struct_0('#skF_2'), u1_struct_0(B_154)) | ~v1_funct_1(C_155) | ~m1_pre_topc(B_154, '#skF_2') | ~v4_tex_2(B_154, '#skF_2') | v2_struct_0(B_154) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_461])).
% 3.16/1.50  tff(c_554, plain, (![B_163, C_164]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_163), C_164, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_163))) | ~v3_borsuk_1(C_164, '#skF_2', B_163) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_163)))) | ~v5_pre_topc(C_164, '#skF_2', B_163) | ~v1_funct_2(C_164, u1_struct_0('#skF_2'), u1_struct_0(B_163)) | ~v1_funct_1(C_164) | ~m1_pre_topc(B_163, '#skF_2') | ~v4_tex_2(B_163, '#skF_2') | v2_struct_0(B_163))), inference(negUnitSimplification, [status(thm)], [c_54, c_472])).
% 3.16/1.50  tff(c_561, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_554])).
% 3.16/1.50  tff(c_565, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_32, c_270, c_561])).
% 3.16/1.50  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_302, c_565])).
% 3.16/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.50  
% 3.16/1.50  Inference rules
% 3.16/1.50  ----------------------
% 3.16/1.50  #Ref     : 0
% 3.16/1.50  #Sup     : 111
% 3.16/1.50  #Fact    : 0
% 3.16/1.50  #Define  : 0
% 3.16/1.50  #Split   : 11
% 3.16/1.50  #Chain   : 0
% 3.16/1.50  #Close   : 0
% 3.16/1.50  
% 3.16/1.50  Ordering : KBO
% 3.16/1.50  
% 3.16/1.50  Simplification rules
% 3.16/1.50  ----------------------
% 3.16/1.50  #Subsume      : 10
% 3.16/1.50  #Demod        : 59
% 3.16/1.50  #Tautology    : 30
% 3.16/1.50  #SimpNegUnit  : 17
% 3.16/1.50  #BackRed      : 1
% 3.16/1.50  
% 3.16/1.50  #Partial instantiations: 0
% 3.16/1.50  #Strategies tried      : 1
% 3.16/1.50  
% 3.16/1.50  Timing (in seconds)
% 3.16/1.50  ----------------------
% 3.16/1.50  Preprocessing        : 0.35
% 3.16/1.50  Parsing              : 0.18
% 3.16/1.50  CNF conversion       : 0.03
% 3.16/1.50  Main loop            : 0.36
% 3.16/1.50  Inferencing          : 0.13
% 3.16/1.50  Reduction            : 0.11
% 3.16/1.50  Demodulation         : 0.08
% 3.16/1.50  BG Simplification    : 0.02
% 3.16/1.50  Subsumption          : 0.07
% 3.16/1.50  Abstraction          : 0.02
% 3.16/1.50  MUC search           : 0.00
% 3.16/1.50  Cooper               : 0.00
% 3.16/1.50  Total                : 0.75
% 3.16/1.50  Index Insertion      : 0.00
% 3.16/1.50  Index Deletion       : 0.00
% 3.16/1.50  Index Matching       : 0.00
% 3.16/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:40 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 220 expanded)
%              Number of leaves         :   46 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  209 ( 995 expanded)
%              Number of equality atoms :   33 ( 149 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_188,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

tff(f_149,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_58,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_97,plain,(
    ! [B_120,A_121] :
      ( l1_pre_topc(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_97])).

tff(c_103,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_100])).

tff(c_22,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_138,plain,(
    ! [A_132,B_133] :
      ( k6_domain_1(A_132,B_133) = k1_tarski(B_133)
      | ~ m1_subset_1(B_133,A_132)
      | v1_xboole_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_154,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_138])).

tff(c_181,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_26,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_185,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_181,c_26])).

tff(c_188,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_185])).

tff(c_191,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_191])).

tff(c_196,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_42,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_71,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_153,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_71,c_138])).

tff(c_155,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_158,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_155,c_26])).

tff(c_161,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_158])).

tff(c_164,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_161])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_164])).

tff(c_169,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_40,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_72,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_176,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_72])).

tff(c_230,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_176])).

tff(c_60,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_52,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_48,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_197,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_232,plain,(
    ! [A_149,B_150,C_151] :
      ( k7_domain_1(A_149,B_150,C_151) = k2_tarski(B_150,C_151)
      | ~ m1_subset_1(C_151,A_149)
      | ~ m1_subset_1(B_150,A_149)
      | v1_xboole_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_240,plain,(
    ! [B_150] :
      ( k7_domain_1(u1_struct_0('#skF_2'),B_150,'#skF_4') = k2_tarski(B_150,'#skF_4')
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_46,c_232])).

tff(c_260,plain,(
    ! [B_153] :
      ( k7_domain_1(u1_struct_0('#skF_2'),B_153,'#skF_4') = k2_tarski(B_153,'#skF_4')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_240])).

tff(c_263,plain,(
    k7_domain_1(u1_struct_0('#skF_2'),'#skF_4','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_260])).

tff(c_265,plain,(
    k7_domain_1(u1_struct_0('#skF_2'),'#skF_4','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_263])).

tff(c_30,plain,(
    ! [A_46,B_47,C_48] :
      ( m1_subset_1(k7_domain_1(A_46,B_47,C_48),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(C_48,A_46)
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_310,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_30])).

tff(c_314,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_310])).

tff(c_315,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_314])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_66,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_170,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_238,plain,(
    ! [B_150] :
      ( k7_domain_1(u1_struct_0('#skF_1'),B_150,'#skF_4') = k2_tarski(B_150,'#skF_4')
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_71,c_232])).

tff(c_250,plain,(
    ! [B_152] :
      ( k7_domain_1(u1_struct_0('#skF_1'),B_152,'#skF_4') = k2_tarski(B_152,'#skF_4')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_238])).

tff(c_253,plain,(
    k7_domain_1(u1_struct_0('#skF_1'),'#skF_4','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_250])).

tff(c_255,plain,(
    k7_domain_1(u1_struct_0('#skF_1'),'#skF_4','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_253])).

tff(c_266,plain,(
    ! [A_154,B_155,C_156] :
      ( m1_subset_1(k7_domain_1(A_154,B_155,C_156),k1_zfmisc_1(A_154))
      | ~ m1_subset_1(C_156,A_154)
      | ~ m1_subset_1(B_155,A_154)
      | v1_xboole_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_280,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_266])).

tff(c_286,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_280])).

tff(c_287,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_286])).

tff(c_706,plain,(
    ! [A_211,B_212,C_213,E_214] :
      ( k8_relset_1(u1_struct_0(A_211),u1_struct_0(B_212),C_213,E_214) = k2_pre_topc(A_211,E_214)
      | ~ m1_subset_1(E_214,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ m1_subset_1(E_214,k1_zfmisc_1(u1_struct_0(B_212)))
      | ~ v3_borsuk_1(C_213,A_211,B_212)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_211),u1_struct_0(B_212))))
      | ~ v5_pre_topc(C_213,A_211,B_212)
      | ~ v1_funct_2(C_213,u1_struct_0(A_211),u1_struct_0(B_212))
      | ~ v1_funct_1(C_213)
      | ~ m1_pre_topc(B_212,A_211)
      | ~ v4_tex_2(B_212,A_211)
      | v2_struct_0(B_212)
      | ~ l1_pre_topc(A_211)
      | ~ v3_tdlat_3(A_211)
      | ~ v2_pre_topc(A_211)
      | v2_struct_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_718,plain,(
    ! [B_212,C_213] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_212),C_213,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_212)))
      | ~ v3_borsuk_1(C_213,'#skF_1',B_212)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_212))))
      | ~ v5_pre_topc(C_213,'#skF_1',B_212)
      | ~ v1_funct_2(C_213,u1_struct_0('#skF_1'),u1_struct_0(B_212))
      | ~ v1_funct_1(C_213)
      | ~ m1_pre_topc(B_212,'#skF_1')
      | ~ v4_tex_2(B_212,'#skF_1')
      | v2_struct_0(B_212)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_287,c_706])).

tff(c_738,plain,(
    ! [B_212,C_213] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_212),C_213,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_212)))
      | ~ v3_borsuk_1(C_213,'#skF_1',B_212)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_212))))
      | ~ v5_pre_topc(C_213,'#skF_1',B_212)
      | ~ v1_funct_2(C_213,u1_struct_0('#skF_1'),u1_struct_0(B_212))
      | ~ v1_funct_1(C_213)
      | ~ m1_pre_topc(B_212,'#skF_1')
      | ~ v4_tex_2(B_212,'#skF_1')
      | v2_struct_0(B_212)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_718])).

tff(c_793,plain,(
    ! [B_220,C_221] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_220),C_221,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_220)))
      | ~ v3_borsuk_1(C_221,'#skF_1',B_220)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_220))))
      | ~ v5_pre_topc(C_221,'#skF_1',B_220)
      | ~ v1_funct_2(C_221,u1_struct_0('#skF_1'),u1_struct_0(B_220))
      | ~ v1_funct_1(C_221)
      | ~ m1_pre_topc(B_220,'#skF_1')
      | ~ v4_tex_2(B_220,'#skF_1')
      | v2_struct_0(B_220) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_738])).

tff(c_800,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v4_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_793])).

tff(c_808,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_48,c_315,c_800])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_230,c_808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.58  
% 3.33/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.59  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.59  
% 3.33/1.59  %Foreground sorts:
% 3.33/1.59  
% 3.33/1.59  
% 3.33/1.59  %Background operators:
% 3.33/1.59  
% 3.33/1.59  
% 3.33/1.59  %Foreground operators:
% 3.33/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.59  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.33/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.59  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.33/1.59  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.33/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.33/1.59  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.33/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.33/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.33/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.59  tff(k7_domain_1, type, k7_domain_1: ($i * $i * $i) > $i).
% 3.33/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.33/1.59  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.33/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.59  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.33/1.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.33/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.33/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.59  
% 3.33/1.60  tff(f_188, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 3.33/1.60  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.33/1.60  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.33/1.60  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.33/1.60  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.33/1.60  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.33/1.60  tff(f_104, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => (k7_domain_1(A, B, C) = k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_domain_1)).
% 3.33/1.60  tff(f_88, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => m1_subset_1(k7_domain_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_domain_1)).
% 3.33/1.60  tff(f_149, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 3.33/1.60  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_58, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_97, plain, (![B_120, A_121]: (l1_pre_topc(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.60  tff(c_100, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_97])).
% 3.33/1.60  tff(c_103, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_100])).
% 3.33/1.60  tff(c_22, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.60  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_138, plain, (![A_132, B_133]: (k6_domain_1(A_132, B_133)=k1_tarski(B_133) | ~m1_subset_1(B_133, A_132) | v1_xboole_0(A_132))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.33/1.60  tff(c_154, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_138])).
% 3.33/1.60  tff(c_181, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_154])).
% 3.33/1.60  tff(c_26, plain, (![A_38]: (~v1_xboole_0(u1_struct_0(A_38)) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.33/1.60  tff(c_185, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_181, c_26])).
% 3.33/1.60  tff(c_188, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_185])).
% 3.33/1.60  tff(c_191, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_188])).
% 3.33/1.60  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_191])).
% 3.33/1.60  tff(c_196, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_154])).
% 3.33/1.60  tff(c_70, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_42, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_71, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 3.33/1.60  tff(c_153, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_71, c_138])).
% 3.33/1.60  tff(c_155, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_153])).
% 3.33/1.60  tff(c_158, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_155, c_26])).
% 3.33/1.60  tff(c_161, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_70, c_158])).
% 3.33/1.60  tff(c_164, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_161])).
% 3.33/1.60  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_164])).
% 3.33/1.60  tff(c_169, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_153])).
% 3.33/1.60  tff(c_40, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_72, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 3.33/1.60  tff(c_176, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_72])).
% 3.33/1.60  tff(c_230, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_176])).
% 3.33/1.60  tff(c_60, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_54, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_52, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_48, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.60  tff(c_197, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_154])).
% 3.33/1.60  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.33/1.60  tff(c_232, plain, (![A_149, B_150, C_151]: (k7_domain_1(A_149, B_150, C_151)=k2_tarski(B_150, C_151) | ~m1_subset_1(C_151, A_149) | ~m1_subset_1(B_150, A_149) | v1_xboole_0(A_149))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.33/1.60  tff(c_240, plain, (![B_150]: (k7_domain_1(u1_struct_0('#skF_2'), B_150, '#skF_4')=k2_tarski(B_150, '#skF_4') | ~m1_subset_1(B_150, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_46, c_232])).
% 3.33/1.61  tff(c_260, plain, (![B_153]: (k7_domain_1(u1_struct_0('#skF_2'), B_153, '#skF_4')=k2_tarski(B_153, '#skF_4') | ~m1_subset_1(B_153, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_197, c_240])).
% 3.33/1.61  tff(c_263, plain, (k7_domain_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_260])).
% 3.33/1.61  tff(c_265, plain, (k7_domain_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_263])).
% 3.33/1.61  tff(c_30, plain, (![A_46, B_47, C_48]: (m1_subset_1(k7_domain_1(A_46, B_47, C_48), k1_zfmisc_1(A_46)) | ~m1_subset_1(C_48, A_46) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.33/1.61  tff(c_310, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_265, c_30])).
% 3.33/1.61  tff(c_314, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_310])).
% 3.33/1.61  tff(c_315, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_197, c_314])).
% 3.33/1.61  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.61  tff(c_68, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.61  tff(c_66, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.33/1.61  tff(c_170, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_153])).
% 3.33/1.61  tff(c_238, plain, (![B_150]: (k7_domain_1(u1_struct_0('#skF_1'), B_150, '#skF_4')=k2_tarski(B_150, '#skF_4') | ~m1_subset_1(B_150, u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_71, c_232])).
% 3.33/1.61  tff(c_250, plain, (![B_152]: (k7_domain_1(u1_struct_0('#skF_1'), B_152, '#skF_4')=k2_tarski(B_152, '#skF_4') | ~m1_subset_1(B_152, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_170, c_238])).
% 3.33/1.61  tff(c_253, plain, (k7_domain_1(u1_struct_0('#skF_1'), '#skF_4', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_71, c_250])).
% 3.33/1.61  tff(c_255, plain, (k7_domain_1(u1_struct_0('#skF_1'), '#skF_4', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_253])).
% 3.33/1.61  tff(c_266, plain, (![A_154, B_155, C_156]: (m1_subset_1(k7_domain_1(A_154, B_155, C_156), k1_zfmisc_1(A_154)) | ~m1_subset_1(C_156, A_154) | ~m1_subset_1(B_155, A_154) | v1_xboole_0(A_154))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.33/1.61  tff(c_280, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_266])).
% 3.33/1.61  tff(c_286, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_280])).
% 3.33/1.61  tff(c_287, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_170, c_286])).
% 3.33/1.61  tff(c_706, plain, (![A_211, B_212, C_213, E_214]: (k8_relset_1(u1_struct_0(A_211), u1_struct_0(B_212), C_213, E_214)=k2_pre_topc(A_211, E_214) | ~m1_subset_1(E_214, k1_zfmisc_1(u1_struct_0(A_211))) | ~m1_subset_1(E_214, k1_zfmisc_1(u1_struct_0(B_212))) | ~v3_borsuk_1(C_213, A_211, B_212) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_211), u1_struct_0(B_212)))) | ~v5_pre_topc(C_213, A_211, B_212) | ~v1_funct_2(C_213, u1_struct_0(A_211), u1_struct_0(B_212)) | ~v1_funct_1(C_213) | ~m1_pre_topc(B_212, A_211) | ~v4_tex_2(B_212, A_211) | v2_struct_0(B_212) | ~l1_pre_topc(A_211) | ~v3_tdlat_3(A_211) | ~v2_pre_topc(A_211) | v2_struct_0(A_211))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.33/1.61  tff(c_718, plain, (![B_212, C_213]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_212), C_213, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_212))) | ~v3_borsuk_1(C_213, '#skF_1', B_212) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_212)))) | ~v5_pre_topc(C_213, '#skF_1', B_212) | ~v1_funct_2(C_213, u1_struct_0('#skF_1'), u1_struct_0(B_212)) | ~v1_funct_1(C_213) | ~m1_pre_topc(B_212, '#skF_1') | ~v4_tex_2(B_212, '#skF_1') | v2_struct_0(B_212) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_287, c_706])).
% 3.33/1.61  tff(c_738, plain, (![B_212, C_213]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_212), C_213, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_212))) | ~v3_borsuk_1(C_213, '#skF_1', B_212) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_212)))) | ~v5_pre_topc(C_213, '#skF_1', B_212) | ~v1_funct_2(C_213, u1_struct_0('#skF_1'), u1_struct_0(B_212)) | ~v1_funct_1(C_213) | ~m1_pre_topc(B_212, '#skF_1') | ~v4_tex_2(B_212, '#skF_1') | v2_struct_0(B_212) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_718])).
% 3.33/1.61  tff(c_793, plain, (![B_220, C_221]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_220), C_221, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_220))) | ~v3_borsuk_1(C_221, '#skF_1', B_220) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_220)))) | ~v5_pre_topc(C_221, '#skF_1', B_220) | ~v1_funct_2(C_221, u1_struct_0('#skF_1'), u1_struct_0(B_220)) | ~v1_funct_1(C_221) | ~m1_pre_topc(B_220, '#skF_1') | ~v4_tex_2(B_220, '#skF_1') | v2_struct_0(B_220))), inference(negUnitSimplification, [status(thm)], [c_70, c_738])).
% 3.33/1.61  tff(c_800, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_793])).
% 3.33/1.61  tff(c_808, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_48, c_315, c_800])).
% 3.33/1.61  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_230, c_808])).
% 3.33/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.61  
% 3.33/1.61  Inference rules
% 3.33/1.61  ----------------------
% 3.33/1.61  #Ref     : 0
% 3.33/1.61  #Sup     : 158
% 3.33/1.61  #Fact    : 0
% 3.33/1.61  #Define  : 0
% 3.33/1.61  #Split   : 9
% 3.33/1.61  #Chain   : 0
% 3.33/1.61  #Close   : 0
% 3.33/1.61  
% 3.33/1.61  Ordering : KBO
% 3.33/1.61  
% 3.33/1.61  Simplification rules
% 3.33/1.61  ----------------------
% 3.33/1.61  #Subsume      : 22
% 3.33/1.61  #Demod        : 73
% 3.33/1.61  #Tautology    : 66
% 3.33/1.61  #SimpNegUnit  : 14
% 3.33/1.61  #BackRed      : 1
% 3.33/1.61  
% 3.33/1.61  #Partial instantiations: 0
% 3.33/1.61  #Strategies tried      : 1
% 3.33/1.61  
% 3.33/1.61  Timing (in seconds)
% 3.33/1.61  ----------------------
% 3.33/1.61  Preprocessing        : 0.40
% 3.33/1.61  Parsing              : 0.22
% 3.33/1.61  CNF conversion       : 0.03
% 3.33/1.61  Main loop            : 0.40
% 3.33/1.61  Inferencing          : 0.14
% 3.33/1.61  Reduction            : 0.13
% 3.33/1.61  Demodulation         : 0.09
% 3.33/1.61  BG Simplification    : 0.03
% 3.33/1.61  Subsumption          : 0.07
% 3.33/1.61  Abstraction          : 0.02
% 3.33/1.61  MUC search           : 0.00
% 3.33/1.61  Cooper               : 0.00
% 3.33/1.61  Total                : 0.84
% 3.33/1.61  Index Insertion      : 0.00
% 3.33/1.61  Index Deletion       : 0.00
% 3.33/1.61  Index Matching       : 0.00
% 3.33/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

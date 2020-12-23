%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:39 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 220 expanded)
%              Number of leaves         :   46 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  205 ( 995 expanded)
%              Number of equality atoms :   33 ( 149 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

tff(f_142,axiom,(
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

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_22,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_40,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_69,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_132,plain,(
    ! [A_125,B_126] :
      ( k6_domain_1(A_125,B_126) = k1_tarski(B_126)
      | ~ m1_subset_1(B_126,A_125)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_147,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_69,c_132])).

tff(c_178,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_26,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_190,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_178,c_26])).

tff(c_193,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_190])).

tff(c_196,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_196])).

tff(c_201,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_56,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_96,plain,(
    ! [B_115,A_116] :
      ( l1_pre_topc(B_115)
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_96])).

tff(c_102,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_99])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_148,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_132])).

tff(c_158,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_161,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_158,c_26])).

tff(c_164,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_161])).

tff(c_167,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_167])).

tff(c_172,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_38,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_70,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_203,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_70])).

tff(c_204,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_203])).

tff(c_58,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_50,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_46,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_173,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_268,plain,(
    ! [A_157,B_158,C_159] :
      ( k7_domain_1(A_157,B_158,C_159) = k2_tarski(B_158,C_159)
      | ~ m1_subset_1(C_159,A_157)
      | ~ m1_subset_1(B_158,A_157)
      | v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_280,plain,(
    ! [B_158] :
      ( k7_domain_1(u1_struct_0('#skF_2'),B_158,'#skF_4') = k2_tarski(B_158,'#skF_4')
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_268])).

tff(c_348,plain,(
    ! [B_170] :
      ( k7_domain_1(u1_struct_0('#skF_2'),B_170,'#skF_4') = k2_tarski(B_170,'#skF_4')
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_280])).

tff(c_351,plain,(
    k7_domain_1(u1_struct_0('#skF_2'),'#skF_4','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_348])).

tff(c_353,plain,(
    k7_domain_1(u1_struct_0('#skF_2'),'#skF_4','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_351])).

tff(c_30,plain,(
    ! [A_46,B_47,C_48] :
      ( m1_subset_1(k7_domain_1(A_46,B_47,C_48),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(C_48,A_46)
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_357,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_30])).

tff(c_361,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_357])).

tff(c_362,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_361])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_64,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_202,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_278,plain,(
    ! [B_158] :
      ( k7_domain_1(u1_struct_0('#skF_1'),B_158,'#skF_4') = k2_tarski(B_158,'#skF_4')
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_69,c_268])).

tff(c_292,plain,(
    ! [B_160] :
      ( k7_domain_1(u1_struct_0('#skF_1'),B_160,'#skF_4') = k2_tarski(B_160,'#skF_4')
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_278])).

tff(c_295,plain,(
    k7_domain_1(u1_struct_0('#skF_1'),'#skF_4','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_69,c_292])).

tff(c_297,plain,(
    k7_domain_1(u1_struct_0('#skF_1'),'#skF_4','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_295])).

tff(c_301,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_30])).

tff(c_305,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_301])).

tff(c_306,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_305])).

tff(c_395,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_403,plain,(
    ! [B_174,C_175] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_174),C_175,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_174)))
      | ~ v3_borsuk_1(C_175,'#skF_1',B_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_174))))
      | ~ v5_pre_topc(C_175,'#skF_1',B_174)
      | ~ v1_funct_2(C_175,u1_struct_0('#skF_1'),u1_struct_0(B_174))
      | ~ v1_funct_1(C_175)
      | ~ m1_pre_topc(B_174,'#skF_1')
      | ~ v4_tex_2(B_174,'#skF_1')
      | v2_struct_0(B_174)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_306,c_395])).

tff(c_420,plain,(
    ! [B_174,C_175] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_174),C_175,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_174)))
      | ~ v3_borsuk_1(C_175,'#skF_1',B_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_174))))
      | ~ v5_pre_topc(C_175,'#skF_1',B_174)
      | ~ v1_funct_2(C_175,u1_struct_0('#skF_1'),u1_struct_0(B_174))
      | ~ v1_funct_1(C_175)
      | ~ m1_pre_topc(B_174,'#skF_1')
      | ~ v4_tex_2(B_174,'#skF_1')
      | v2_struct_0(B_174)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_403])).

tff(c_427,plain,(
    ! [B_177,C_178] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_177),C_178,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_177)))
      | ~ v3_borsuk_1(C_178,'#skF_1',B_177)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_177))))
      | ~ v5_pre_topc(C_178,'#skF_1',B_177)
      | ~ v1_funct_2(C_178,u1_struct_0('#skF_1'),u1_struct_0(B_177))
      | ~ v1_funct_1(C_178)
      | ~ m1_pre_topc(B_177,'#skF_1')
      | ~ v4_tex_2(B_177,'#skF_1')
      | v2_struct_0(B_177) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_420])).

tff(c_434,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v4_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_427])).

tff(c_442,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_46,c_362,c_434])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_204,c_442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.49  
% 3.07/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.49  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.07/1.49  
% 3.07/1.49  %Foreground sorts:
% 3.07/1.49  
% 3.07/1.49  
% 3.07/1.49  %Background operators:
% 3.07/1.49  
% 3.07/1.49  
% 3.07/1.49  %Foreground operators:
% 3.07/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.07/1.49  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.07/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.49  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.07/1.49  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.07/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.07/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.07/1.49  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.07/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.07/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.07/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.49  tff(k7_domain_1, type, k7_domain_1: ($i * $i * $i) > $i).
% 3.07/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.07/1.49  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.07/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.49  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.07/1.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.07/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.07/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.07/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.07/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.07/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.49  
% 3.24/1.51  tff(f_181, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 3.24/1.51  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.24/1.51  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.24/1.51  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.24/1.51  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.24/1.51  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.24/1.51  tff(f_104, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => (k7_domain_1(A, B, C) = k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_domain_1)).
% 3.24/1.51  tff(f_88, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => m1_subset_1(k7_domain_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_domain_1)).
% 3.24/1.51  tff(f_142, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 3.24/1.51  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_22, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.24/1.51  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_40, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_69, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 3.24/1.51  tff(c_132, plain, (![A_125, B_126]: (k6_domain_1(A_125, B_126)=k1_tarski(B_126) | ~m1_subset_1(B_126, A_125) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.51  tff(c_147, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_69, c_132])).
% 3.24/1.51  tff(c_178, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_147])).
% 3.24/1.51  tff(c_26, plain, (![A_38]: (~v1_xboole_0(u1_struct_0(A_38)) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.24/1.51  tff(c_190, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_178, c_26])).
% 3.24/1.51  tff(c_193, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_190])).
% 3.24/1.51  tff(c_196, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_193])).
% 3.24/1.51  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_196])).
% 3.24/1.51  tff(c_201, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_147])).
% 3.24/1.51  tff(c_56, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_96, plain, (![B_115, A_116]: (l1_pre_topc(B_115) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.51  tff(c_99, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_96])).
% 3.24/1.51  tff(c_102, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_99])).
% 3.24/1.51  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_148, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_132])).
% 3.24/1.51  tff(c_158, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_148])).
% 3.24/1.51  tff(c_161, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_158, c_26])).
% 3.24/1.51  tff(c_164, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_161])).
% 3.24/1.51  tff(c_167, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_164])).
% 3.24/1.51  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_167])).
% 3.24/1.51  tff(c_172, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_148])).
% 3.24/1.51  tff(c_38, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_70, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 3.24/1.51  tff(c_203, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_70])).
% 3.24/1.51  tff(c_204, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_203])).
% 3.24/1.51  tff(c_58, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_50, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_46, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_173, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_148])).
% 3.24/1.51  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.51  tff(c_268, plain, (![A_157, B_158, C_159]: (k7_domain_1(A_157, B_158, C_159)=k2_tarski(B_158, C_159) | ~m1_subset_1(C_159, A_157) | ~m1_subset_1(B_158, A_157) | v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.24/1.51  tff(c_280, plain, (![B_158]: (k7_domain_1(u1_struct_0('#skF_2'), B_158, '#skF_4')=k2_tarski(B_158, '#skF_4') | ~m1_subset_1(B_158, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_268])).
% 3.24/1.51  tff(c_348, plain, (![B_170]: (k7_domain_1(u1_struct_0('#skF_2'), B_170, '#skF_4')=k2_tarski(B_170, '#skF_4') | ~m1_subset_1(B_170, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_173, c_280])).
% 3.24/1.51  tff(c_351, plain, (k7_domain_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_348])).
% 3.24/1.51  tff(c_353, plain, (k7_domain_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_351])).
% 3.24/1.51  tff(c_30, plain, (![A_46, B_47, C_48]: (m1_subset_1(k7_domain_1(A_46, B_47, C_48), k1_zfmisc_1(A_46)) | ~m1_subset_1(C_48, A_46) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.24/1.51  tff(c_357, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_353, c_30])).
% 3.24/1.51  tff(c_361, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_357])).
% 3.24/1.51  tff(c_362, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_173, c_361])).
% 3.24/1.51  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_64, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.24/1.51  tff(c_202, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_147])).
% 3.24/1.51  tff(c_278, plain, (![B_158]: (k7_domain_1(u1_struct_0('#skF_1'), B_158, '#skF_4')=k2_tarski(B_158, '#skF_4') | ~m1_subset_1(B_158, u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_69, c_268])).
% 3.24/1.51  tff(c_292, plain, (![B_160]: (k7_domain_1(u1_struct_0('#skF_1'), B_160, '#skF_4')=k2_tarski(B_160, '#skF_4') | ~m1_subset_1(B_160, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_202, c_278])).
% 3.24/1.51  tff(c_295, plain, (k7_domain_1(u1_struct_0('#skF_1'), '#skF_4', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_69, c_292])).
% 3.24/1.51  tff(c_297, plain, (k7_domain_1(u1_struct_0('#skF_1'), '#skF_4', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_295])).
% 3.24/1.51  tff(c_301, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_297, c_30])).
% 3.24/1.51  tff(c_305, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_301])).
% 3.24/1.51  tff(c_306, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_202, c_305])).
% 3.24/1.51  tff(c_395, plain, (![A_173, B_174, C_175, E_176]: (k8_relset_1(u1_struct_0(A_173), u1_struct_0(B_174), C_175, E_176)=k2_pre_topc(A_173, E_176) | ~m1_subset_1(E_176, k1_zfmisc_1(u1_struct_0(A_173))) | ~m1_subset_1(E_176, k1_zfmisc_1(u1_struct_0(B_174))) | ~v3_borsuk_1(C_175, A_173, B_174) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_173), u1_struct_0(B_174)))) | ~v5_pre_topc(C_175, A_173, B_174) | ~v1_funct_2(C_175, u1_struct_0(A_173), u1_struct_0(B_174)) | ~v1_funct_1(C_175) | ~m1_pre_topc(B_174, A_173) | ~v4_tex_2(B_174, A_173) | v2_struct_0(B_174) | ~l1_pre_topc(A_173) | ~v3_tdlat_3(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.24/1.51  tff(c_403, plain, (![B_174, C_175]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_174), C_175, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_174))) | ~v3_borsuk_1(C_175, '#skF_1', B_174) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_174)))) | ~v5_pre_topc(C_175, '#skF_1', B_174) | ~v1_funct_2(C_175, u1_struct_0('#skF_1'), u1_struct_0(B_174)) | ~v1_funct_1(C_175) | ~m1_pre_topc(B_174, '#skF_1') | ~v4_tex_2(B_174, '#skF_1') | v2_struct_0(B_174) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_306, c_395])).
% 3.24/1.51  tff(c_420, plain, (![B_174, C_175]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_174), C_175, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_174))) | ~v3_borsuk_1(C_175, '#skF_1', B_174) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_174)))) | ~v5_pre_topc(C_175, '#skF_1', B_174) | ~v1_funct_2(C_175, u1_struct_0('#skF_1'), u1_struct_0(B_174)) | ~v1_funct_1(C_175) | ~m1_pre_topc(B_174, '#skF_1') | ~v4_tex_2(B_174, '#skF_1') | v2_struct_0(B_174) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_403])).
% 3.24/1.51  tff(c_427, plain, (![B_177, C_178]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_177), C_178, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_177))) | ~v3_borsuk_1(C_178, '#skF_1', B_177) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_177)))) | ~v5_pre_topc(C_178, '#skF_1', B_177) | ~v1_funct_2(C_178, u1_struct_0('#skF_1'), u1_struct_0(B_177)) | ~v1_funct_1(C_178) | ~m1_pre_topc(B_177, '#skF_1') | ~v4_tex_2(B_177, '#skF_1') | v2_struct_0(B_177))), inference(negUnitSimplification, [status(thm)], [c_68, c_420])).
% 3.24/1.51  tff(c_434, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_427])).
% 3.24/1.51  tff(c_442, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_46, c_362, c_434])).
% 3.24/1.51  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_204, c_442])).
% 3.24/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.51  
% 3.24/1.51  Inference rules
% 3.24/1.51  ----------------------
% 3.24/1.51  #Ref     : 0
% 3.24/1.51  #Sup     : 84
% 3.24/1.51  #Fact    : 0
% 3.24/1.51  #Define  : 0
% 3.24/1.51  #Split   : 8
% 3.24/1.51  #Chain   : 0
% 3.24/1.51  #Close   : 0
% 3.24/1.51  
% 3.24/1.51  Ordering : KBO
% 3.24/1.51  
% 3.24/1.51  Simplification rules
% 3.24/1.51  ----------------------
% 3.24/1.51  #Subsume      : 2
% 3.24/1.51  #Demod        : 26
% 3.24/1.51  #Tautology    : 33
% 3.24/1.51  #SimpNegUnit  : 9
% 3.24/1.51  #BackRed      : 1
% 3.24/1.51  
% 3.24/1.51  #Partial instantiations: 0
% 3.24/1.51  #Strategies tried      : 1
% 3.24/1.51  
% 3.24/1.51  Timing (in seconds)
% 3.24/1.51  ----------------------
% 3.24/1.51  Preprocessing        : 0.36
% 3.24/1.51  Parsing              : 0.19
% 3.24/1.51  CNF conversion       : 0.03
% 3.24/1.51  Main loop            : 0.30
% 3.24/1.51  Inferencing          : 0.10
% 3.24/1.51  Reduction            : 0.10
% 3.24/1.51  Demodulation         : 0.07
% 3.24/1.51  BG Simplification    : 0.02
% 3.24/1.51  Subsumption          : 0.06
% 3.24/1.51  Abstraction          : 0.02
% 3.24/1.51  MUC search           : 0.00
% 3.24/1.51  Cooper               : 0.00
% 3.24/1.51  Total                : 0.70
% 3.24/1.51  Index Insertion      : 0.00
% 3.24/1.51  Index Deletion       : 0.00
% 3.24/1.51  Index Matching       : 0.00
% 3.24/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

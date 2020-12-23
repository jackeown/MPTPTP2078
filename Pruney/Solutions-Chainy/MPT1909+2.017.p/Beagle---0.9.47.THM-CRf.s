%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:39 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 218 expanded)
%              Number of leaves         :   45 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  204 ( 994 expanded)
%              Number of equality atoms :   32 ( 148 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

tff(f_145,axiom,(
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

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_18,plain,(
    ! [A_32] :
      ( l1_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_38,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_67,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_115,plain,(
    ! [A_124,B_125] :
      ( k6_domain_1(A_124,B_125) = k1_tarski(B_125)
      | ~ m1_subset_1(B_125,A_124)
      | v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_126,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_67,c_115])).

tff(c_128,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_22,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_131,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_128,c_22])).

tff(c_134,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_131])).

tff(c_137,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_134])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_137])).

tff(c_142,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_54,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_83,plain,(
    ! [B_114,A_115] :
      ( l1_pre_topc(B_114)
      | ~ m1_pre_topc(B_114,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_83])).

tff(c_89,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_86])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_127,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_115])).

tff(c_144,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_147,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_144,c_22])).

tff(c_150,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_147])).

tff(c_153,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_150])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_153])).

tff(c_158,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_36,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_68,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_186,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_158,c_68])).

tff(c_56,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_48,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_44,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_159,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_206,plain,(
    ! [A_145,B_146,C_147] :
      ( k7_domain_1(A_145,B_146,C_147) = k2_tarski(B_146,C_147)
      | ~ m1_subset_1(C_147,A_145)
      | ~ m1_subset_1(B_146,A_145)
      | v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_214,plain,(
    ! [B_146] :
      ( k7_domain_1(u1_struct_0('#skF_2'),B_146,'#skF_4') = k2_tarski(B_146,'#skF_4')
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_42,c_206])).

tff(c_237,plain,(
    ! [B_152] :
      ( k7_domain_1(u1_struct_0('#skF_2'),B_152,'#skF_4') = k2_tarski(B_152,'#skF_4')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_214])).

tff(c_240,plain,(
    k7_domain_1(u1_struct_0('#skF_2'),'#skF_4','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_237])).

tff(c_242,plain,(
    k7_domain_1(u1_struct_0('#skF_2'),'#skF_4','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_240])).

tff(c_248,plain,(
    ! [A_153,B_154,C_155] :
      ( m1_subset_1(k7_domain_1(A_153,B_154,C_155),k1_zfmisc_1(A_153))
      | ~ m1_subset_1(C_155,A_153)
      | ~ m1_subset_1(B_154,A_153)
      | v1_xboole_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_262,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_248])).

tff(c_271,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_262])).

tff(c_272,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_271])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_62,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_143,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_212,plain,(
    ! [B_146] :
      ( k7_domain_1(u1_struct_0('#skF_1'),B_146,'#skF_4') = k2_tarski(B_146,'#skF_4')
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_67,c_206])).

tff(c_223,plain,(
    ! [B_148] :
      ( k7_domain_1(u1_struct_0('#skF_1'),B_148,'#skF_4') = k2_tarski(B_148,'#skF_4')
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_212])).

tff(c_226,plain,(
    k7_domain_1(u1_struct_0('#skF_1'),'#skF_4','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_67,c_223])).

tff(c_228,plain,(
    k7_domain_1(u1_struct_0('#skF_1'),'#skF_4','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_226])).

tff(c_265,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_248])).

tff(c_274,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_265])).

tff(c_275,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_274])).

tff(c_350,plain,(
    ! [A_167,B_168,C_169,E_170] :
      ( k8_relset_1(u1_struct_0(A_167),u1_struct_0(B_168),C_169,E_170) = k2_pre_topc(A_167,E_170)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_subset_1(E_170,k1_zfmisc_1(u1_struct_0(B_168)))
      | ~ v3_borsuk_1(C_169,A_167,B_168)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_167),u1_struct_0(B_168))))
      | ~ v5_pre_topc(C_169,A_167,B_168)
      | ~ v1_funct_2(C_169,u1_struct_0(A_167),u1_struct_0(B_168))
      | ~ v1_funct_1(C_169)
      | ~ m1_pre_topc(B_168,A_167)
      | ~ v4_tex_2(B_168,A_167)
      | v2_struct_0(B_168)
      | ~ l1_pre_topc(A_167)
      | ~ v3_tdlat_3(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_356,plain,(
    ! [B_168,C_169] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_168),C_169,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_168)))
      | ~ v3_borsuk_1(C_169,'#skF_1',B_168)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_168))))
      | ~ v5_pre_topc(C_169,'#skF_1',B_168)
      | ~ v1_funct_2(C_169,u1_struct_0('#skF_1'),u1_struct_0(B_168))
      | ~ v1_funct_1(C_169)
      | ~ m1_pre_topc(B_168,'#skF_1')
      | ~ v4_tex_2(B_168,'#skF_1')
      | v2_struct_0(B_168)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_275,c_350])).

tff(c_368,plain,(
    ! [B_168,C_169] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_168),C_169,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_168)))
      | ~ v3_borsuk_1(C_169,'#skF_1',B_168)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_168))))
      | ~ v5_pre_topc(C_169,'#skF_1',B_168)
      | ~ v1_funct_2(C_169,u1_struct_0('#skF_1'),u1_struct_0(B_168))
      | ~ v1_funct_1(C_169)
      | ~ m1_pre_topc(B_168,'#skF_1')
      | ~ v4_tex_2(B_168,'#skF_1')
      | v2_struct_0(B_168)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_356])).

tff(c_405,plain,(
    ! [B_175,C_176] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_175),C_176,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_175)))
      | ~ v3_borsuk_1(C_176,'#skF_1',B_175)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_175))))
      | ~ v5_pre_topc(C_176,'#skF_1',B_175)
      | ~ v1_funct_2(C_176,u1_struct_0('#skF_1'),u1_struct_0(B_175))
      | ~ v1_funct_1(C_176)
      | ~ m1_pre_topc(B_175,'#skF_1')
      | ~ v4_tex_2(B_175,'#skF_1')
      | v2_struct_0(B_175) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_368])).

tff(c_412,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v4_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_405])).

tff(c_416,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_44,c_272,c_412])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_186,c_416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.52  
% 2.42/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.52  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.52  
% 2.42/1.52  %Foreground sorts:
% 2.42/1.52  
% 2.42/1.52  
% 2.42/1.52  %Background operators:
% 2.42/1.52  
% 2.42/1.52  
% 2.42/1.52  %Foreground operators:
% 2.42/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.42/1.52  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.42/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.52  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.42/1.52  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.42/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.42/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.42/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.42/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.42/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.52  tff(k7_domain_1, type, k7_domain_1: ($i * $i * $i) > $i).
% 2.42/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.42/1.52  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.42/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.52  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.42/1.52  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.42/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.42/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.42/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.42/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.52  
% 2.70/1.54  tff(f_184, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 2.70/1.54  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.70/1.54  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.70/1.54  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.70/1.54  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.70/1.54  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.70/1.54  tff(f_100, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => (k7_domain_1(A, B, C) = k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_domain_1)).
% 2.70/1.54  tff(f_84, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => m1_subset_1(k7_domain_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_domain_1)).
% 2.70/1.54  tff(f_145, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 2.70/1.54  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_18, plain, (![A_32]: (l1_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.54  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_38, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_67, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 2.70/1.54  tff(c_115, plain, (![A_124, B_125]: (k6_domain_1(A_124, B_125)=k1_tarski(B_125) | ~m1_subset_1(B_125, A_124) | v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.54  tff(c_126, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_67, c_115])).
% 2.70/1.54  tff(c_128, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_126])).
% 2.70/1.54  tff(c_22, plain, (![A_36]: (~v1_xboole_0(u1_struct_0(A_36)) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.70/1.54  tff(c_131, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_128, c_22])).
% 2.70/1.54  tff(c_134, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_131])).
% 2.70/1.54  tff(c_137, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_134])).
% 2.70/1.54  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_137])).
% 2.70/1.54  tff(c_142, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_126])).
% 2.70/1.54  tff(c_54, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_83, plain, (![B_114, A_115]: (l1_pre_topc(B_114) | ~m1_pre_topc(B_114, A_115) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.70/1.54  tff(c_86, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_83])).
% 2.70/1.54  tff(c_89, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_86])).
% 2.70/1.54  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_115])).
% 2.70/1.54  tff(c_144, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_127])).
% 2.70/1.54  tff(c_147, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_144, c_22])).
% 2.70/1.54  tff(c_150, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_147])).
% 2.70/1.54  tff(c_153, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_150])).
% 2.70/1.54  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_153])).
% 2.70/1.54  tff(c_158, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_127])).
% 2.70/1.54  tff(c_36, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_68, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 2.70/1.54  tff(c_186, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_158, c_68])).
% 2.70/1.54  tff(c_56, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_48, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_44, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_159, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_127])).
% 2.70/1.54  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.54  tff(c_206, plain, (![A_145, B_146, C_147]: (k7_domain_1(A_145, B_146, C_147)=k2_tarski(B_146, C_147) | ~m1_subset_1(C_147, A_145) | ~m1_subset_1(B_146, A_145) | v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.70/1.54  tff(c_214, plain, (![B_146]: (k7_domain_1(u1_struct_0('#skF_2'), B_146, '#skF_4')=k2_tarski(B_146, '#skF_4') | ~m1_subset_1(B_146, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_42, c_206])).
% 2.70/1.54  tff(c_237, plain, (![B_152]: (k7_domain_1(u1_struct_0('#skF_2'), B_152, '#skF_4')=k2_tarski(B_152, '#skF_4') | ~m1_subset_1(B_152, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_159, c_214])).
% 2.70/1.54  tff(c_240, plain, (k7_domain_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_237])).
% 2.70/1.54  tff(c_242, plain, (k7_domain_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_240])).
% 2.70/1.54  tff(c_248, plain, (![A_153, B_154, C_155]: (m1_subset_1(k7_domain_1(A_153, B_154, C_155), k1_zfmisc_1(A_153)) | ~m1_subset_1(C_155, A_153) | ~m1_subset_1(B_154, A_153) | v1_xboole_0(A_153))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.70/1.54  tff(c_262, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_242, c_248])).
% 2.70/1.54  tff(c_271, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_262])).
% 2.70/1.54  tff(c_272, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_159, c_271])).
% 2.70/1.54  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_62, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.70/1.54  tff(c_143, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_126])).
% 2.70/1.54  tff(c_212, plain, (![B_146]: (k7_domain_1(u1_struct_0('#skF_1'), B_146, '#skF_4')=k2_tarski(B_146, '#skF_4') | ~m1_subset_1(B_146, u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_67, c_206])).
% 2.70/1.54  tff(c_223, plain, (![B_148]: (k7_domain_1(u1_struct_0('#skF_1'), B_148, '#skF_4')=k2_tarski(B_148, '#skF_4') | ~m1_subset_1(B_148, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_143, c_212])).
% 2.70/1.54  tff(c_226, plain, (k7_domain_1(u1_struct_0('#skF_1'), '#skF_4', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_67, c_223])).
% 2.70/1.54  tff(c_228, plain, (k7_domain_1(u1_struct_0('#skF_1'), '#skF_4', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_226])).
% 2.70/1.54  tff(c_265, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_248])).
% 2.70/1.54  tff(c_274, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_265])).
% 2.70/1.54  tff(c_275, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_143, c_274])).
% 2.70/1.54  tff(c_350, plain, (![A_167, B_168, C_169, E_170]: (k8_relset_1(u1_struct_0(A_167), u1_struct_0(B_168), C_169, E_170)=k2_pre_topc(A_167, E_170) | ~m1_subset_1(E_170, k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_subset_1(E_170, k1_zfmisc_1(u1_struct_0(B_168))) | ~v3_borsuk_1(C_169, A_167, B_168) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_167), u1_struct_0(B_168)))) | ~v5_pre_topc(C_169, A_167, B_168) | ~v1_funct_2(C_169, u1_struct_0(A_167), u1_struct_0(B_168)) | ~v1_funct_1(C_169) | ~m1_pre_topc(B_168, A_167) | ~v4_tex_2(B_168, A_167) | v2_struct_0(B_168) | ~l1_pre_topc(A_167) | ~v3_tdlat_3(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.70/1.54  tff(c_356, plain, (![B_168, C_169]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_168), C_169, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_168))) | ~v3_borsuk_1(C_169, '#skF_1', B_168) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_168)))) | ~v5_pre_topc(C_169, '#skF_1', B_168) | ~v1_funct_2(C_169, u1_struct_0('#skF_1'), u1_struct_0(B_168)) | ~v1_funct_1(C_169) | ~m1_pre_topc(B_168, '#skF_1') | ~v4_tex_2(B_168, '#skF_1') | v2_struct_0(B_168) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_275, c_350])).
% 2.70/1.54  tff(c_368, plain, (![B_168, C_169]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_168), C_169, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_168))) | ~v3_borsuk_1(C_169, '#skF_1', B_168) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_168)))) | ~v5_pre_topc(C_169, '#skF_1', B_168) | ~v1_funct_2(C_169, u1_struct_0('#skF_1'), u1_struct_0(B_168)) | ~v1_funct_1(C_169) | ~m1_pre_topc(B_168, '#skF_1') | ~v4_tex_2(B_168, '#skF_1') | v2_struct_0(B_168) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_356])).
% 2.70/1.54  tff(c_405, plain, (![B_175, C_176]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_175), C_176, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_175))) | ~v3_borsuk_1(C_176, '#skF_1', B_175) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_175)))) | ~v5_pre_topc(C_176, '#skF_1', B_175) | ~v1_funct_2(C_176, u1_struct_0('#skF_1'), u1_struct_0(B_175)) | ~v1_funct_1(C_176) | ~m1_pre_topc(B_175, '#skF_1') | ~v4_tex_2(B_175, '#skF_1') | v2_struct_0(B_175))), inference(negUnitSimplification, [status(thm)], [c_66, c_368])).
% 2.70/1.54  tff(c_412, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_405])).
% 2.70/1.54  tff(c_416, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_44, c_272, c_412])).
% 2.70/1.54  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_186, c_416])).
% 2.70/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.54  
% 2.70/1.54  Inference rules
% 2.70/1.54  ----------------------
% 2.70/1.54  #Ref     : 0
% 2.70/1.54  #Sup     : 78
% 2.70/1.54  #Fact    : 0
% 2.70/1.54  #Define  : 0
% 2.70/1.54  #Split   : 8
% 2.70/1.54  #Chain   : 0
% 2.70/1.54  #Close   : 0
% 2.70/1.54  
% 2.70/1.54  Ordering : KBO
% 2.70/1.54  
% 2.70/1.54  Simplification rules
% 2.70/1.54  ----------------------
% 2.70/1.54  #Subsume      : 3
% 2.70/1.54  #Demod        : 32
% 2.70/1.54  #Tautology    : 28
% 2.70/1.54  #SimpNegUnit  : 10
% 2.70/1.54  #BackRed      : 0
% 2.70/1.54  
% 2.70/1.54  #Partial instantiations: 0
% 2.70/1.54  #Strategies tried      : 1
% 2.70/1.54  
% 2.70/1.54  Timing (in seconds)
% 2.70/1.54  ----------------------
% 2.70/1.54  Preprocessing        : 0.33
% 2.70/1.54  Parsing              : 0.17
% 2.70/1.54  CNF conversion       : 0.03
% 2.70/1.54  Main loop            : 0.27
% 2.70/1.54  Inferencing          : 0.09
% 2.70/1.54  Reduction            : 0.09
% 2.70/1.54  Demodulation         : 0.06
% 2.70/1.54  BG Simplification    : 0.02
% 2.70/1.54  Subsumption          : 0.05
% 2.70/1.55  Abstraction          : 0.01
% 2.70/1.55  MUC search           : 0.00
% 2.70/1.55  Cooper               : 0.00
% 2.70/1.55  Total                : 0.64
% 2.70/1.55  Index Insertion      : 0.00
% 2.70/1.55  Index Deletion       : 0.00
% 2.70/1.55  Index Matching       : 0.00
% 2.70/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

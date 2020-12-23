%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:52 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 824 expanded)
%              Number of leaves         :   39 ( 310 expanded)
%              Depth                    :   25
%              Number of atoms          :  408 (3315 expanded)
%              Number of equality atoms :   23 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_147,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_188,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_176,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_213,plain,(
    ! [A_70,B_71] :
      ( m1_pre_topc('#skF_2'(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | v1_xboole_0(B_71)
      | ~ l1_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_220,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_213])).

tff(c_225,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_220])).

tff(c_226,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_225])).

tff(c_154,plain,(
    ! [A_64,B_65] :
      ( ~ v2_struct_0('#skF_2'(A_64,B_65))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | v1_xboole_0(B_65)
      | ~ l1_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_161,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_154])).

tff(c_165,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_161])).

tff(c_166,plain,(
    ~ v2_struct_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_165])).

tff(c_180,plain,(
    ! [A_68,B_69] :
      ( u1_struct_0('#skF_2'(A_68,B_69)) = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | v1_xboole_0(B_69)
      | ~ l1_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_187,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_180])).

tff(c_191,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_187])).

tff(c_192,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_191])).

tff(c_70,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_72,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_30,plain,(
    ! [A_24] :
      ( m1_subset_1('#skF_1'(A_24),A_24)
      | ~ v1_zfmisc_1(A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_266,plain,(
    ! [C_76,A_77,B_78] :
      ( m1_subset_1(C_76,u1_struct_0(A_77))
      | ~ m1_subset_1(C_76,u1_struct_0(B_78))
      | ~ m1_pre_topc(B_78,A_77)
      | v2_struct_0(B_78)
      | ~ l1_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_661,plain,(
    ! [B_105,A_106] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_105)),u1_struct_0(A_106))
      | ~ m1_pre_topc(B_105,A_106)
      | v2_struct_0(B_105)
      | ~ l1_pre_topc(A_106)
      | v2_struct_0(A_106)
      | ~ v1_zfmisc_1(u1_struct_0(B_105))
      | v1_xboole_0(u1_struct_0(B_105)) ) ),
    inference(resolution,[status(thm)],[c_30,c_266])).

tff(c_684,plain,(
    ! [A_106] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_106))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_106)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_106)
      | v2_struct_0(A_106)
      | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
      | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_661])).

tff(c_692,plain,(
    ! [A_106] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_106))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_106)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_106)
      | v2_struct_0(A_106)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_72,c_192,c_684])).

tff(c_693,plain,(
    ! [A_106] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_106))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_106)
      | ~ l1_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_166,c_692])).

tff(c_64,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_74,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64])).

tff(c_28,plain,(
    ! [A_24] :
      ( k6_domain_1(A_24,'#skF_1'(A_24)) = A_24
      | ~ v1_zfmisc_1(A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_246,plain,
    ( l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_226,c_6])).

tff(c_253,plain,(
    l1_pre_topc('#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_246])).

tff(c_58,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_24,plain,(
    ! [B_23,A_21] :
      ( v2_tdlat_3(B_23)
      | ~ m1_pre_topc(B_23,A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_tdlat_3(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_243,plain,
    ( v2_tdlat_3('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_226,c_24])).

tff(c_249,plain,
    ( v2_tdlat_3('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_243])).

tff(c_250,plain,(
    v2_tdlat_3('#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_249])).

tff(c_16,plain,(
    ! [A_19] :
      ( v2_pre_topc(A_19)
      | ~ v2_tdlat_3(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_257,plain,
    ( v2_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_250,c_16])).

tff(c_259,plain,(
    v2_pre_topc('#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_257])).

tff(c_227,plain,(
    ! [A_72,B_73] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_72),B_73),A_72)
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_230,plain,(
    ! [B_73] :
      ( v2_tex_2(k6_domain_1('#skF_5',B_73),'#skF_2'('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_2'('#skF_4','#skF_5')))
      | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_227])).

tff(c_239,plain,(
    ! [B_73] :
      ( v2_tex_2(k6_domain_1('#skF_5',B_73),'#skF_2'('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_73,'#skF_5')
      | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_230])).

tff(c_240,plain,(
    ! [B_73] :
      ( v2_tex_2(k6_domain_1('#skF_5',B_73),'#skF_2'('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_73,'#skF_5')
      | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_2'('#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_239])).

tff(c_350,plain,(
    ! [B_85] :
      ( v2_tex_2(k6_domain_1('#skF_5',B_85),'#skF_2'('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_85,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_253,c_240])).

tff(c_358,plain,
    ( v2_tex_2('#skF_5','#skF_2'('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_350])).

tff(c_363,plain,
    ( v2_tex_2('#skF_5','#skF_2'('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_358])).

tff(c_364,plain,
    ( v2_tex_2('#skF_5','#skF_2'('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_363])).

tff(c_365,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_369,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_365])).

tff(c_372,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_369])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_372])).

tff(c_376,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_12,plain,(
    ! [A_16,B_17] :
      ( k6_domain_1(A_16,B_17) = k1_tarski(B_17)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_382,plain,
    ( k6_domain_1('#skF_5','#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_376,c_12])).

tff(c_388,plain,(
    k6_domain_1('#skF_5','#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_382])).

tff(c_398,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_28])).

tff(c_414,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_398])).

tff(c_415,plain,(
    k1_tarski('#skF_1'('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_414])).

tff(c_86,plain,(
    ! [B_51,A_52] :
      ( v1_xboole_0(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_86])).

tff(c_97,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_93])).

tff(c_268,plain,(
    ! [C_76,A_77] :
      ( m1_subset_1(C_76,u1_struct_0(A_77))
      | ~ m1_subset_1(C_76,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_77)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_266])).

tff(c_274,plain,(
    ! [C_79,A_80] :
      ( m1_subset_1(C_79,u1_struct_0(A_80))
      | ~ m1_subset_1(C_79,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_80)
      | ~ l1_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_268])).

tff(c_847,plain,(
    ! [A_113,C_114] :
      ( k6_domain_1(u1_struct_0(A_113),C_114) = k1_tarski(C_114)
      | v1_xboole_0(u1_struct_0(A_113))
      | ~ m1_subset_1(C_114,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_113)
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_274,c_12])).

tff(c_849,plain,(
    ! [C_114] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_114) = k1_tarski(C_114)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_114,'#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_226,c_847])).

tff(c_852,plain,(
    ! [C_114] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_114) = k1_tarski(C_114)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_114,'#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_849])).

tff(c_854,plain,(
    ! [C_115] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_115) = k1_tarski(C_115)
      | ~ m1_subset_1(C_115,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_97,c_852])).

tff(c_50,plain,(
    ! [A_40,B_42] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_40),B_42),A_40)
      | ~ m1_subset_1(B_42,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_864,plain,(
    ! [C_115] :
      ( v2_tex_2(k1_tarski(C_115),'#skF_4')
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_115,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_50])).

tff(c_893,plain,(
    ! [C_115] :
      ( v2_tex_2(k1_tarski(C_115),'#skF_4')
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_115,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_864])).

tff(c_905,plain,(
    ! [C_116] :
      ( v2_tex_2(k1_tarski(C_116),'#skF_4')
      | ~ m1_subset_1(C_116,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_116,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_893])).

tff(c_908,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_905])).

tff(c_913,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_908])).

tff(c_914,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_913])).

tff(c_930,plain,
    ( ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_693,c_914])).

tff(c_936,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_226,c_930])).

tff(c_938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_936])).

tff(c_939,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1391,plain,(
    ! [A_176,B_177] :
      ( m1_pre_topc('#skF_3'(A_176,B_177),A_176)
      | ~ v2_tex_2(B_177,A_176)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | v1_xboole_0(B_177)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1400,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1391])).

tff(c_1407,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_939,c_1400])).

tff(c_1408,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_1407])).

tff(c_1414,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1408,c_6])).

tff(c_1421,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1414])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1291,plain,(
    ! [A_165,B_166] :
      ( ~ v2_struct_0('#skF_3'(A_165,B_166))
      | ~ v2_tex_2(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | v1_xboole_0(B_166)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1304,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1291])).

tff(c_1311,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_939,c_1304])).

tff(c_1312,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_1311])).

tff(c_1411,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1408,c_24])).

tff(c_1417,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1411])).

tff(c_1418,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1417])).

tff(c_1425,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1418,c_16])).

tff(c_1427,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_1425])).

tff(c_1203,plain,(
    ! [A_157,B_158] :
      ( v1_tdlat_3('#skF_3'(A_157,B_158))
      | ~ v2_tex_2(B_158,A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | v1_xboole_0(B_158)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1213,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1203])).

tff(c_1220,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_939,c_1213])).

tff(c_1221,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_1220])).

tff(c_20,plain,(
    ! [A_20] :
      ( v7_struct_0(A_20)
      | ~ v2_tdlat_3(A_20)
      | ~ v1_tdlat_3(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_940,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1470,plain,(
    ! [A_183,B_184] :
      ( u1_struct_0('#skF_3'(A_183,B_184)) = B_184
      | ~ v2_tex_2(B_184,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | v1_xboole_0(B_184)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1483,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1470])).

tff(c_1490,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_939,c_1483])).

tff(c_1491,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_1490])).

tff(c_8,plain,(
    ! [A_8] :
      ( v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | ~ v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1528,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1491,c_8])).

tff(c_1565,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_940,c_1528])).

tff(c_1567,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1565])).

tff(c_1570,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_1567])).

tff(c_1573,plain,(
    v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_1427,c_1221,c_1418,c_1570])).

tff(c_1575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1312,c_1573])).

tff(c_1576,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1565])).

tff(c_1591,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_1576])).

tff(c_1595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_1591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:22:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.68  
% 3.95/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.68  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 4.14/1.68  
% 4.14/1.68  %Foreground sorts:
% 4.14/1.68  
% 4.14/1.68  
% 4.14/1.68  %Background operators:
% 4.14/1.68  
% 4.14/1.68  
% 4.14/1.68  %Foreground operators:
% 4.14/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.14/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.14/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.14/1.68  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.14/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.14/1.68  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.14/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.14/1.68  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.14/1.68  tff('#skF_5', type, '#skF_5': $i).
% 4.14/1.68  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.14/1.68  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.14/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.14/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.14/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.68  tff('#skF_4', type, '#skF_4': $i).
% 4.14/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.14/1.68  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.14/1.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.14/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.14/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.14/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.14/1.68  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.14/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.14/1.68  
% 4.14/1.72  tff(f_208, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 4.14/1.72  tff(f_147, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 4.14/1.72  tff(f_126, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 4.14/1.72  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 4.14/1.72  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.14/1.72  tff(f_116, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 4.14/1.72  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 4.14/1.72  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.14/1.72  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.14/1.72  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.14/1.72  tff(f_176, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 4.14/1.72  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.14/1.72  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 4.14/1.72  tff(f_49, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 4.14/1.72  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.14/1.72  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.14/1.72  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.14/1.72  tff(c_60, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.14/1.72  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.14/1.72  tff(c_213, plain, (![A_70, B_71]: (m1_pre_topc('#skF_2'(A_70, B_71), A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | v1_xboole_0(B_71) | ~l1_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.14/1.72  tff(c_220, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_213])).
% 4.14/1.72  tff(c_225, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_220])).
% 4.14/1.72  tff(c_226, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_225])).
% 4.14/1.72  tff(c_154, plain, (![A_64, B_65]: (~v2_struct_0('#skF_2'(A_64, B_65)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | v1_xboole_0(B_65) | ~l1_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.14/1.72  tff(c_161, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_154])).
% 4.14/1.72  tff(c_165, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_161])).
% 4.14/1.72  tff(c_166, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_165])).
% 4.14/1.72  tff(c_180, plain, (![A_68, B_69]: (u1_struct_0('#skF_2'(A_68, B_69))=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | v1_xboole_0(B_69) | ~l1_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.14/1.72  tff(c_187, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_180])).
% 4.14/1.72  tff(c_191, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_187])).
% 4.14/1.72  tff(c_192, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_191])).
% 4.14/1.72  tff(c_70, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.14/1.72  tff(c_72, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 4.14/1.72  tff(c_30, plain, (![A_24]: (m1_subset_1('#skF_1'(A_24), A_24) | ~v1_zfmisc_1(A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.14/1.72  tff(c_266, plain, (![C_76, A_77, B_78]: (m1_subset_1(C_76, u1_struct_0(A_77)) | ~m1_subset_1(C_76, u1_struct_0(B_78)) | ~m1_pre_topc(B_78, A_77) | v2_struct_0(B_78) | ~l1_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.14/1.72  tff(c_661, plain, (![B_105, A_106]: (m1_subset_1('#skF_1'(u1_struct_0(B_105)), u1_struct_0(A_106)) | ~m1_pre_topc(B_105, A_106) | v2_struct_0(B_105) | ~l1_pre_topc(A_106) | v2_struct_0(A_106) | ~v1_zfmisc_1(u1_struct_0(B_105)) | v1_xboole_0(u1_struct_0(B_105)))), inference(resolution, [status(thm)], [c_30, c_266])).
% 4.14/1.72  tff(c_684, plain, (![A_106]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_106)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_106) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_106) | v2_struct_0(A_106) | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_192, c_661])).
% 4.14/1.72  tff(c_692, plain, (![A_106]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_106)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_106) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_106) | v2_struct_0(A_106) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_72, c_192, c_684])).
% 4.14/1.72  tff(c_693, plain, (![A_106]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_106)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_106) | ~l1_pre_topc(A_106) | v2_struct_0(A_106))), inference(negUnitSimplification, [status(thm)], [c_54, c_166, c_692])).
% 4.14/1.72  tff(c_64, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.14/1.72  tff(c_74, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64])).
% 4.14/1.72  tff(c_28, plain, (![A_24]: (k6_domain_1(A_24, '#skF_1'(A_24))=A_24 | ~v1_zfmisc_1(A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.14/1.72  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.14/1.72  tff(c_246, plain, (l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_226, c_6])).
% 4.14/1.72  tff(c_253, plain, (l1_pre_topc('#skF_2'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_246])).
% 4.14/1.72  tff(c_58, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.14/1.72  tff(c_24, plain, (![B_23, A_21]: (v2_tdlat_3(B_23) | ~m1_pre_topc(B_23, A_21) | ~l1_pre_topc(A_21) | ~v2_tdlat_3(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.14/1.72  tff(c_243, plain, (v2_tdlat_3('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_226, c_24])).
% 4.14/1.72  tff(c_249, plain, (v2_tdlat_3('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_243])).
% 4.14/1.72  tff(c_250, plain, (v2_tdlat_3('#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_249])).
% 4.14/1.72  tff(c_16, plain, (![A_19]: (v2_pre_topc(A_19) | ~v2_tdlat_3(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.14/1.72  tff(c_257, plain, (v2_pre_topc('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_250, c_16])).
% 4.14/1.72  tff(c_259, plain, (v2_pre_topc('#skF_2'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_257])).
% 4.14/1.72  tff(c_227, plain, (![A_72, B_73]: (v2_tex_2(k6_domain_1(u1_struct_0(A_72), B_73), A_72) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.14/1.72  tff(c_230, plain, (![B_73]: (v2_tex_2(k6_domain_1('#skF_5', B_73), '#skF_2'('#skF_4', '#skF_5')) | ~m1_subset_1(B_73, u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_192, c_227])).
% 4.14/1.72  tff(c_239, plain, (![B_73]: (v2_tex_2(k6_domain_1('#skF_5', B_73), '#skF_2'('#skF_4', '#skF_5')) | ~m1_subset_1(B_73, '#skF_5') | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_230])).
% 4.14/1.72  tff(c_240, plain, (![B_73]: (v2_tex_2(k6_domain_1('#skF_5', B_73), '#skF_2'('#skF_4', '#skF_5')) | ~m1_subset_1(B_73, '#skF_5') | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_2'('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_166, c_239])).
% 4.14/1.72  tff(c_350, plain, (![B_85]: (v2_tex_2(k6_domain_1('#skF_5', B_85), '#skF_2'('#skF_4', '#skF_5')) | ~m1_subset_1(B_85, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_253, c_240])).
% 4.14/1.72  tff(c_358, plain, (v2_tex_2('#skF_5', '#skF_2'('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_350])).
% 4.14/1.72  tff(c_363, plain, (v2_tex_2('#skF_5', '#skF_2'('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_358])).
% 4.14/1.72  tff(c_364, plain, (v2_tex_2('#skF_5', '#skF_2'('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_363])).
% 4.14/1.72  tff(c_365, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_364])).
% 4.14/1.72  tff(c_369, plain, (~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_365])).
% 4.14/1.72  tff(c_372, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_369])).
% 4.14/1.72  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_372])).
% 4.14/1.72  tff(c_376, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_364])).
% 4.14/1.72  tff(c_12, plain, (![A_16, B_17]: (k6_domain_1(A_16, B_17)=k1_tarski(B_17) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.14/1.72  tff(c_382, plain, (k6_domain_1('#skF_5', '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_376, c_12])).
% 4.14/1.72  tff(c_388, plain, (k6_domain_1('#skF_5', '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_382])).
% 4.14/1.72  tff(c_398, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_388, c_28])).
% 4.14/1.72  tff(c_414, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_398])).
% 4.14/1.72  tff(c_415, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_414])).
% 4.14/1.72  tff(c_86, plain, (![B_51, A_52]: (v1_xboole_0(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.14/1.72  tff(c_93, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_86])).
% 4.14/1.72  tff(c_97, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_93])).
% 4.14/1.72  tff(c_268, plain, (![C_76, A_77]: (m1_subset_1(C_76, u1_struct_0(A_77)) | ~m1_subset_1(C_76, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_77) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_77) | v2_struct_0(A_77))), inference(superposition, [status(thm), theory('equality')], [c_192, c_266])).
% 4.14/1.72  tff(c_274, plain, (![C_79, A_80]: (m1_subset_1(C_79, u1_struct_0(A_80)) | ~m1_subset_1(C_79, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_80) | ~l1_pre_topc(A_80) | v2_struct_0(A_80))), inference(negUnitSimplification, [status(thm)], [c_166, c_268])).
% 4.14/1.72  tff(c_847, plain, (![A_113, C_114]: (k6_domain_1(u1_struct_0(A_113), C_114)=k1_tarski(C_114) | v1_xboole_0(u1_struct_0(A_113)) | ~m1_subset_1(C_114, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_113) | ~l1_pre_topc(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_274, c_12])).
% 4.14/1.72  tff(c_849, plain, (![C_114]: (k6_domain_1(u1_struct_0('#skF_4'), C_114)=k1_tarski(C_114) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_114, '#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_226, c_847])).
% 4.14/1.72  tff(c_852, plain, (![C_114]: (k6_domain_1(u1_struct_0('#skF_4'), C_114)=k1_tarski(C_114) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_114, '#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_849])).
% 4.14/1.72  tff(c_854, plain, (![C_115]: (k6_domain_1(u1_struct_0('#skF_4'), C_115)=k1_tarski(C_115) | ~m1_subset_1(C_115, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_97, c_852])).
% 4.14/1.72  tff(c_50, plain, (![A_40, B_42]: (v2_tex_2(k6_domain_1(u1_struct_0(A_40), B_42), A_40) | ~m1_subset_1(B_42, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.14/1.72  tff(c_864, plain, (![C_115]: (v2_tex_2(k1_tarski(C_115), '#skF_4') | ~m1_subset_1(C_115, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(C_115, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_854, c_50])).
% 4.14/1.72  tff(c_893, plain, (![C_115]: (v2_tex_2(k1_tarski(C_115), '#skF_4') | ~m1_subset_1(C_115, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_subset_1(C_115, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_864])).
% 4.14/1.72  tff(c_905, plain, (![C_116]: (v2_tex_2(k1_tarski(C_116), '#skF_4') | ~m1_subset_1(C_116, u1_struct_0('#skF_4')) | ~m1_subset_1(C_116, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_893])).
% 4.14/1.72  tff(c_908, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_415, c_905])).
% 4.14/1.72  tff(c_913, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_908])).
% 4.14/1.72  tff(c_914, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_913])).
% 4.14/1.72  tff(c_930, plain, (~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_693, c_914])).
% 4.14/1.72  tff(c_936, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_226, c_930])).
% 4.14/1.72  tff(c_938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_936])).
% 4.14/1.72  tff(c_939, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_70])).
% 4.14/1.72  tff(c_1391, plain, (![A_176, B_177]: (m1_pre_topc('#skF_3'(A_176, B_177), A_176) | ~v2_tex_2(B_177, A_176) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | v1_xboole_0(B_177) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.14/1.72  tff(c_1400, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1391])).
% 4.14/1.72  tff(c_1407, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_939, c_1400])).
% 4.14/1.72  tff(c_1408, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_1407])).
% 4.14/1.72  tff(c_1414, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1408, c_6])).
% 4.14/1.72  tff(c_1421, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1414])).
% 4.14/1.72  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.14/1.72  tff(c_1291, plain, (![A_165, B_166]: (~v2_struct_0('#skF_3'(A_165, B_166)) | ~v2_tex_2(B_166, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | v1_xboole_0(B_166) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.14/1.72  tff(c_1304, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1291])).
% 4.14/1.72  tff(c_1311, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_939, c_1304])).
% 4.14/1.72  tff(c_1312, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_1311])).
% 4.14/1.72  tff(c_1411, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1408, c_24])).
% 4.14/1.72  tff(c_1417, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_1411])).
% 4.14/1.72  tff(c_1418, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_1417])).
% 4.14/1.72  tff(c_1425, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1418, c_16])).
% 4.14/1.72  tff(c_1427, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1421, c_1425])).
% 4.14/1.72  tff(c_1203, plain, (![A_157, B_158]: (v1_tdlat_3('#skF_3'(A_157, B_158)) | ~v2_tex_2(B_158, A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | v1_xboole_0(B_158) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.14/1.72  tff(c_1213, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1203])).
% 4.14/1.72  tff(c_1220, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_939, c_1213])).
% 4.14/1.72  tff(c_1221, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_1220])).
% 4.14/1.72  tff(c_20, plain, (![A_20]: (v7_struct_0(A_20) | ~v2_tdlat_3(A_20) | ~v1_tdlat_3(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.14/1.72  tff(c_940, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 4.14/1.72  tff(c_1470, plain, (![A_183, B_184]: (u1_struct_0('#skF_3'(A_183, B_184))=B_184 | ~v2_tex_2(B_184, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | v1_xboole_0(B_184) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.14/1.72  tff(c_1483, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1470])).
% 4.14/1.72  tff(c_1490, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_939, c_1483])).
% 4.14/1.72  tff(c_1491, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_1490])).
% 4.14/1.72  tff(c_8, plain, (![A_8]: (v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | ~v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/1.72  tff(c_1528, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1491, c_8])).
% 4.14/1.72  tff(c_1565, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_940, c_1528])).
% 4.14/1.72  tff(c_1567, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1565])).
% 4.14/1.72  tff(c_1570, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_1567])).
% 4.14/1.72  tff(c_1573, plain, (v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1421, c_1427, c_1221, c_1418, c_1570])).
% 4.14/1.72  tff(c_1575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1312, c_1573])).
% 4.14/1.72  tff(c_1576, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1565])).
% 4.14/1.72  tff(c_1591, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_1576])).
% 4.14/1.72  tff(c_1595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1421, c_1591])).
% 4.14/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.72  
% 4.14/1.72  Inference rules
% 4.14/1.72  ----------------------
% 4.14/1.72  #Ref     : 0
% 4.14/1.72  #Sup     : 299
% 4.14/1.72  #Fact    : 0
% 4.14/1.72  #Define  : 0
% 4.14/1.72  #Split   : 9
% 4.14/1.72  #Chain   : 0
% 4.14/1.72  #Close   : 0
% 4.14/1.72  
% 4.14/1.72  Ordering : KBO
% 4.14/1.72  
% 4.14/1.72  Simplification rules
% 4.14/1.72  ----------------------
% 4.14/1.72  #Subsume      : 19
% 4.14/1.72  #Demod        : 237
% 4.14/1.72  #Tautology    : 80
% 4.14/1.72  #SimpNegUnit  : 121
% 4.14/1.72  #BackRed      : 1
% 4.14/1.72  
% 4.14/1.72  #Partial instantiations: 0
% 4.14/1.72  #Strategies tried      : 1
% 4.14/1.72  
% 4.14/1.72  Timing (in seconds)
% 4.14/1.72  ----------------------
% 4.14/1.72  Preprocessing        : 0.34
% 4.14/1.72  Parsing              : 0.18
% 4.14/1.72  CNF conversion       : 0.03
% 4.14/1.72  Main loop            : 0.58
% 4.14/1.72  Inferencing          : 0.21
% 4.14/1.72  Reduction            : 0.18
% 4.14/1.72  Demodulation         : 0.12
% 4.14/1.72  BG Simplification    : 0.03
% 4.14/1.72  Subsumption          : 0.12
% 4.14/1.72  Abstraction          : 0.03
% 4.14/1.72  MUC search           : 0.00
% 4.14/1.72  Cooper               : 0.00
% 4.14/1.73  Total                : 1.00
% 4.14/1.73  Index Insertion      : 0.00
% 4.14/1.73  Index Deletion       : 0.00
% 4.14/1.73  Index Matching       : 0.00
% 4.14/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------

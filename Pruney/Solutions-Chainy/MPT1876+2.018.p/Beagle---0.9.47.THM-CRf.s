%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:52 EST 2020

% Result     : Theorem 11.34s
% Output     : CNFRefutation 11.39s
% Verified   : 
% Statistics : Number of formulae       :  186 (1045 expanded)
%              Number of leaves         :   50 ( 390 expanded)
%              Depth                    :   23
%              Number of atoms          :  477 (4198 expanded)
%              Number of equality atoms :   26 ( 127 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_subset_1 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m2_subset_1,type,(
    m2_subset_1: ( $i * $i * $i ) > $o )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_263,negated_conjecture,(
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

tff(f_189,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_123,axiom,(
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

tff(f_130,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_168,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_243,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_202,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_231,axiom,(
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

tff(f_154,axiom,(
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

tff(f_107,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_34,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_84,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_80,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1457,plain,(
    ! [A_188,B_189] :
      ( m1_pre_topc('#skF_3'(A_188,B_189),A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | v1_xboole_0(B_189)
      | ~ l1_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1471,plain,
    ( m1_pre_topc('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1457])).

tff(c_1478,plain,
    ( m1_pre_topc('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1471])).

tff(c_1479,plain,(
    m1_pre_topc('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78,c_1478])).

tff(c_1076,plain,(
    ! [A_160,B_161] :
      ( ~ v2_struct_0('#skF_3'(A_160,B_161))
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | v1_xboole_0(B_161)
      | ~ l1_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1087,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1076])).

tff(c_1092,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1087])).

tff(c_1093,plain,(
    ~ v2_struct_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78,c_1092])).

tff(c_1640,plain,(
    ! [A_199,B_200] :
      ( u1_struct_0('#skF_3'(A_199,B_200)) = B_200
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | v1_xboole_0(B_200)
      | ~ l1_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1663,plain,
    ( u1_struct_0('#skF_3'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1640])).

tff(c_1671,plain,
    ( u1_struct_0('#skF_3'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1663])).

tff(c_1672,plain,(
    u1_struct_0('#skF_3'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78,c_1671])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(A_77,B_78)
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_134,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_1930,plain,(
    ! [C_202,A_203,B_204] :
      ( m1_subset_1(C_202,u1_struct_0(A_203))
      | ~ m1_subset_1(C_202,u1_struct_0(B_204))
      | ~ m1_pre_topc(B_204,A_203)
      | v2_struct_0(B_204)
      | ~ l1_pre_topc(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4962,plain,(
    ! [B_279,A_280] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_279)),u1_struct_0(A_280))
      | ~ m1_pre_topc(B_279,A_280)
      | v2_struct_0(B_279)
      | ~ l1_pre_topc(A_280)
      | v2_struct_0(A_280)
      | v1_xboole_0(u1_struct_0(B_279)) ) ),
    inference(resolution,[status(thm)],[c_134,c_1930])).

tff(c_4984,plain,(
    ! [A_280] :
      ( m1_subset_1('#skF_1'('#skF_6'),u1_struct_0(A_280))
      | ~ m1_pre_topc('#skF_3'('#skF_5','#skF_6'),A_280)
      | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
      | ~ l1_pre_topc(A_280)
      | v2_struct_0(A_280)
      | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1672,c_4962])).

tff(c_4993,plain,(
    ! [A_280] :
      ( m1_subset_1('#skF_1'('#skF_6'),u1_struct_0(A_280))
      | ~ m1_pre_topc('#skF_3'('#skF_5','#skF_6'),A_280)
      | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
      | ~ l1_pre_topc(A_280)
      | v2_struct_0(A_280)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_4984])).

tff(c_4994,plain,(
    ! [A_280] :
      ( m1_subset_1('#skF_1'('#skF_6'),u1_struct_0(A_280))
      | ~ m1_pre_topc('#skF_3'('#skF_5','#skF_6'),A_280)
      | ~ l1_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1093,c_4993])).

tff(c_94,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_108,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_88,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_110,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_88])).

tff(c_307,plain,(
    ! [A_100,B_101] :
      ( k6_domain_1(A_100,B_101) = k1_tarski(B_101)
      | ~ m1_subset_1(B_101,A_100)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_326,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_134,c_307])).

tff(c_36,plain,(
    ! [B_30,A_28] :
      ( l1_pre_topc(B_30)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1485,plain,
    ( l1_pre_topc('#skF_3'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1479,c_36])).

tff(c_1492,plain,(
    l1_pre_topc('#skF_3'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1485])).

tff(c_82,plain,(
    v2_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_52,plain,(
    ! [B_45,A_43] :
      ( v2_tdlat_3(B_45)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43)
      | ~ v2_tdlat_3(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1482,plain,
    ( v2_tdlat_3('#skF_3'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1479,c_52])).

tff(c_1488,plain,
    ( v2_tdlat_3('#skF_3'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1482])).

tff(c_1489,plain,(
    v2_tdlat_3('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1488])).

tff(c_44,plain,(
    ! [A_41] :
      ( v2_pre_topc(A_41)
      | ~ v2_tdlat_3(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1496,plain,
    ( v2_pre_topc('#skF_3'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_3'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1489,c_44])).

tff(c_1498,plain,(
    v2_pre_topc('#skF_3'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1492,c_1496])).

tff(c_74,plain,(
    ! [A_61,B_63] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_61),B_63),A_61)
      | ~ m1_subset_1(B_63,u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_1681,plain,(
    ! [B_63] :
      ( v2_tex_2(k6_domain_1('#skF_6',B_63),'#skF_3'('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_3'('#skF_5','#skF_6')))
      | ~ l1_pre_topc('#skF_3'('#skF_5','#skF_6'))
      | ~ v2_pre_topc('#skF_3'('#skF_5','#skF_6'))
      | v2_struct_0('#skF_3'('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1672,c_74])).

tff(c_1703,plain,(
    ! [B_63] :
      ( v2_tex_2(k6_domain_1('#skF_6',B_63),'#skF_3'('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_63,'#skF_6')
      | v2_struct_0('#skF_3'('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_1492,c_1672,c_1681])).

tff(c_1715,plain,(
    ! [B_201] :
      ( v2_tex_2(k6_domain_1('#skF_6',B_201),'#skF_3'('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_201,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1093,c_1703])).

tff(c_1719,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_6')),'#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_1715])).

tff(c_1720,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_6')),'#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1719])).

tff(c_1721,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1720])).

tff(c_1727,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_134,c_1721])).

tff(c_1735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1727])).

tff(c_1737,plain,(
    m1_subset_1('#skF_1'('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1720])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_430,plain,(
    ! [B_110,A_111] :
      ( B_110 = A_111
      | ~ r1_tarski(A_111,B_110)
      | ~ v1_zfmisc_1(B_110)
      | v1_xboole_0(B_110)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_433,plain,(
    ! [A_7,B_8] :
      ( k1_tarski(A_7) = B_8
      | ~ v1_zfmisc_1(B_8)
      | v1_xboole_0(B_8)
      | v1_xboole_0(k1_tarski(A_7))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_430])).

tff(c_754,plain,(
    ! [A_140,B_141] :
      ( k1_tarski(A_140) = B_141
      | ~ v1_zfmisc_1(B_141)
      | v1_xboole_0(B_141)
      | ~ r2_hidden(A_140,B_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_433])).

tff(c_775,plain,(
    ! [A_18,B_19] :
      ( k1_tarski(A_18) = B_19
      | ~ v1_zfmisc_1(B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_26,c_754])).

tff(c_1742,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1737,c_775])).

tff(c_1753,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1742])).

tff(c_1754,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1753])).

tff(c_167,plain,(
    ! [B_91,A_92] :
      ( v1_xboole_0(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_174,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_76,c_167])).

tff(c_178,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_174])).

tff(c_1932,plain,(
    ! [C_202,A_203] :
      ( m1_subset_1(C_202,u1_struct_0(A_203))
      | ~ m1_subset_1(C_202,'#skF_6')
      | ~ m1_pre_topc('#skF_3'('#skF_5','#skF_6'),A_203)
      | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
      | ~ l1_pre_topc(A_203)
      | v2_struct_0(A_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1672,c_1930])).

tff(c_3609,plain,(
    ! [C_245,A_246] :
      ( m1_subset_1(C_245,u1_struct_0(A_246))
      | ~ m1_subset_1(C_245,'#skF_6')
      | ~ m1_pre_topc('#skF_3'('#skF_5','#skF_6'),A_246)
      | ~ l1_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1093,c_1932])).

tff(c_42,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_21521,plain,(
    ! [A_634,C_635] :
      ( k6_domain_1(u1_struct_0(A_634),C_635) = k1_tarski(C_635)
      | v1_xboole_0(u1_struct_0(A_634))
      | ~ m1_subset_1(C_635,'#skF_6')
      | ~ m1_pre_topc('#skF_3'('#skF_5','#skF_6'),A_634)
      | ~ l1_pre_topc(A_634)
      | v2_struct_0(A_634) ) ),
    inference(resolution,[status(thm)],[c_3609,c_42])).

tff(c_21523,plain,(
    ! [C_635] :
      ( k6_domain_1(u1_struct_0('#skF_5'),C_635) = k1_tarski(C_635)
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_635,'#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1479,c_21521])).

tff(c_21526,plain,(
    ! [C_635] :
      ( k6_domain_1(u1_struct_0('#skF_5'),C_635) = k1_tarski(C_635)
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_635,'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_21523])).

tff(c_21528,plain,(
    ! [C_636] :
      ( k6_domain_1(u1_struct_0('#skF_5'),C_636) = k1_tarski(C_636)
      | ~ m1_subset_1(C_636,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_178,c_21526])).

tff(c_21558,plain,(
    ! [C_636] :
      ( v2_tex_2(k1_tarski(C_636),'#skF_5')
      | ~ m1_subset_1(C_636,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_636,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21528,c_74])).

tff(c_21611,plain,(
    ! [C_636] :
      ( v2_tex_2(k1_tarski(C_636),'#skF_5')
      | ~ m1_subset_1(C_636,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_636,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_21558])).

tff(c_21633,plain,(
    ! [C_637] :
      ( v2_tex_2(k1_tarski(C_637),'#skF_5')
      | ~ m1_subset_1(C_637,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_637,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_21611])).

tff(c_21648,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_21633])).

tff(c_21662,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_21648])).

tff(c_21663,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_21662])).

tff(c_21675,plain,
    ( ~ m1_pre_topc('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4994,c_21663])).

tff(c_21697,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1479,c_21675])).

tff(c_21699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_21697])).

tff(c_21700,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_23523,plain,(
    ! [A_777,B_778] :
      ( ~ v2_struct_0('#skF_4'(A_777,B_778))
      | ~ v2_tex_2(B_778,A_777)
      | ~ m1_subset_1(B_778,k1_zfmisc_1(u1_struct_0(A_777)))
      | v1_xboole_0(B_778)
      | ~ l1_pre_topc(A_777)
      | ~ v2_pre_topc(A_777)
      | v2_struct_0(A_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_23552,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_23523])).

tff(c_23563,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_21700,c_23552])).

tff(c_23564,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78,c_23563])).

tff(c_23620,plain,(
    ! [A_786,B_787] :
      ( v1_tdlat_3('#skF_4'(A_786,B_787))
      | ~ v2_tex_2(B_787,A_786)
      | ~ m1_subset_1(B_787,k1_zfmisc_1(u1_struct_0(A_786)))
      | v1_xboole_0(B_787)
      | ~ l1_pre_topc(A_786)
      | ~ v2_pre_topc(A_786)
      | v2_struct_0(A_786) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_23649,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_23620])).

tff(c_23660,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_21700,c_23649])).

tff(c_23661,plain,(
    v1_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78,c_23660])).

tff(c_48,plain,(
    ! [A_42] :
      ( v7_struct_0(A_42)
      | ~ v2_tdlat_3(A_42)
      | ~ v1_tdlat_3(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_21701,plain,(
    ~ v1_zfmisc_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_23757,plain,(
    ! [A_794,B_795] :
      ( u1_struct_0('#skF_4'(A_794,B_795)) = B_795
      | ~ v2_tex_2(B_795,A_794)
      | ~ m1_subset_1(B_795,k1_zfmisc_1(u1_struct_0(A_794)))
      | v1_xboole_0(B_795)
      | ~ l1_pre_topc(A_794)
      | ~ v2_pre_topc(A_794)
      | v2_struct_0(A_794) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_23786,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_23757])).

tff(c_23797,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_21700,c_23786])).

tff(c_23798,plain,(
    u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78,c_23797])).

tff(c_38,plain,(
    ! [A_31] :
      ( v1_zfmisc_1(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | ~ v7_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_23836,plain,
    ( v1_zfmisc_1('#skF_6')
    | ~ l1_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23798,c_38])).

tff(c_23852,plain,
    ( ~ l1_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_21701,c_23836])).

tff(c_23854,plain,(
    ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_23852])).

tff(c_23857,plain,
    ( ~ v2_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_23854])).

tff(c_23860,plain,
    ( ~ v2_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23661,c_23857])).

tff(c_23861,plain,
    ( ~ v2_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_23564,c_23860])).

tff(c_23862,plain,(
    ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_23861])).

tff(c_23967,plain,(
    ! [A_800,B_801] :
      ( m1_pre_topc('#skF_4'(A_800,B_801),A_800)
      | ~ v2_tex_2(B_801,A_800)
      | ~ m1_subset_1(B_801,k1_zfmisc_1(u1_struct_0(A_800)))
      | v1_xboole_0(B_801)
      | ~ l1_pre_topc(A_800)
      | ~ v2_pre_topc(A_800)
      | v2_struct_0(A_800) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_23990,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_23967])).

tff(c_24002,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_21700,c_23990])).

tff(c_24003,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78,c_24002])).

tff(c_24009,plain,
    ( l1_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24003,c_36])).

tff(c_24016,plain,(
    l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_24009])).

tff(c_24018,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23862,c_24016])).

tff(c_24019,plain,
    ( ~ v2_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_23861])).

tff(c_24021,plain,(
    ~ v2_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_24019])).

tff(c_24169,plain,(
    ! [A_809,B_810] :
      ( m1_pre_topc('#skF_4'(A_809,B_810),A_809)
      | ~ v2_tex_2(B_810,A_809)
      | ~ m1_subset_1(B_810,k1_zfmisc_1(u1_struct_0(A_809)))
      | v1_xboole_0(B_810)
      | ~ l1_pre_topc(A_809)
      | ~ v2_pre_topc(A_809)
      | v2_struct_0(A_809) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_24192,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_24169])).

tff(c_24206,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_21700,c_24192])).

tff(c_24207,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78,c_24206])).

tff(c_24210,plain,
    ( v2_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24207,c_52])).

tff(c_24216,plain,
    ( v2_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_24210])).

tff(c_24218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_24021,c_24216])).

tff(c_24219,plain,(
    ~ v2_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_24019])).

tff(c_24020,plain,(
    l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_23861])).

tff(c_24220,plain,(
    v2_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_24019])).

tff(c_24223,plain,
    ( v2_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_24220,c_44])).

tff(c_24226,plain,(
    v2_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24020,c_24223])).

tff(c_24230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24219,c_24226])).

tff(c_24231,plain,(
    ~ l1_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_23852])).

tff(c_24236,plain,(
    ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_24231])).

tff(c_24239,plain,(
    ! [A_812,B_813] :
      ( m1_pre_topc('#skF_4'(A_812,B_813),A_812)
      | ~ v2_tex_2(B_813,A_812)
      | ~ m1_subset_1(B_813,k1_zfmisc_1(u1_struct_0(A_812)))
      | v1_xboole_0(B_813)
      | ~ l1_pre_topc(A_812)
      | ~ v2_pre_topc(A_812)
      | v2_struct_0(A_812) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_24262,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_24239])).

tff(c_24274,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_21700,c_24262])).

tff(c_24275,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78,c_24274])).

tff(c_24281,plain,
    ( l1_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24275,c_36])).

tff(c_24288,plain,(
    l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_24281])).

tff(c_24290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24236,c_24288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:25:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.34/4.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.97  
% 11.39/4.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.97  %$ m2_subset_1 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 11.39/4.97  
% 11.39/4.97  %Foreground sorts:
% 11.39/4.97  
% 11.39/4.97  
% 11.39/4.97  %Background operators:
% 11.39/4.97  
% 11.39/4.97  
% 11.39/4.97  %Foreground operators:
% 11.39/4.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.39/4.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.39/4.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.39/4.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.39/4.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.39/4.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.39/4.97  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 11.39/4.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.39/4.97  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 11.39/4.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.39/4.97  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.39/4.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.39/4.97  tff('#skF_5', type, '#skF_5': $i).
% 11.39/4.97  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 11.39/4.97  tff('#skF_6', type, '#skF_6': $i).
% 11.39/4.97  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 11.39/4.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.39/4.97  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.39/4.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.39/4.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.39/4.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.39/4.97  tff(m2_subset_1, type, m2_subset_1: ($i * $i * $i) > $o).
% 11.39/4.97  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 11.39/4.97  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.39/4.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.39/4.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.39/4.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.39/4.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.39/4.97  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.39/4.97  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 11.39/4.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.39/4.97  
% 11.39/4.99  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.39/4.99  tff(f_263, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 11.39/4.99  tff(f_189, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 11.39/4.99  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.39/4.99  tff(f_60, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 11.39/4.99  tff(f_123, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 11.39/4.99  tff(f_130, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.39/4.99  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.39/4.99  tff(f_168, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 11.39/4.99  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 11.39/4.99  tff(f_243, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 11.39/4.99  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 11.39/4.99  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 11.39/4.99  tff(f_40, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 11.39/4.99  tff(f_202, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 11.39/4.99  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.39/4.99  tff(f_231, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 11.39/4.99  tff(f_154, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 11.39/4.99  tff(f_107, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 11.39/4.99  tff(c_34, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.39/4.99  tff(c_86, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.39/4.99  tff(c_78, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.39/4.99  tff(c_84, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.39/4.99  tff(c_80, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.39/4.99  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.39/4.99  tff(c_1457, plain, (![A_188, B_189]: (m1_pre_topc('#skF_3'(A_188, B_189), A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | v1_xboole_0(B_189) | ~l1_pre_topc(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.39/4.99  tff(c_1471, plain, (m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1457])).
% 11.39/4.99  tff(c_1478, plain, (m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1471])).
% 11.39/4.99  tff(c_1479, plain, (m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_78, c_1478])).
% 11.39/4.99  tff(c_1076, plain, (![A_160, B_161]: (~v2_struct_0('#skF_3'(A_160, B_161)) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | v1_xboole_0(B_161) | ~l1_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.39/4.99  tff(c_1087, plain, (~v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1076])).
% 11.39/4.99  tff(c_1092, plain, (~v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1087])).
% 11.39/4.99  tff(c_1093, plain, (~v2_struct_0('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_78, c_1092])).
% 11.39/4.99  tff(c_1640, plain, (![A_199, B_200]: (u1_struct_0('#skF_3'(A_199, B_200))=B_200 | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | v1_xboole_0(B_200) | ~l1_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.39/4.99  tff(c_1663, plain, (u1_struct_0('#skF_3'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1640])).
% 11.39/4.99  tff(c_1671, plain, (u1_struct_0('#skF_3'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1663])).
% 11.39/4.99  tff(c_1672, plain, (u1_struct_0('#skF_3'('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_86, c_78, c_1671])).
% 11.39/4.99  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.39/4.99  tff(c_130, plain, (![A_77, B_78]: (m1_subset_1(A_77, B_78) | ~r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.39/4.99  tff(c_134, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_130])).
% 11.39/4.99  tff(c_1930, plain, (![C_202, A_203, B_204]: (m1_subset_1(C_202, u1_struct_0(A_203)) | ~m1_subset_1(C_202, u1_struct_0(B_204)) | ~m1_pre_topc(B_204, A_203) | v2_struct_0(B_204) | ~l1_pre_topc(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.39/4.99  tff(c_4962, plain, (![B_279, A_280]: (m1_subset_1('#skF_1'(u1_struct_0(B_279)), u1_struct_0(A_280)) | ~m1_pre_topc(B_279, A_280) | v2_struct_0(B_279) | ~l1_pre_topc(A_280) | v2_struct_0(A_280) | v1_xboole_0(u1_struct_0(B_279)))), inference(resolution, [status(thm)], [c_134, c_1930])).
% 11.39/4.99  tff(c_4984, plain, (![A_280]: (m1_subset_1('#skF_1'('#skF_6'), u1_struct_0(A_280)) | ~m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), A_280) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc(A_280) | v2_struct_0(A_280) | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_1672, c_4962])).
% 11.39/4.99  tff(c_4993, plain, (![A_280]: (m1_subset_1('#skF_1'('#skF_6'), u1_struct_0(A_280)) | ~m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), A_280) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc(A_280) | v2_struct_0(A_280) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_4984])).
% 11.39/4.99  tff(c_4994, plain, (![A_280]: (m1_subset_1('#skF_1'('#skF_6'), u1_struct_0(A_280)) | ~m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), A_280) | ~l1_pre_topc(A_280) | v2_struct_0(A_280))), inference(negUnitSimplification, [status(thm)], [c_78, c_1093, c_4993])).
% 11.39/4.99  tff(c_94, plain, (v2_tex_2('#skF_6', '#skF_5') | v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.39/4.99  tff(c_108, plain, (v1_zfmisc_1('#skF_6')), inference(splitLeft, [status(thm)], [c_94])).
% 11.39/4.99  tff(c_88, plain, (~v1_zfmisc_1('#skF_6') | ~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.39/4.99  tff(c_110, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_88])).
% 11.39/4.99  tff(c_307, plain, (![A_100, B_101]: (k6_domain_1(A_100, B_101)=k1_tarski(B_101) | ~m1_subset_1(B_101, A_100) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.39/4.99  tff(c_326, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_134, c_307])).
% 11.39/4.99  tff(c_36, plain, (![B_30, A_28]: (l1_pre_topc(B_30) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.39/4.99  tff(c_1485, plain, (l1_pre_topc('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1479, c_36])).
% 11.39/4.99  tff(c_1492, plain, (l1_pre_topc('#skF_3'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1485])).
% 11.39/4.99  tff(c_82, plain, (v2_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.39/4.99  tff(c_52, plain, (![B_45, A_43]: (v2_tdlat_3(B_45) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43) | ~v2_tdlat_3(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.39/4.99  tff(c_1482, plain, (v2_tdlat_3('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1479, c_52])).
% 11.39/4.99  tff(c_1488, plain, (v2_tdlat_3('#skF_3'('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1482])).
% 11.39/4.99  tff(c_1489, plain, (v2_tdlat_3('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_1488])).
% 11.39/4.99  tff(c_44, plain, (![A_41]: (v2_pre_topc(A_41) | ~v2_tdlat_3(A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.39/4.99  tff(c_1496, plain, (v2_pre_topc('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_3'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1489, c_44])).
% 11.39/4.99  tff(c_1498, plain, (v2_pre_topc('#skF_3'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1492, c_1496])).
% 11.39/4.99  tff(c_74, plain, (![A_61, B_63]: (v2_tex_2(k6_domain_1(u1_struct_0(A_61), B_63), A_61) | ~m1_subset_1(B_63, u1_struct_0(A_61)) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.39/4.99  tff(c_1681, plain, (![B_63]: (v2_tex_2(k6_domain_1('#skF_6', B_63), '#skF_3'('#skF_5', '#skF_6')) | ~m1_subset_1(B_63, u1_struct_0('#skF_3'('#skF_5', '#skF_6'))) | ~l1_pre_topc('#skF_3'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_3'('#skF_5', '#skF_6')) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1672, c_74])).
% 11.39/4.99  tff(c_1703, plain, (![B_63]: (v2_tex_2(k6_domain_1('#skF_6', B_63), '#skF_3'('#skF_5', '#skF_6')) | ~m1_subset_1(B_63, '#skF_6') | v2_struct_0('#skF_3'('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_1492, c_1672, c_1681])).
% 11.39/4.99  tff(c_1715, plain, (![B_201]: (v2_tex_2(k6_domain_1('#skF_6', B_201), '#skF_3'('#skF_5', '#skF_6')) | ~m1_subset_1(B_201, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1093, c_1703])).
% 11.39/4.99  tff(c_1719, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_6')), '#skF_3'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6'), '#skF_6') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_326, c_1715])).
% 11.39/4.99  tff(c_1720, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_6')), '#skF_3'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_1719])).
% 11.39/4.99  tff(c_1721, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1720])).
% 11.39/4.99  tff(c_1727, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_134, c_1721])).
% 11.39/4.99  tff(c_1735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1727])).
% 11.39/4.99  tff(c_1737, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_1720])).
% 11.39/4.99  tff(c_26, plain, (![A_18, B_19]: (r2_hidden(A_18, B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.39/4.99  tff(c_8, plain, (![A_6]: (~v1_xboole_0(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.39/4.99  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.39/4.99  tff(c_430, plain, (![B_110, A_111]: (B_110=A_111 | ~r1_tarski(A_111, B_110) | ~v1_zfmisc_1(B_110) | v1_xboole_0(B_110) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_202])).
% 11.39/4.99  tff(c_433, plain, (![A_7, B_8]: (k1_tarski(A_7)=B_8 | ~v1_zfmisc_1(B_8) | v1_xboole_0(B_8) | v1_xboole_0(k1_tarski(A_7)) | ~r2_hidden(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_430])).
% 11.39/4.99  tff(c_754, plain, (![A_140, B_141]: (k1_tarski(A_140)=B_141 | ~v1_zfmisc_1(B_141) | v1_xboole_0(B_141) | ~r2_hidden(A_140, B_141))), inference(negUnitSimplification, [status(thm)], [c_8, c_433])).
% 11.39/4.99  tff(c_775, plain, (![A_18, B_19]: (k1_tarski(A_18)=B_19 | ~v1_zfmisc_1(B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(resolution, [status(thm)], [c_26, c_754])).
% 11.39/4.99  tff(c_1742, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1737, c_775])).
% 11.39/4.99  tff(c_1753, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1742])).
% 11.39/4.99  tff(c_1754, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_78, c_1753])).
% 11.39/4.99  tff(c_167, plain, (![B_91, A_92]: (v1_xboole_0(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.39/4.99  tff(c_174, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_167])).
% 11.39/4.99  tff(c_178, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_174])).
% 11.39/4.99  tff(c_1932, plain, (![C_202, A_203]: (m1_subset_1(C_202, u1_struct_0(A_203)) | ~m1_subset_1(C_202, '#skF_6') | ~m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), A_203) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc(A_203) | v2_struct_0(A_203))), inference(superposition, [status(thm), theory('equality')], [c_1672, c_1930])).
% 11.39/4.99  tff(c_3609, plain, (![C_245, A_246]: (m1_subset_1(C_245, u1_struct_0(A_246)) | ~m1_subset_1(C_245, '#skF_6') | ~m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), A_246) | ~l1_pre_topc(A_246) | v2_struct_0(A_246))), inference(negUnitSimplification, [status(thm)], [c_1093, c_1932])).
% 11.39/4.99  tff(c_42, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.39/4.99  tff(c_21521, plain, (![A_634, C_635]: (k6_domain_1(u1_struct_0(A_634), C_635)=k1_tarski(C_635) | v1_xboole_0(u1_struct_0(A_634)) | ~m1_subset_1(C_635, '#skF_6') | ~m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), A_634) | ~l1_pre_topc(A_634) | v2_struct_0(A_634))), inference(resolution, [status(thm)], [c_3609, c_42])).
% 11.39/4.99  tff(c_21523, plain, (![C_635]: (k6_domain_1(u1_struct_0('#skF_5'), C_635)=k1_tarski(C_635) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_635, '#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1479, c_21521])).
% 11.39/4.99  tff(c_21526, plain, (![C_635]: (k6_domain_1(u1_struct_0('#skF_5'), C_635)=k1_tarski(C_635) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_635, '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_21523])).
% 11.39/4.99  tff(c_21528, plain, (![C_636]: (k6_domain_1(u1_struct_0('#skF_5'), C_636)=k1_tarski(C_636) | ~m1_subset_1(C_636, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_178, c_21526])).
% 11.39/4.99  tff(c_21558, plain, (![C_636]: (v2_tex_2(k1_tarski(C_636), '#skF_5') | ~m1_subset_1(C_636, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(C_636, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_21528, c_74])).
% 11.39/4.99  tff(c_21611, plain, (![C_636]: (v2_tex_2(k1_tarski(C_636), '#skF_5') | ~m1_subset_1(C_636, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_636, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_21558])).
% 11.39/4.99  tff(c_21633, plain, (![C_637]: (v2_tex_2(k1_tarski(C_637), '#skF_5') | ~m1_subset_1(C_637, u1_struct_0('#skF_5')) | ~m1_subset_1(C_637, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_21611])).
% 11.39/4.99  tff(c_21648, plain, (v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_6'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1754, c_21633])).
% 11.39/4.99  tff(c_21662, plain, (v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_21648])).
% 11.39/4.99  tff(c_21663, plain, (~m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_110, c_21662])).
% 11.39/4.99  tff(c_21675, plain, (~m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4994, c_21663])).
% 11.39/4.99  tff(c_21697, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1479, c_21675])).
% 11.39/4.99  tff(c_21699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_21697])).
% 11.39/4.99  tff(c_21700, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_94])).
% 11.39/4.99  tff(c_23523, plain, (![A_777, B_778]: (~v2_struct_0('#skF_4'(A_777, B_778)) | ~v2_tex_2(B_778, A_777) | ~m1_subset_1(B_778, k1_zfmisc_1(u1_struct_0(A_777))) | v1_xboole_0(B_778) | ~l1_pre_topc(A_777) | ~v2_pre_topc(A_777) | v2_struct_0(A_777))), inference(cnfTransformation, [status(thm)], [f_231])).
% 11.39/4.99  tff(c_23552, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_23523])).
% 11.39/4.99  tff(c_23563, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_21700, c_23552])).
% 11.39/4.99  tff(c_23564, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_78, c_23563])).
% 11.39/4.99  tff(c_23620, plain, (![A_786, B_787]: (v1_tdlat_3('#skF_4'(A_786, B_787)) | ~v2_tex_2(B_787, A_786) | ~m1_subset_1(B_787, k1_zfmisc_1(u1_struct_0(A_786))) | v1_xboole_0(B_787) | ~l1_pre_topc(A_786) | ~v2_pre_topc(A_786) | v2_struct_0(A_786))), inference(cnfTransformation, [status(thm)], [f_231])).
% 11.39/4.99  tff(c_23649, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_23620])).
% 11.39/4.99  tff(c_23660, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_21700, c_23649])).
% 11.39/4.99  tff(c_23661, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_78, c_23660])).
% 11.39/4.99  tff(c_48, plain, (![A_42]: (v7_struct_0(A_42) | ~v2_tdlat_3(A_42) | ~v1_tdlat_3(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.39/4.99  tff(c_21701, plain, (~v1_zfmisc_1('#skF_6')), inference(splitRight, [status(thm)], [c_94])).
% 11.39/4.99  tff(c_23757, plain, (![A_794, B_795]: (u1_struct_0('#skF_4'(A_794, B_795))=B_795 | ~v2_tex_2(B_795, A_794) | ~m1_subset_1(B_795, k1_zfmisc_1(u1_struct_0(A_794))) | v1_xboole_0(B_795) | ~l1_pre_topc(A_794) | ~v2_pre_topc(A_794) | v2_struct_0(A_794))), inference(cnfTransformation, [status(thm)], [f_231])).
% 11.39/4.99  tff(c_23786, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_23757])).
% 11.39/4.99  tff(c_23797, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_21700, c_23786])).
% 11.39/4.99  tff(c_23798, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_86, c_78, c_23797])).
% 11.39/4.99  tff(c_38, plain, (![A_31]: (v1_zfmisc_1(u1_struct_0(A_31)) | ~l1_struct_0(A_31) | ~v7_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.39/4.99  tff(c_23836, plain, (v1_zfmisc_1('#skF_6') | ~l1_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_23798, c_38])).
% 11.39/4.99  tff(c_23852, plain, (~l1_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_21701, c_23836])).
% 11.39/4.99  tff(c_23854, plain, (~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_23852])).
% 11.39/4.99  tff(c_23857, plain, (~v2_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_23854])).
% 11.39/4.99  tff(c_23860, plain, (~v2_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_23661, c_23857])).
% 11.39/4.99  tff(c_23861, plain, (~v2_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_23564, c_23860])).
% 11.39/4.99  tff(c_23862, plain, (~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_23861])).
% 11.39/4.99  tff(c_23967, plain, (![A_800, B_801]: (m1_pre_topc('#skF_4'(A_800, B_801), A_800) | ~v2_tex_2(B_801, A_800) | ~m1_subset_1(B_801, k1_zfmisc_1(u1_struct_0(A_800))) | v1_xboole_0(B_801) | ~l1_pre_topc(A_800) | ~v2_pre_topc(A_800) | v2_struct_0(A_800))), inference(cnfTransformation, [status(thm)], [f_231])).
% 11.39/4.99  tff(c_23990, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_23967])).
% 11.39/4.99  tff(c_24002, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_21700, c_23990])).
% 11.39/4.99  tff(c_24003, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_78, c_24002])).
% 11.39/4.99  tff(c_24009, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24003, c_36])).
% 11.39/4.99  tff(c_24016, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_24009])).
% 11.39/4.99  tff(c_24018, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23862, c_24016])).
% 11.39/4.99  tff(c_24019, plain, (~v2_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~v2_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_23861])).
% 11.39/4.99  tff(c_24021, plain, (~v2_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_24019])).
% 11.39/4.99  tff(c_24169, plain, (![A_809, B_810]: (m1_pre_topc('#skF_4'(A_809, B_810), A_809) | ~v2_tex_2(B_810, A_809) | ~m1_subset_1(B_810, k1_zfmisc_1(u1_struct_0(A_809))) | v1_xboole_0(B_810) | ~l1_pre_topc(A_809) | ~v2_pre_topc(A_809) | v2_struct_0(A_809))), inference(cnfTransformation, [status(thm)], [f_231])).
% 11.39/4.99  tff(c_24192, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_24169])).
% 11.39/4.99  tff(c_24206, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_21700, c_24192])).
% 11.39/4.99  tff(c_24207, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_78, c_24206])).
% 11.39/4.99  tff(c_24210, plain, (v2_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24207, c_52])).
% 11.39/4.99  tff(c_24216, plain, (v2_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_24210])).
% 11.39/4.99  tff(c_24218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_24021, c_24216])).
% 11.39/4.99  tff(c_24219, plain, (~v2_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_24019])).
% 11.39/4.99  tff(c_24020, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_23861])).
% 11.39/4.99  tff(c_24220, plain, (v2_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_24019])).
% 11.39/4.99  tff(c_24223, plain, (v2_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_24220, c_44])).
% 11.39/4.99  tff(c_24226, plain, (v2_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_24020, c_24223])).
% 11.39/4.99  tff(c_24230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24219, c_24226])).
% 11.39/4.99  tff(c_24231, plain, (~l1_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_23852])).
% 11.39/4.99  tff(c_24236, plain, (~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_24231])).
% 11.39/4.99  tff(c_24239, plain, (![A_812, B_813]: (m1_pre_topc('#skF_4'(A_812, B_813), A_812) | ~v2_tex_2(B_813, A_812) | ~m1_subset_1(B_813, k1_zfmisc_1(u1_struct_0(A_812))) | v1_xboole_0(B_813) | ~l1_pre_topc(A_812) | ~v2_pre_topc(A_812) | v2_struct_0(A_812))), inference(cnfTransformation, [status(thm)], [f_231])).
% 11.39/4.99  tff(c_24262, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_24239])).
% 11.39/4.99  tff(c_24274, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_21700, c_24262])).
% 11.39/4.99  tff(c_24275, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_78, c_24274])).
% 11.39/4.99  tff(c_24281, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24275, c_36])).
% 11.39/4.99  tff(c_24288, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_24281])).
% 11.39/4.99  tff(c_24290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24236, c_24288])).
% 11.39/4.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.99  
% 11.39/4.99  Inference rules
% 11.39/4.99  ----------------------
% 11.39/4.99  #Ref     : 0
% 11.39/4.99  #Sup     : 5183
% 11.39/4.99  #Fact    : 0
% 11.39/4.99  #Define  : 0
% 11.39/4.99  #Split   : 20
% 11.39/4.99  #Chain   : 0
% 11.39/4.99  #Close   : 0
% 11.39/4.99  
% 11.39/4.99  Ordering : KBO
% 11.39/4.99  
% 11.39/4.99  Simplification rules
% 11.39/4.99  ----------------------
% 11.39/4.99  #Subsume      : 2071
% 11.39/4.99  #Demod        : 4444
% 11.39/4.99  #Tautology    : 1384
% 11.39/4.99  #SimpNegUnit  : 1592
% 11.39/4.99  #BackRed      : 0
% 11.39/4.99  
% 11.39/4.99  #Partial instantiations: 0
% 11.39/4.99  #Strategies tried      : 1
% 11.39/4.99  
% 11.39/4.99  Timing (in seconds)
% 11.39/4.99  ----------------------
% 11.39/5.00  Preprocessing        : 0.38
% 11.39/5.00  Parsing              : 0.21
% 11.39/5.00  CNF conversion       : 0.03
% 11.39/5.00  Main loop            : 3.75
% 11.39/5.00  Inferencing          : 0.87
% 11.39/5.00  Reduction            : 1.23
% 11.39/5.00  Demodulation         : 0.85
% 11.39/5.00  BG Simplification    : 0.08
% 11.39/5.00  Subsumption          : 1.38
% 11.39/5.00  Abstraction          : 0.15
% 11.39/5.00  MUC search           : 0.00
% 11.39/5.00  Cooper               : 0.00
% 11.39/5.00  Total                : 4.19
% 11.39/5.00  Index Insertion      : 0.00
% 11.39/5.00  Index Deletion       : 0.00
% 11.39/5.00  Index Matching       : 0.00
% 11.39/5.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------

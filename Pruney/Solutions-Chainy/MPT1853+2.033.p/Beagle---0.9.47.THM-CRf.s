%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:04 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 315 expanded)
%              Number of leaves         :   41 ( 119 expanded)
%              Depth                    :   14
%              Number of atoms          :  265 ( 834 expanded)
%              Number of equality atoms :   14 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k4_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_195,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_130,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_158,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_184,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ~ ( u1_struct_0(B) = u1_struct_0(A)
              & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_206,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_16,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_74,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_tex_2(k1_tex_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_93,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,
    ( v1_tex_2(k1_tex_2('#skF_4','#skF_5'),'#skF_4')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_106,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_80])).

tff(c_165,plain,(
    ! [A_106,B_107] :
      ( ~ v1_zfmisc_1(A_106)
      | ~ v1_subset_1(k6_domain_1(A_106,B_107),A_106)
      | ~ m1_subset_1(B_107,A_106)
      | v1_xboole_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_171,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_106,c_165])).

tff(c_175,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_171])).

tff(c_176,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_192,plain,(
    ! [A_113,B_114] :
      ( m1_pre_topc(k1_tex_2(A_113,B_114),A_113)
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_194,plain,
    ( m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_192])).

tff(c_197,plain,
    ( m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_194])).

tff(c_198,plain,(
    m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_197])).

tff(c_353,plain,(
    ! [A_127,B_128] :
      ( m1_subset_1('#skF_2'(A_127,B_128),k1_zfmisc_1(u1_struct_0(A_127)))
      | v1_tex_2(B_128,A_127)
      | ~ m1_pre_topc(B_128,A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    ! [B_43,A_42] :
      ( v1_subset_1(B_43,A_42)
      | B_43 = A_42
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_581,plain,(
    ! [A_151,B_152] :
      ( v1_subset_1('#skF_2'(A_151,B_152),u1_struct_0(A_151))
      | u1_struct_0(A_151) = '#skF_2'(A_151,B_152)
      | v1_tex_2(B_152,A_151)
      | ~ m1_pre_topc(B_152,A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_353,c_38])).

tff(c_32,plain,(
    ! [A_32,B_38] :
      ( ~ v1_subset_1('#skF_2'(A_32,B_38),u1_struct_0(A_32))
      | v1_tex_2(B_38,A_32)
      | ~ m1_pre_topc(B_38,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_597,plain,(
    ! [A_153,B_154] :
      ( u1_struct_0(A_153) = '#skF_2'(A_153,B_154)
      | v1_tex_2(B_154,A_153)
      | ~ m1_pre_topc(B_154,A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(resolution,[status(thm)],[c_581,c_32])).

tff(c_611,plain,
    ( '#skF_2'('#skF_4',k1_tex_2('#skF_4','#skF_5')) = u1_struct_0('#skF_4')
    | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_597,c_93])).

tff(c_617,plain,(
    '#skF_2'('#skF_4',k1_tex_2('#skF_4','#skF_5')) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_198,c_611])).

tff(c_18,plain,(
    ! [B_22,A_20] :
      ( l1_pre_topc(B_22)
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_201,plain,
    ( l1_pre_topc(k1_tex_2('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_198,c_18])).

tff(c_204,plain,(
    l1_pre_topc(k1_tex_2('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_201])).

tff(c_147,plain,(
    ! [A_98,B_99] :
      ( v7_struct_0(k1_tex_2(A_98,B_99))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_150,plain,
    ( v7_struct_0(k1_tex_2('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_147])).

tff(c_153,plain,
    ( v7_struct_0(k1_tex_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_150])).

tff(c_154,plain,(
    v7_struct_0(k1_tex_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_153])).

tff(c_205,plain,(
    ! [B_115,A_116] :
      ( u1_struct_0(B_115) = '#skF_2'(A_116,B_115)
      | v1_tex_2(B_115,A_116)
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_215,plain,
    ( u1_struct_0(k1_tex_2('#skF_4','#skF_5')) = '#skF_2'('#skF_4',k1_tex_2('#skF_4','#skF_5'))
    | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_205,c_93])).

tff(c_220,plain,(
    u1_struct_0(k1_tex_2('#skF_4','#skF_5')) = '#skF_2'('#skF_4',k1_tex_2('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_198,c_215])).

tff(c_22,plain,(
    ! [A_24] :
      ( v1_zfmisc_1(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | ~ v7_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_251,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_4',k1_tex_2('#skF_4','#skF_5')))
    | ~ l1_struct_0(k1_tex_2('#skF_4','#skF_5'))
    | ~ v7_struct_0(k1_tex_2('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_22])).

tff(c_280,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_4',k1_tex_2('#skF_4','#skF_5')))
    | ~ l1_struct_0(k1_tex_2('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_251])).

tff(c_283,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_286,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_283])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_286])).

tff(c_291,plain,(
    v1_zfmisc_1('#skF_2'('#skF_4',k1_tex_2('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_627,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_291])).

tff(c_630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_627])).

tff(c_631,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_20,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_637,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_631,c_20])).

tff(c_643,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_637])).

tff(c_646,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_643])).

tff(c_650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_646])).

tff(c_652,plain,(
    v1_tex_2(k1_tex_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_715,plain,(
    ! [B_190,A_191] :
      ( ~ v1_tex_2(B_190,A_191)
      | u1_struct_0(B_190) != u1_struct_0(A_191)
      | ~ m1_pre_topc(B_190,A_191)
      | ~ l1_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_718,plain,
    ( u1_struct_0(k1_tex_2('#skF_4','#skF_5')) != u1_struct_0('#skF_4')
    | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_652,c_715])).

tff(c_721,plain,
    ( u1_struct_0(k1_tex_2('#skF_4','#skF_5')) != u1_struct_0('#skF_4')
    | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_718])).

tff(c_722,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_721])).

tff(c_790,plain,(
    ! [A_207,B_208] :
      ( m1_pre_topc(k1_tex_2(A_207,B_208),A_207)
      | ~ m1_subset_1(B_208,u1_struct_0(A_207))
      | ~ l1_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_792,plain,
    ( m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_790])).

tff(c_795,plain,
    ( m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_792])).

tff(c_797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_722,c_795])).

tff(c_799,plain,(
    m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_721])).

tff(c_802,plain,
    ( l1_pre_topc(k1_tex_2('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_799,c_18])).

tff(c_805,plain,(
    l1_pre_topc(k1_tex_2('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_802])).

tff(c_699,plain,(
    ! [A_186,B_187] :
      ( ~ v2_struct_0(k1_tex_2(A_186,B_187))
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l1_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_702,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_699])).

tff(c_705,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_702])).

tff(c_706,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_705])).

tff(c_815,plain,(
    ! [A_213,B_214] :
      ( v1_subset_1(k6_domain_1(A_213,B_214),A_213)
      | ~ m1_subset_1(B_214,A_213)
      | v1_zfmisc_1(A_213)
      | v1_xboole_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_651,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_821,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_zfmisc_1(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_815,c_651])).

tff(c_825,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_821])).

tff(c_826,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_825])).

tff(c_831,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_826,c_20])).

tff(c_837,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_831])).

tff(c_840,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_837])).

tff(c_844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_840])).

tff(c_846,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_825])).

tff(c_845,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_825])).

tff(c_24,plain,(
    ! [B_27,A_25] :
      ( m1_subset_1(u1_struct_0(B_27),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_978,plain,(
    ! [B_234,A_235] :
      ( v1_subset_1(u1_struct_0(B_234),u1_struct_0(A_235))
      | ~ m1_subset_1(u1_struct_0(B_234),k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ v1_tex_2(B_234,A_235)
      | ~ m1_pre_topc(B_234,A_235)
      | ~ l1_pre_topc(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_988,plain,(
    ! [B_27,A_25] :
      ( v1_subset_1(u1_struct_0(B_27),u1_struct_0(A_25))
      | ~ v1_tex_2(B_27,A_25)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_24,c_978])).

tff(c_847,plain,(
    ! [B_215,A_216] :
      ( ~ v1_subset_1(B_215,A_216)
      | v1_xboole_0(B_215)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(A_216))
      | ~ v1_zfmisc_1(A_216)
      | v1_xboole_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1031,plain,(
    ! [B_249,A_250] :
      ( ~ v1_subset_1(u1_struct_0(B_249),u1_struct_0(A_250))
      | v1_xboole_0(u1_struct_0(B_249))
      | ~ v1_zfmisc_1(u1_struct_0(A_250))
      | v1_xboole_0(u1_struct_0(A_250))
      | ~ m1_pre_topc(B_249,A_250)
      | ~ l1_pre_topc(A_250) ) ),
    inference(resolution,[status(thm)],[c_24,c_847])).

tff(c_1046,plain,(
    ! [B_251,A_252] :
      ( v1_xboole_0(u1_struct_0(B_251))
      | ~ v1_zfmisc_1(u1_struct_0(A_252))
      | v1_xboole_0(u1_struct_0(A_252))
      | ~ v1_tex_2(B_251,A_252)
      | ~ m1_pre_topc(B_251,A_252)
      | ~ l1_pre_topc(A_252) ) ),
    inference(resolution,[status(thm)],[c_988,c_1031])).

tff(c_1050,plain,(
    ! [B_251] :
      ( v1_xboole_0(u1_struct_0(B_251))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ v1_tex_2(B_251,'#skF_4')
      | ~ m1_pre_topc(B_251,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_845,c_1046])).

tff(c_1058,plain,(
    ! [B_251] :
      ( v1_xboole_0(u1_struct_0(B_251))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ v1_tex_2(B_251,'#skF_4')
      | ~ m1_pre_topc(B_251,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1050])).

tff(c_1062,plain,(
    ! [B_253] :
      ( v1_xboole_0(u1_struct_0(B_253))
      | ~ v1_tex_2(B_253,'#skF_4')
      | ~ m1_pre_topc(B_253,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_846,c_1058])).

tff(c_1087,plain,(
    ! [B_254] :
      ( ~ l1_struct_0(B_254)
      | v2_struct_0(B_254)
      | ~ v1_tex_2(B_254,'#skF_4')
      | ~ m1_pre_topc(B_254,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1062,c_20])).

tff(c_1094,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_4','#skF_5'))
    | v2_struct_0(k1_tex_2('#skF_4','#skF_5'))
    | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_652,c_1087])).

tff(c_1100,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_4','#skF_5'))
    | v2_struct_0(k1_tex_2('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_1094])).

tff(c_1101,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_706,c_1100])).

tff(c_1104,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_1101])).

tff(c_1108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_1104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n012.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 15:40:37 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.54  
% 3.83/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.55  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k4_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 3.83/1.55  
% 3.83/1.55  %Foreground sorts:
% 3.83/1.55  
% 3.83/1.55  
% 3.83/1.55  %Background operators:
% 3.83/1.55  
% 3.83/1.55  
% 3.83/1.55  %Foreground operators:
% 3.83/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.83/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.83/1.55  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.83/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.83/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.83/1.55  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.83/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.55  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.83/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.83/1.55  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.83/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.83/1.55  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.83/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.83/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.83/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.55  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.83/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.83/1.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.83/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.83/1.55  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.83/1.55  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.83/1.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.83/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.83/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.83/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.83/1.55  
% 3.83/1.57  tff(f_219, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 3.83/1.57  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.83/1.57  tff(f_195, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.83/1.57  tff(f_144, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.83/1.57  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 3.83/1.57  tff(f_130, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.83/1.57  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.83/1.57  tff(f_158, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.83/1.57  tff(f_84, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.83/1.57  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.83/1.57  tff(f_184, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 3.83/1.57  tff(f_206, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 3.83/1.57  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.83/1.57  tff(f_109, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.83/1.57  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.83/1.57  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.83/1.57  tff(c_16, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.83/1.57  tff(c_68, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.83/1.57  tff(c_74, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4')) | ~v1_tex_2(k1_tex_2('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.83/1.57  tff(c_93, plain, (~v1_tex_2(k1_tex_2('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_74])).
% 3.83/1.57  tff(c_80, plain, (v1_tex_2(k1_tex_2('#skF_4', '#skF_5'), '#skF_4') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.83/1.57  tff(c_106, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_93, c_80])).
% 3.83/1.57  tff(c_165, plain, (![A_106, B_107]: (~v1_zfmisc_1(A_106) | ~v1_subset_1(k6_domain_1(A_106, B_107), A_106) | ~m1_subset_1(B_107, A_106) | v1_xboole_0(A_106))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.83/1.57  tff(c_171, plain, (~v1_zfmisc_1(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_106, c_165])).
% 3.83/1.57  tff(c_175, plain, (~v1_zfmisc_1(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_171])).
% 3.83/1.57  tff(c_176, plain, (~v1_zfmisc_1(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_175])).
% 3.83/1.57  tff(c_192, plain, (![A_113, B_114]: (m1_pre_topc(k1_tex_2(A_113, B_114), A_113) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.83/1.57  tff(c_194, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_192])).
% 3.83/1.57  tff(c_197, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_194])).
% 3.83/1.57  tff(c_198, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_197])).
% 3.83/1.57  tff(c_353, plain, (![A_127, B_128]: (m1_subset_1('#skF_2'(A_127, B_128), k1_zfmisc_1(u1_struct_0(A_127))) | v1_tex_2(B_128, A_127) | ~m1_pre_topc(B_128, A_127) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.83/1.57  tff(c_38, plain, (![B_43, A_42]: (v1_subset_1(B_43, A_42) | B_43=A_42 | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.83/1.57  tff(c_581, plain, (![A_151, B_152]: (v1_subset_1('#skF_2'(A_151, B_152), u1_struct_0(A_151)) | u1_struct_0(A_151)='#skF_2'(A_151, B_152) | v1_tex_2(B_152, A_151) | ~m1_pre_topc(B_152, A_151) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_353, c_38])).
% 3.83/1.57  tff(c_32, plain, (![A_32, B_38]: (~v1_subset_1('#skF_2'(A_32, B_38), u1_struct_0(A_32)) | v1_tex_2(B_38, A_32) | ~m1_pre_topc(B_38, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.83/1.57  tff(c_597, plain, (![A_153, B_154]: (u1_struct_0(A_153)='#skF_2'(A_153, B_154) | v1_tex_2(B_154, A_153) | ~m1_pre_topc(B_154, A_153) | ~l1_pre_topc(A_153))), inference(resolution, [status(thm)], [c_581, c_32])).
% 3.83/1.57  tff(c_611, plain, ('#skF_2'('#skF_4', k1_tex_2('#skF_4', '#skF_5'))=u1_struct_0('#skF_4') | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_597, c_93])).
% 3.83/1.57  tff(c_617, plain, ('#skF_2'('#skF_4', k1_tex_2('#skF_4', '#skF_5'))=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_198, c_611])).
% 3.83/1.57  tff(c_18, plain, (![B_22, A_20]: (l1_pre_topc(B_22) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.83/1.57  tff(c_201, plain, (l1_pre_topc(k1_tex_2('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_198, c_18])).
% 3.83/1.57  tff(c_204, plain, (l1_pre_topc(k1_tex_2('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_201])).
% 3.83/1.57  tff(c_147, plain, (![A_98, B_99]: (v7_struct_0(k1_tex_2(A_98, B_99)) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l1_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.83/1.57  tff(c_150, plain, (v7_struct_0(k1_tex_2('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_147])).
% 3.83/1.57  tff(c_153, plain, (v7_struct_0(k1_tex_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_150])).
% 3.83/1.57  tff(c_154, plain, (v7_struct_0(k1_tex_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_153])).
% 3.83/1.57  tff(c_205, plain, (![B_115, A_116]: (u1_struct_0(B_115)='#skF_2'(A_116, B_115) | v1_tex_2(B_115, A_116) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.83/1.57  tff(c_215, plain, (u1_struct_0(k1_tex_2('#skF_4', '#skF_5'))='#skF_2'('#skF_4', k1_tex_2('#skF_4', '#skF_5')) | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_205, c_93])).
% 3.83/1.57  tff(c_220, plain, (u1_struct_0(k1_tex_2('#skF_4', '#skF_5'))='#skF_2'('#skF_4', k1_tex_2('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_198, c_215])).
% 3.83/1.57  tff(c_22, plain, (![A_24]: (v1_zfmisc_1(u1_struct_0(A_24)) | ~l1_struct_0(A_24) | ~v7_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.83/1.57  tff(c_251, plain, (v1_zfmisc_1('#skF_2'('#skF_4', k1_tex_2('#skF_4', '#skF_5'))) | ~l1_struct_0(k1_tex_2('#skF_4', '#skF_5')) | ~v7_struct_0(k1_tex_2('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_220, c_22])).
% 3.83/1.57  tff(c_280, plain, (v1_zfmisc_1('#skF_2'('#skF_4', k1_tex_2('#skF_4', '#skF_5'))) | ~l1_struct_0(k1_tex_2('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_251])).
% 3.83/1.57  tff(c_283, plain, (~l1_struct_0(k1_tex_2('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_280])).
% 3.83/1.57  tff(c_286, plain, (~l1_pre_topc(k1_tex_2('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_283])).
% 3.83/1.57  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_286])).
% 3.83/1.57  tff(c_291, plain, (v1_zfmisc_1('#skF_2'('#skF_4', k1_tex_2('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_280])).
% 3.83/1.57  tff(c_627, plain, (v1_zfmisc_1(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_617, c_291])).
% 3.83/1.57  tff(c_630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_627])).
% 3.83/1.57  tff(c_631, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_175])).
% 3.83/1.57  tff(c_20, plain, (![A_23]: (~v1_xboole_0(u1_struct_0(A_23)) | ~l1_struct_0(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.83/1.57  tff(c_637, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_631, c_20])).
% 3.83/1.57  tff(c_643, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_637])).
% 3.83/1.57  tff(c_646, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_643])).
% 3.83/1.57  tff(c_650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_646])).
% 3.83/1.57  tff(c_652, plain, (v1_tex_2(k1_tex_2('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 3.83/1.57  tff(c_715, plain, (![B_190, A_191]: (~v1_tex_2(B_190, A_191) | u1_struct_0(B_190)!=u1_struct_0(A_191) | ~m1_pre_topc(B_190, A_191) | ~l1_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.83/1.57  tff(c_718, plain, (u1_struct_0(k1_tex_2('#skF_4', '#skF_5'))!=u1_struct_0('#skF_4') | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_652, c_715])).
% 3.83/1.57  tff(c_721, plain, (u1_struct_0(k1_tex_2('#skF_4', '#skF_5'))!=u1_struct_0('#skF_4') | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_718])).
% 3.83/1.57  tff(c_722, plain, (~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_721])).
% 3.83/1.57  tff(c_790, plain, (![A_207, B_208]: (m1_pre_topc(k1_tex_2(A_207, B_208), A_207) | ~m1_subset_1(B_208, u1_struct_0(A_207)) | ~l1_pre_topc(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.83/1.57  tff(c_792, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_790])).
% 3.83/1.57  tff(c_795, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_792])).
% 3.83/1.57  tff(c_797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_722, c_795])).
% 3.83/1.57  tff(c_799, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_721])).
% 3.83/1.57  tff(c_802, plain, (l1_pre_topc(k1_tex_2('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_799, c_18])).
% 3.83/1.57  tff(c_805, plain, (l1_pre_topc(k1_tex_2('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_802])).
% 3.83/1.57  tff(c_699, plain, (![A_186, B_187]: (~v2_struct_0(k1_tex_2(A_186, B_187)) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l1_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.83/1.57  tff(c_702, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_699])).
% 3.83/1.57  tff(c_705, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_702])).
% 3.83/1.57  tff(c_706, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_705])).
% 3.83/1.57  tff(c_815, plain, (![A_213, B_214]: (v1_subset_1(k6_domain_1(A_213, B_214), A_213) | ~m1_subset_1(B_214, A_213) | v1_zfmisc_1(A_213) | v1_xboole_0(A_213))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.83/1.57  tff(c_651, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_74])).
% 3.83/1.57  tff(c_821, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v1_zfmisc_1(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_815, c_651])).
% 3.83/1.57  tff(c_825, plain, (v1_zfmisc_1(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_821])).
% 3.83/1.57  tff(c_826, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_825])).
% 3.83/1.57  tff(c_831, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_826, c_20])).
% 3.83/1.57  tff(c_837, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_831])).
% 3.83/1.57  tff(c_840, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_837])).
% 3.83/1.57  tff(c_844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_840])).
% 3.83/1.57  tff(c_846, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_825])).
% 3.83/1.57  tff(c_845, plain, (v1_zfmisc_1(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_825])).
% 3.83/1.57  tff(c_24, plain, (![B_27, A_25]: (m1_subset_1(u1_struct_0(B_27), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.83/1.57  tff(c_978, plain, (![B_234, A_235]: (v1_subset_1(u1_struct_0(B_234), u1_struct_0(A_235)) | ~m1_subset_1(u1_struct_0(B_234), k1_zfmisc_1(u1_struct_0(A_235))) | ~v1_tex_2(B_234, A_235) | ~m1_pre_topc(B_234, A_235) | ~l1_pre_topc(A_235))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.83/1.57  tff(c_988, plain, (![B_27, A_25]: (v1_subset_1(u1_struct_0(B_27), u1_struct_0(A_25)) | ~v1_tex_2(B_27, A_25) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_24, c_978])).
% 3.83/1.57  tff(c_847, plain, (![B_215, A_216]: (~v1_subset_1(B_215, A_216) | v1_xboole_0(B_215) | ~m1_subset_1(B_215, k1_zfmisc_1(A_216)) | ~v1_zfmisc_1(A_216) | v1_xboole_0(A_216))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.83/1.57  tff(c_1031, plain, (![B_249, A_250]: (~v1_subset_1(u1_struct_0(B_249), u1_struct_0(A_250)) | v1_xboole_0(u1_struct_0(B_249)) | ~v1_zfmisc_1(u1_struct_0(A_250)) | v1_xboole_0(u1_struct_0(A_250)) | ~m1_pre_topc(B_249, A_250) | ~l1_pre_topc(A_250))), inference(resolution, [status(thm)], [c_24, c_847])).
% 3.83/1.57  tff(c_1046, plain, (![B_251, A_252]: (v1_xboole_0(u1_struct_0(B_251)) | ~v1_zfmisc_1(u1_struct_0(A_252)) | v1_xboole_0(u1_struct_0(A_252)) | ~v1_tex_2(B_251, A_252) | ~m1_pre_topc(B_251, A_252) | ~l1_pre_topc(A_252))), inference(resolution, [status(thm)], [c_988, c_1031])).
% 3.83/1.57  tff(c_1050, plain, (![B_251]: (v1_xboole_0(u1_struct_0(B_251)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v1_tex_2(B_251, '#skF_4') | ~m1_pre_topc(B_251, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_845, c_1046])).
% 3.83/1.57  tff(c_1058, plain, (![B_251]: (v1_xboole_0(u1_struct_0(B_251)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v1_tex_2(B_251, '#skF_4') | ~m1_pre_topc(B_251, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1050])).
% 3.83/1.57  tff(c_1062, plain, (![B_253]: (v1_xboole_0(u1_struct_0(B_253)) | ~v1_tex_2(B_253, '#skF_4') | ~m1_pre_topc(B_253, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_846, c_1058])).
% 3.83/1.57  tff(c_1087, plain, (![B_254]: (~l1_struct_0(B_254) | v2_struct_0(B_254) | ~v1_tex_2(B_254, '#skF_4') | ~m1_pre_topc(B_254, '#skF_4'))), inference(resolution, [status(thm)], [c_1062, c_20])).
% 3.83/1.57  tff(c_1094, plain, (~l1_struct_0(k1_tex_2('#skF_4', '#skF_5')) | v2_struct_0(k1_tex_2('#skF_4', '#skF_5')) | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_652, c_1087])).
% 3.83/1.57  tff(c_1100, plain, (~l1_struct_0(k1_tex_2('#skF_4', '#skF_5')) | v2_struct_0(k1_tex_2('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_1094])).
% 3.83/1.57  tff(c_1101, plain, (~l1_struct_0(k1_tex_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_706, c_1100])).
% 3.83/1.57  tff(c_1104, plain, (~l1_pre_topc(k1_tex_2('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_1101])).
% 3.83/1.57  tff(c_1108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_805, c_1104])).
% 3.83/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.57  
% 3.83/1.57  Inference rules
% 3.83/1.57  ----------------------
% 3.83/1.57  #Ref     : 0
% 3.83/1.57  #Sup     : 210
% 3.83/1.57  #Fact    : 0
% 3.83/1.57  #Define  : 0
% 3.83/1.57  #Split   : 9
% 3.83/1.57  #Chain   : 0
% 3.83/1.57  #Close   : 0
% 3.83/1.57  
% 3.83/1.57  Ordering : KBO
% 3.83/1.57  
% 3.83/1.57  Simplification rules
% 3.83/1.57  ----------------------
% 3.83/1.57  #Subsume      : 31
% 3.83/1.57  #Demod        : 82
% 3.83/1.57  #Tautology    : 22
% 3.83/1.57  #SimpNegUnit  : 27
% 3.83/1.57  #BackRed      : 11
% 3.83/1.57  
% 3.83/1.57  #Partial instantiations: 0
% 3.83/1.57  #Strategies tried      : 1
% 3.83/1.57  
% 3.83/1.57  Timing (in seconds)
% 3.83/1.57  ----------------------
% 3.83/1.57  Preprocessing        : 0.37
% 3.83/1.57  Parsing              : 0.19
% 3.83/1.57  CNF conversion       : 0.03
% 3.83/1.57  Main loop            : 0.50
% 3.83/1.57  Inferencing          : 0.19
% 3.83/1.57  Reduction            : 0.14
% 3.83/1.57  Demodulation         : 0.09
% 3.83/1.57  BG Simplification    : 0.03
% 3.83/1.57  Subsumption          : 0.10
% 3.83/1.57  Abstraction          : 0.03
% 3.83/1.57  MUC search           : 0.00
% 3.83/1.57  Cooper               : 0.00
% 3.83/1.57  Total                : 0.92
% 3.83/1.57  Index Insertion      : 0.00
% 3.83/1.57  Index Deletion       : 0.00
% 3.83/1.57  Index Matching       : 0.00
% 3.83/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

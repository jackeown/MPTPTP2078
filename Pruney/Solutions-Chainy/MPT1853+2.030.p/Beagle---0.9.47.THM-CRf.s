%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:04 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 352 expanded)
%              Number of leaves         :   36 ( 128 expanded)
%              Depth                    :   14
%              Number of atoms          :  281 ( 958 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_171,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_115,axiom,(
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

tff(f_122,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_150,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ~ ( u1_struct_0(B) = u1_struct_0(A)
              & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_182,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_8,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_68,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_75,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_109,plain,(
    ! [A_70,B_71] :
      ( ~ v1_zfmisc_1(A_70)
      | ~ v1_subset_1(k6_domain_1(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_112,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_75,c_109])).

tff(c_115,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_112])).

tff(c_116,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_156,plain,(
    ! [A_82,B_83] :
      ( m1_pre_topc(k1_tex_2(A_82,B_83),A_82)
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_158,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_156])).

tff(c_161,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_158])).

tff(c_162,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_161])).

tff(c_309,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1('#skF_2'(A_101,B_102),k1_zfmisc_1(u1_struct_0(A_101)))
      | v1_tex_2(B_102,A_101)
      | ~ m1_pre_topc(B_102,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ! [B_33,A_32] :
      ( v1_subset_1(B_33,A_32)
      | B_33 = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_466,plain,(
    ! [A_121,B_122] :
      ( v1_subset_1('#skF_2'(A_121,B_122),u1_struct_0(A_121))
      | u1_struct_0(A_121) = '#skF_2'(A_121,B_122)
      | v1_tex_2(B_122,A_121)
      | ~ m1_pre_topc(B_122,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_309,c_34])).

tff(c_28,plain,(
    ! [A_22,B_28] :
      ( ~ v1_subset_1('#skF_2'(A_22,B_28),u1_struct_0(A_22))
      | v1_tex_2(B_28,A_22)
      | ~ m1_pre_topc(B_28,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_476,plain,(
    ! [A_123,B_124] :
      ( u1_struct_0(A_123) = '#skF_2'(A_123,B_124)
      | v1_tex_2(B_124,A_123)
      | ~ m1_pre_topc(B_124,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_466,c_28])).

tff(c_62,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_106,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_62])).

tff(c_486,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_476,c_106])).

tff(c_491,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_162,c_486])).

tff(c_10,plain,(
    ! [B_11,A_9] :
      ( l1_pre_topc(B_11)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_165,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_10])).

tff(c_168,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_165])).

tff(c_131,plain,(
    ! [A_74,B_75] :
      ( ~ v2_struct_0(k1_tex_2(A_74,B_75))
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l1_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_134,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_131])).

tff(c_137,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_134])).

tff(c_138,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_137])).

tff(c_174,plain,(
    ! [B_86,A_87] :
      ( u1_struct_0(B_86) = '#skF_2'(A_87,B_86)
      | v1_tex_2(B_86,A_87)
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_180,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_106])).

tff(c_184,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_162,c_180])).

tff(c_12,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_213,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_12])).

tff(c_239,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_213])).

tff(c_243,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_246,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_243])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_246])).

tff(c_252,plain,(
    l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_147,plain,(
    ! [A_78,B_79] :
      ( v7_struct_0(k1_tex_2(A_78,B_79))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_150,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_147])).

tff(c_153,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_150])).

tff(c_154,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_153])).

tff(c_14,plain,(
    ! [A_13] :
      ( v1_zfmisc_1(u1_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | ~ v7_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_216,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_14])).

tff(c_241,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_216])).

tff(c_260,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_241])).

tff(c_501,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_260])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_501])).

tff(c_506,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_512,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_506,c_12])).

tff(c_518,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_512])).

tff(c_521,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_518])).

tff(c_525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_521])).

tff(c_526,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_604,plain,(
    ! [B_147,A_148] :
      ( ~ v1_tex_2(B_147,A_148)
      | u1_struct_0(B_147) != u1_struct_0(A_148)
      | ~ m1_pre_topc(B_147,A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_607,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) != u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_604])).

tff(c_610,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) != u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_607])).

tff(c_611,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_643,plain,(
    ! [A_159,B_160] :
      ( m1_pre_topc(k1_tex_2(A_159,B_160),A_159)
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l1_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_645,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_643])).

tff(c_648,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_645])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_611,c_648])).

tff(c_652,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_655,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_652,c_10])).

tff(c_658,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_655])).

tff(c_664,plain,(
    ! [A_163,B_164] :
      ( ~ v2_struct_0(k1_tex_2(A_163,B_164))
      | ~ m1_subset_1(B_164,u1_struct_0(A_163))
      | ~ l1_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_667,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_664])).

tff(c_670,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_667])).

tff(c_671,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_670])).

tff(c_561,plain,(
    ! [A_141,B_142] :
      ( v1_subset_1(k6_domain_1(A_141,B_142),A_141)
      | ~ m1_subset_1(B_142,A_141)
      | v1_zfmisc_1(A_141)
      | v1_xboole_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_527,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_564,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_561,c_527])).

tff(c_567,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_564])).

tff(c_568,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_567])).

tff(c_580,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_568,c_12])).

tff(c_586,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_580])).

tff(c_589,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_586])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_589])).

tff(c_595,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_594,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_22,plain,(
    ! [B_18,A_16] :
      ( m1_subset_1(u1_struct_0(B_18),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_741,plain,(
    ! [B_188,A_189] :
      ( v1_subset_1(u1_struct_0(B_188),u1_struct_0(A_189))
      | ~ m1_subset_1(u1_struct_0(B_188),k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ v1_tex_2(B_188,A_189)
      | ~ m1_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_745,plain,(
    ! [B_18,A_16] :
      ( v1_subset_1(u1_struct_0(B_18),u1_struct_0(A_16))
      | ~ v1_tex_2(B_18,A_16)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_741])).

tff(c_680,plain,(
    ! [B_167,A_168] :
      ( v1_xboole_0(B_167)
      | ~ v1_subset_1(B_167,A_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_168))
      | ~ v1_zfmisc_1(A_168)
      | v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_791,plain,(
    ! [B_203,A_204] :
      ( v1_xboole_0(u1_struct_0(B_203))
      | ~ v1_subset_1(u1_struct_0(B_203),u1_struct_0(A_204))
      | ~ v1_zfmisc_1(u1_struct_0(A_204))
      | v1_xboole_0(u1_struct_0(A_204))
      | ~ m1_pre_topc(B_203,A_204)
      | ~ l1_pre_topc(A_204) ) ),
    inference(resolution,[status(thm)],[c_22,c_680])).

tff(c_800,plain,(
    ! [B_205,A_206] :
      ( v1_xboole_0(u1_struct_0(B_205))
      | ~ v1_zfmisc_1(u1_struct_0(A_206))
      | v1_xboole_0(u1_struct_0(A_206))
      | ~ v1_tex_2(B_205,A_206)
      | ~ m1_pre_topc(B_205,A_206)
      | ~ l1_pre_topc(A_206) ) ),
    inference(resolution,[status(thm)],[c_745,c_791])).

tff(c_802,plain,(
    ! [B_205] :
      ( v1_xboole_0(u1_struct_0(B_205))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_205,'#skF_3')
      | ~ m1_pre_topc(B_205,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_594,c_800])).

tff(c_810,plain,(
    ! [B_205] :
      ( v1_xboole_0(u1_struct_0(B_205))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_205,'#skF_3')
      | ~ m1_pre_topc(B_205,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_802])).

tff(c_814,plain,(
    ! [B_207] :
      ( v1_xboole_0(u1_struct_0(B_207))
      | ~ v1_tex_2(B_207,'#skF_3')
      | ~ m1_pre_topc(B_207,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_810])).

tff(c_871,plain,(
    ! [B_211] :
      ( ~ l1_struct_0(B_211)
      | v2_struct_0(B_211)
      | ~ v1_tex_2(B_211,'#skF_3')
      | ~ m1_pre_topc(B_211,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_814,c_12])).

tff(c_882,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_871])).

tff(c_891,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_882])).

tff(c_892,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_891])).

tff(c_895,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_892])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.18/0.33  % DateTime   : Tue Dec  1 11:03:32 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.71  
% 3.62/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.71  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.62/1.71  
% 3.62/1.71  %Foreground sorts:
% 3.62/1.71  
% 3.62/1.71  
% 3.62/1.71  %Background operators:
% 3.62/1.71  
% 3.62/1.71  
% 3.62/1.71  %Foreground operators:
% 3.62/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.62/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.71  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.62/1.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.62/1.71  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.62/1.71  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.62/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.62/1.71  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.62/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.71  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.62/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.62/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.71  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.62/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.62/1.71  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.62/1.71  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.62/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.62/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.71  
% 3.62/1.73  tff(f_195, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 3.62/1.73  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.62/1.73  tff(f_171, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.62/1.73  tff(f_136, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.62/1.73  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 3.62/1.73  tff(f_122, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.62/1.73  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.62/1.73  tff(f_150, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.62/1.73  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.62/1.73  tff(f_69, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.62/1.73  tff(f_160, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 3.62/1.73  tff(f_182, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 3.62/1.73  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.62/1.73  tff(f_101, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) => v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tex_2)).
% 3.62/1.73  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.62/1.73  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.62/1.73  tff(c_8, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.73  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.62/1.73  tff(c_68, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.62/1.73  tff(c_75, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_68])).
% 3.62/1.73  tff(c_109, plain, (![A_70, B_71]: (~v1_zfmisc_1(A_70) | ~v1_subset_1(k6_domain_1(A_70, B_71), A_70) | ~m1_subset_1(B_71, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.62/1.73  tff(c_112, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_75, c_109])).
% 3.62/1.73  tff(c_115, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_112])).
% 3.62/1.73  tff(c_116, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_115])).
% 3.62/1.73  tff(c_156, plain, (![A_82, B_83]: (m1_pre_topc(k1_tex_2(A_82, B_83), A_82) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.62/1.73  tff(c_158, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_156])).
% 3.62/1.73  tff(c_161, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_158])).
% 3.62/1.73  tff(c_162, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_161])).
% 3.62/1.73  tff(c_309, plain, (![A_101, B_102]: (m1_subset_1('#skF_2'(A_101, B_102), k1_zfmisc_1(u1_struct_0(A_101))) | v1_tex_2(B_102, A_101) | ~m1_pre_topc(B_102, A_101) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.62/1.73  tff(c_34, plain, (![B_33, A_32]: (v1_subset_1(B_33, A_32) | B_33=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.62/1.73  tff(c_466, plain, (![A_121, B_122]: (v1_subset_1('#skF_2'(A_121, B_122), u1_struct_0(A_121)) | u1_struct_0(A_121)='#skF_2'(A_121, B_122) | v1_tex_2(B_122, A_121) | ~m1_pre_topc(B_122, A_121) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_309, c_34])).
% 3.62/1.73  tff(c_28, plain, (![A_22, B_28]: (~v1_subset_1('#skF_2'(A_22, B_28), u1_struct_0(A_22)) | v1_tex_2(B_28, A_22) | ~m1_pre_topc(B_28, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.62/1.73  tff(c_476, plain, (![A_123, B_124]: (u1_struct_0(A_123)='#skF_2'(A_123, B_124) | v1_tex_2(B_124, A_123) | ~m1_pre_topc(B_124, A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_466, c_28])).
% 3.62/1.73  tff(c_62, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.62/1.73  tff(c_106, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_62])).
% 3.62/1.73  tff(c_486, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_476, c_106])).
% 3.62/1.73  tff(c_491, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_162, c_486])).
% 3.62/1.73  tff(c_10, plain, (![B_11, A_9]: (l1_pre_topc(B_11) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.62/1.73  tff(c_165, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_162, c_10])).
% 3.62/1.73  tff(c_168, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_165])).
% 3.62/1.73  tff(c_131, plain, (![A_74, B_75]: (~v2_struct_0(k1_tex_2(A_74, B_75)) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l1_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.62/1.73  tff(c_134, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_131])).
% 3.62/1.73  tff(c_137, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_134])).
% 3.62/1.73  tff(c_138, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_137])).
% 3.62/1.73  tff(c_174, plain, (![B_86, A_87]: (u1_struct_0(B_86)='#skF_2'(A_87, B_86) | v1_tex_2(B_86, A_87) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.62/1.73  tff(c_180, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_174, c_106])).
% 3.62/1.73  tff(c_184, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_162, c_180])).
% 3.62/1.73  tff(c_12, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.73  tff(c_213, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_12])).
% 3.62/1.73  tff(c_239, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_138, c_213])).
% 3.62/1.73  tff(c_243, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_239])).
% 3.62/1.73  tff(c_246, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_243])).
% 3.62/1.73  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_246])).
% 3.62/1.73  tff(c_252, plain, (l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_239])).
% 3.62/1.73  tff(c_147, plain, (![A_78, B_79]: (v7_struct_0(k1_tex_2(A_78, B_79)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.62/1.73  tff(c_150, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_147])).
% 3.62/1.73  tff(c_153, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_150])).
% 3.62/1.73  tff(c_154, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_153])).
% 3.62/1.73  tff(c_14, plain, (![A_13]: (v1_zfmisc_1(u1_struct_0(A_13)) | ~l1_struct_0(A_13) | ~v7_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.62/1.73  tff(c_216, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_14])).
% 3.62/1.73  tff(c_241, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_216])).
% 3.62/1.73  tff(c_260, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_241])).
% 3.62/1.73  tff(c_501, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_260])).
% 3.62/1.73  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_501])).
% 3.62/1.73  tff(c_506, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_115])).
% 3.62/1.73  tff(c_512, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_506, c_12])).
% 3.62/1.73  tff(c_518, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_512])).
% 3.62/1.73  tff(c_521, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_518])).
% 3.62/1.73  tff(c_525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_521])).
% 3.62/1.73  tff(c_526, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 3.62/1.73  tff(c_604, plain, (![B_147, A_148]: (~v1_tex_2(B_147, A_148) | u1_struct_0(B_147)!=u1_struct_0(A_148) | ~m1_pre_topc(B_147, A_148) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.62/1.73  tff(c_607, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_526, c_604])).
% 3.62/1.73  tff(c_610, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_607])).
% 3.62/1.73  tff(c_611, plain, (~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_610])).
% 3.62/1.73  tff(c_643, plain, (![A_159, B_160]: (m1_pre_topc(k1_tex_2(A_159, B_160), A_159) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l1_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.62/1.73  tff(c_645, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_643])).
% 3.62/1.73  tff(c_648, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_645])).
% 3.62/1.73  tff(c_650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_611, c_648])).
% 3.62/1.73  tff(c_652, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_610])).
% 3.62/1.73  tff(c_655, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_652, c_10])).
% 3.62/1.73  tff(c_658, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_655])).
% 3.62/1.73  tff(c_664, plain, (![A_163, B_164]: (~v2_struct_0(k1_tex_2(A_163, B_164)) | ~m1_subset_1(B_164, u1_struct_0(A_163)) | ~l1_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.62/1.73  tff(c_667, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_664])).
% 3.62/1.73  tff(c_670, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_667])).
% 3.62/1.73  tff(c_671, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_670])).
% 3.62/1.73  tff(c_561, plain, (![A_141, B_142]: (v1_subset_1(k6_domain_1(A_141, B_142), A_141) | ~m1_subset_1(B_142, A_141) | v1_zfmisc_1(A_141) | v1_xboole_0(A_141))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.62/1.73  tff(c_527, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_68])).
% 3.62/1.73  tff(c_564, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_561, c_527])).
% 3.62/1.73  tff(c_567, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_564])).
% 3.62/1.73  tff(c_568, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_567])).
% 3.62/1.73  tff(c_580, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_568, c_12])).
% 3.62/1.73  tff(c_586, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_580])).
% 3.62/1.73  tff(c_589, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_586])).
% 3.62/1.73  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_589])).
% 3.62/1.73  tff(c_595, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_567])).
% 3.62/1.73  tff(c_594, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_567])).
% 3.62/1.73  tff(c_22, plain, (![B_18, A_16]: (m1_subset_1(u1_struct_0(B_18), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.62/1.73  tff(c_741, plain, (![B_188, A_189]: (v1_subset_1(u1_struct_0(B_188), u1_struct_0(A_189)) | ~m1_subset_1(u1_struct_0(B_188), k1_zfmisc_1(u1_struct_0(A_189))) | ~v1_tex_2(B_188, A_189) | ~m1_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.62/1.73  tff(c_745, plain, (![B_18, A_16]: (v1_subset_1(u1_struct_0(B_18), u1_struct_0(A_16)) | ~v1_tex_2(B_18, A_16) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_22, c_741])).
% 3.62/1.73  tff(c_680, plain, (![B_167, A_168]: (v1_xboole_0(B_167) | ~v1_subset_1(B_167, A_168) | ~m1_subset_1(B_167, k1_zfmisc_1(A_168)) | ~v1_zfmisc_1(A_168) | v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.62/1.73  tff(c_791, plain, (![B_203, A_204]: (v1_xboole_0(u1_struct_0(B_203)) | ~v1_subset_1(u1_struct_0(B_203), u1_struct_0(A_204)) | ~v1_zfmisc_1(u1_struct_0(A_204)) | v1_xboole_0(u1_struct_0(A_204)) | ~m1_pre_topc(B_203, A_204) | ~l1_pre_topc(A_204))), inference(resolution, [status(thm)], [c_22, c_680])).
% 3.62/1.73  tff(c_800, plain, (![B_205, A_206]: (v1_xboole_0(u1_struct_0(B_205)) | ~v1_zfmisc_1(u1_struct_0(A_206)) | v1_xboole_0(u1_struct_0(A_206)) | ~v1_tex_2(B_205, A_206) | ~m1_pre_topc(B_205, A_206) | ~l1_pre_topc(A_206))), inference(resolution, [status(thm)], [c_745, c_791])).
% 3.62/1.73  tff(c_802, plain, (![B_205]: (v1_xboole_0(u1_struct_0(B_205)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~v1_tex_2(B_205, '#skF_3') | ~m1_pre_topc(B_205, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_594, c_800])).
% 3.62/1.73  tff(c_810, plain, (![B_205]: (v1_xboole_0(u1_struct_0(B_205)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~v1_tex_2(B_205, '#skF_3') | ~m1_pre_topc(B_205, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_802])).
% 3.62/1.73  tff(c_814, plain, (![B_207]: (v1_xboole_0(u1_struct_0(B_207)) | ~v1_tex_2(B_207, '#skF_3') | ~m1_pre_topc(B_207, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_595, c_810])).
% 3.62/1.73  tff(c_871, plain, (![B_211]: (~l1_struct_0(B_211) | v2_struct_0(B_211) | ~v1_tex_2(B_211, '#skF_3') | ~m1_pre_topc(B_211, '#skF_3'))), inference(resolution, [status(thm)], [c_814, c_12])).
% 3.62/1.73  tff(c_882, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_526, c_871])).
% 3.62/1.73  tff(c_891, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_882])).
% 3.62/1.73  tff(c_892, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_671, c_891])).
% 3.62/1.73  tff(c_895, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_892])).
% 3.62/1.73  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_658, c_895])).
% 3.62/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.73  
% 3.62/1.73  Inference rules
% 3.62/1.73  ----------------------
% 3.62/1.73  #Ref     : 0
% 3.62/1.73  #Sup     : 146
% 3.62/1.73  #Fact    : 0
% 3.62/1.73  #Define  : 0
% 3.62/1.73  #Split   : 8
% 3.62/1.73  #Chain   : 0
% 3.62/1.73  #Close   : 0
% 3.62/1.73  
% 3.62/1.73  Ordering : KBO
% 3.62/1.73  
% 3.62/1.73  Simplification rules
% 3.62/1.73  ----------------------
% 3.62/1.73  #Subsume      : 29
% 3.62/1.73  #Demod        : 88
% 3.62/1.73  #Tautology    : 11
% 3.62/1.73  #SimpNegUnit  : 26
% 3.62/1.73  #BackRed      : 12
% 3.62/1.73  
% 3.62/1.73  #Partial instantiations: 0
% 3.62/1.73  #Strategies tried      : 1
% 3.62/1.73  
% 3.62/1.73  Timing (in seconds)
% 3.62/1.73  ----------------------
% 3.62/1.74  Preprocessing        : 0.42
% 3.62/1.74  Parsing              : 0.22
% 3.62/1.74  CNF conversion       : 0.03
% 3.62/1.74  Main loop            : 0.41
% 3.62/1.74  Inferencing          : 0.16
% 3.62/1.74  Reduction            : 0.11
% 3.62/1.74  Demodulation         : 0.08
% 3.62/1.74  BG Simplification    : 0.03
% 3.62/1.74  Subsumption          : 0.08
% 3.62/1.74  Abstraction          : 0.02
% 3.62/1.74  MUC search           : 0.00
% 3.62/1.74  Cooper               : 0.00
% 3.62/1.74  Total                : 0.88
% 3.62/1.74  Index Insertion      : 0.00
% 3.62/1.74  Index Deletion       : 0.00
% 3.62/1.74  Index Matching       : 0.00
% 3.62/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------

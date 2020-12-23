%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:04 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 479 expanded)
%              Number of leaves         :   37 ( 171 expanded)
%              Depth                    :   13
%              Number of atoms          :  294 (1344 expanded)
%              Number of equality atoms :   32 (  97 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_190,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_106,axiom,(
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

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_177,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ~ ( u1_struct_0(B) = u1_struct_0(A)
              & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_92,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_164,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_62,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_79,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_130,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_68])).

tff(c_211,plain,(
    ! [A_88,B_89] :
      ( m1_pre_topc(k1_tex_2(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_216,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_211])).

tff(c_220,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_216])).

tff(c_221,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_220])).

tff(c_323,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1('#skF_2'(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_93)))
      | v1_tex_2(B_94,A_93)
      | ~ m1_pre_topc(B_94,A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    ! [B_34,A_33] :
      ( v1_subset_1(B_34,A_33)
      | B_34 = A_33
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_688,plain,(
    ! [A_135,B_136] :
      ( v1_subset_1('#skF_2'(A_135,B_136),u1_struct_0(A_135))
      | u1_struct_0(A_135) = '#skF_2'(A_135,B_136)
      | v1_tex_2(B_136,A_135)
      | ~ m1_pre_topc(B_136,A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_323,c_34])).

tff(c_28,plain,(
    ! [A_23,B_29] :
      ( ~ v1_subset_1('#skF_2'(A_23,B_29),u1_struct_0(A_23))
      | v1_tex_2(B_29,A_23)
      | ~ m1_pre_topc(B_29,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_698,plain,(
    ! [A_137,B_138] :
      ( u1_struct_0(A_137) = '#skF_2'(A_137,B_138)
      | v1_tex_2(B_138,A_137)
      | ~ m1_pre_topc(B_138,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_688,c_28])).

tff(c_708,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_698,c_79])).

tff(c_713,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_221,c_708])).

tff(c_157,plain,(
    ! [A_75,B_76] :
      ( ~ v2_struct_0(k1_tex_2(A_75,B_76))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_164,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_157])).

tff(c_168,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_164])).

tff(c_169,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_168])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( l1_pre_topc(B_8)
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_226,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_221,c_8])).

tff(c_232,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_226])).

tff(c_200,plain,(
    ! [B_86,A_87] :
      ( u1_struct_0(B_86) = '#skF_2'(A_87,B_86)
      | v1_tex_2(B_86,A_87)
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_206,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_200,c_79])).

tff(c_210,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_206])).

tff(c_235,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_210])).

tff(c_12,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_273,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_12])).

tff(c_303,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_273])).

tff(c_305,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_308,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_305])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_308])).

tff(c_314,plain,(
    l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_184,plain,(
    ! [A_81,B_82] :
      ( v7_struct_0(k1_tex_2(A_81,B_82))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_191,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_184])).

tff(c_195,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_191])).

tff(c_196,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_195])).

tff(c_427,plain,(
    ! [A_106,B_107] :
      ( ~ v7_struct_0(A_106)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_106),B_107),u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_struct_0(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_434,plain,(
    ! [B_107] :
      ( ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | ~ v1_subset_1(k6_domain_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')),B_107),u1_struct_0(k1_tex_2('#skF_3','#skF_4')))
      | ~ m1_subset_1(B_107,u1_struct_0(k1_tex_2('#skF_3','#skF_4')))
      | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_427])).

tff(c_447,plain,(
    ! [B_107] :
      ( ~ v1_subset_1(k6_domain_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')),B_107),'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | ~ m1_subset_1(B_107,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_235,c_235,c_196,c_434])).

tff(c_448,plain,(
    ! [B_107] :
      ( ~ v1_subset_1(k6_domain_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')),B_107),'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | ~ m1_subset_1(B_107,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_447])).

tff(c_982,plain,(
    ! [B_149] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),B_149),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_713,c_713,c_448])).

tff(c_989,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_130,c_982])).

tff(c_1000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_989])).

tff(c_1002,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1336,plain,(
    ! [B_208,A_209] :
      ( ~ v1_tex_2(B_208,A_209)
      | u1_struct_0(B_208) != u1_struct_0(A_209)
      | ~ m1_pre_topc(B_208,A_209)
      | ~ l1_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1339,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) != u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1002,c_1336])).

tff(c_1342,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) != u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1339])).

tff(c_1356,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1342])).

tff(c_1391,plain,(
    ! [A_221,B_222] :
      ( m1_pre_topc(k1_tex_2(A_221,B_222),A_221)
      | ~ m1_subset_1(B_222,u1_struct_0(A_221))
      | ~ l1_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1396,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1391])).

tff(c_1400,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1396])).

tff(c_1402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1356,c_1400])).

tff(c_1404,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1342])).

tff(c_1407,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1404,c_8])).

tff(c_1410,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1407])).

tff(c_1403,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) != u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1342])).

tff(c_1411,plain,(
    ! [A_223,B_224] :
      ( ~ v2_struct_0(k1_tex_2(A_223,B_224))
      | ~ m1_subset_1(B_224,u1_struct_0(A_223))
      | ~ l1_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1418,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1411])).

tff(c_1422,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1418])).

tff(c_1423,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1422])).

tff(c_1033,plain,(
    ! [A_160,B_161] :
      ( v1_zfmisc_1(A_160)
      | k6_domain_1(A_160,B_161) != A_160
      | ~ m1_subset_1(B_161,A_160)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1041,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_1033])).

tff(c_1061,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1041])).

tff(c_1062,plain,(
    ! [A_165,B_166] :
      ( m1_subset_1(k6_domain_1(A_165,B_166),k1_zfmisc_1(A_165))
      | ~ m1_subset_1(B_166,A_165)
      | v1_xboole_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1229,plain,(
    ! [A_202,B_203] :
      ( v1_subset_1(k6_domain_1(A_202,B_203),A_202)
      | k6_domain_1(A_202,B_203) = A_202
      | ~ m1_subset_1(B_203,A_202)
      | v1_xboole_0(A_202) ) ),
    inference(resolution,[status(thm)],[c_1062,c_34])).

tff(c_1001,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1236,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1229,c_1001])).

tff(c_1243,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1236])).

tff(c_1244,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1061,c_1243])).

tff(c_1249,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1244,c_12])).

tff(c_1255,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1249])).

tff(c_1258,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1255])).

tff(c_1262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1258])).

tff(c_1264,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1041])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k6_domain_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1286,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_14])).

tff(c_1290,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1286])).

tff(c_1292,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1290])).

tff(c_1295,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1292,c_12])).

tff(c_1298,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1295])).

tff(c_1301,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1298])).

tff(c_1305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1301])).

tff(c_1307,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1290])).

tff(c_1263,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1041])).

tff(c_1265,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1263])).

tff(c_18,plain,(
    ! [B_18,A_16] :
      ( r1_tarski(u1_struct_0(B_18),u1_struct_0(A_16))
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1028,plain,(
    ! [B_158,A_159] :
      ( B_158 = A_159
      | ~ r1_tarski(A_159,B_158)
      | ~ v1_zfmisc_1(B_158)
      | v1_xboole_0(B_158)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1617,plain,(
    ! [B_266,A_267] :
      ( u1_struct_0(B_266) = u1_struct_0(A_267)
      | ~ v1_zfmisc_1(u1_struct_0(A_267))
      | v1_xboole_0(u1_struct_0(A_267))
      | v1_xboole_0(u1_struct_0(B_266))
      | ~ m1_pre_topc(B_266,A_267)
      | ~ l1_pre_topc(A_267) ) ),
    inference(resolution,[status(thm)],[c_18,c_1028])).

tff(c_1619,plain,(
    ! [B_266] :
      ( u1_struct_0(B_266) = u1_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0(B_266))
      | ~ m1_pre_topc(B_266,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1265,c_1617])).

tff(c_1625,plain,(
    ! [B_266] :
      ( u1_struct_0(B_266) = u1_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0(B_266))
      | ~ m1_pre_topc(B_266,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1619])).

tff(c_1628,plain,(
    ! [B_268] :
      ( u1_struct_0(B_268) = u1_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0(B_268))
      | ~ m1_pre_topc(B_268,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1307,c_1625])).

tff(c_1643,plain,(
    ! [B_269] :
      ( ~ l1_struct_0(B_269)
      | v2_struct_0(B_269)
      | u1_struct_0(B_269) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_269,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1628,c_12])).

tff(c_1650,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1404,c_1643])).

tff(c_1657,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1403,c_1423,c_1650])).

tff(c_1660,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1657])).

tff(c_1664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1660])).

tff(c_1665,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1263])).

tff(c_1669,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1665,c_12])).

tff(c_1672,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1669])).

tff(c_1675,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1672])).

tff(c_1679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.71  
% 4.15/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.71  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.15/1.71  
% 4.15/1.71  %Foreground sorts:
% 4.15/1.71  
% 4.15/1.71  
% 4.15/1.71  %Background operators:
% 4.15/1.71  
% 4.15/1.71  
% 4.15/1.71  %Foreground operators:
% 4.15/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.15/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.71  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.15/1.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.15/1.71  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 4.15/1.71  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.15/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.15/1.71  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.15/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.15/1.71  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.15/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.15/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.71  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 4.15/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.15/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.15/1.71  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.15/1.71  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.15/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.15/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.15/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.71  
% 4.15/1.74  tff(f_190, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 4.15/1.74  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.15/1.74  tff(f_127, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 4.15/1.74  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 4.15/1.74  tff(f_113, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.15/1.74  tff(f_141, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 4.15/1.74  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.15/1.74  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.15/1.74  tff(f_177, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 4.15/1.74  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 4.15/1.74  tff(f_92, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 4.15/1.74  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.15/1.74  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.15/1.74  tff(f_164, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.15/1.74  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.15/1.74  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.15/1.74  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.15/1.74  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.15/1.74  tff(c_62, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.15/1.74  tff(c_79, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 4.15/1.74  tff(c_68, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.15/1.74  tff(c_130, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_79, c_68])).
% 4.15/1.74  tff(c_211, plain, (![A_88, B_89]: (m1_pre_topc(k1_tex_2(A_88, B_89), A_88) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.15/1.74  tff(c_216, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_211])).
% 4.15/1.74  tff(c_220, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_216])).
% 4.15/1.74  tff(c_221, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_220])).
% 4.15/1.74  tff(c_323, plain, (![A_93, B_94]: (m1_subset_1('#skF_2'(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_93))) | v1_tex_2(B_94, A_93) | ~m1_pre_topc(B_94, A_93) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.15/1.74  tff(c_34, plain, (![B_34, A_33]: (v1_subset_1(B_34, A_33) | B_34=A_33 | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.15/1.74  tff(c_688, plain, (![A_135, B_136]: (v1_subset_1('#skF_2'(A_135, B_136), u1_struct_0(A_135)) | u1_struct_0(A_135)='#skF_2'(A_135, B_136) | v1_tex_2(B_136, A_135) | ~m1_pre_topc(B_136, A_135) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_323, c_34])).
% 4.15/1.74  tff(c_28, plain, (![A_23, B_29]: (~v1_subset_1('#skF_2'(A_23, B_29), u1_struct_0(A_23)) | v1_tex_2(B_29, A_23) | ~m1_pre_topc(B_29, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.15/1.74  tff(c_698, plain, (![A_137, B_138]: (u1_struct_0(A_137)='#skF_2'(A_137, B_138) | v1_tex_2(B_138, A_137) | ~m1_pre_topc(B_138, A_137) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_688, c_28])).
% 4.15/1.74  tff(c_708, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_698, c_79])).
% 4.15/1.74  tff(c_713, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_221, c_708])).
% 4.15/1.74  tff(c_157, plain, (![A_75, B_76]: (~v2_struct_0(k1_tex_2(A_75, B_76)) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.15/1.74  tff(c_164, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_157])).
% 4.15/1.74  tff(c_168, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_164])).
% 4.15/1.74  tff(c_169, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_168])).
% 4.15/1.74  tff(c_8, plain, (![B_8, A_6]: (l1_pre_topc(B_8) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.15/1.74  tff(c_226, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_221, c_8])).
% 4.15/1.74  tff(c_232, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_226])).
% 4.15/1.74  tff(c_200, plain, (![B_86, A_87]: (u1_struct_0(B_86)='#skF_2'(A_87, B_86) | v1_tex_2(B_86, A_87) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.15/1.74  tff(c_206, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_200, c_79])).
% 4.15/1.74  tff(c_210, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_206])).
% 4.15/1.74  tff(c_235, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_210])).
% 4.15/1.74  tff(c_12, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.15/1.74  tff(c_273, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_12])).
% 4.15/1.74  tff(c_303, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_169, c_273])).
% 4.15/1.74  tff(c_305, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_303])).
% 4.15/1.74  tff(c_308, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_305])).
% 4.15/1.74  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_308])).
% 4.15/1.74  tff(c_314, plain, (l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_303])).
% 4.15/1.74  tff(c_184, plain, (![A_81, B_82]: (v7_struct_0(k1_tex_2(A_81, B_82)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.15/1.74  tff(c_191, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_184])).
% 4.15/1.74  tff(c_195, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_191])).
% 4.15/1.74  tff(c_196, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_195])).
% 4.15/1.74  tff(c_427, plain, (![A_106, B_107]: (~v7_struct_0(A_106) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_106), B_107), u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_struct_0(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.15/1.74  tff(c_434, plain, (![B_107]: (~v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v1_subset_1(k6_domain_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')), B_107), u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))) | ~m1_subset_1(B_107, u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_235, c_427])).
% 4.15/1.74  tff(c_447, plain, (![B_107]: (~v1_subset_1(k6_domain_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')), B_107), '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~m1_subset_1(B_107, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_235, c_235, c_196, c_434])).
% 4.15/1.74  tff(c_448, plain, (![B_107]: (~v1_subset_1(k6_domain_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')), B_107), '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~m1_subset_1(B_107, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_169, c_447])).
% 4.15/1.74  tff(c_982, plain, (![B_149]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), B_149), u1_struct_0('#skF_3')) | ~m1_subset_1(B_149, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_713, c_713, c_448])).
% 4.15/1.74  tff(c_989, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_130, c_982])).
% 4.15/1.74  tff(c_1000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_989])).
% 4.15/1.74  tff(c_1002, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 4.15/1.74  tff(c_1336, plain, (![B_208, A_209]: (~v1_tex_2(B_208, A_209) | u1_struct_0(B_208)!=u1_struct_0(A_209) | ~m1_pre_topc(B_208, A_209) | ~l1_pre_topc(A_209))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.15/1.74  tff(c_1339, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1002, c_1336])).
% 4.15/1.74  tff(c_1342, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1339])).
% 4.15/1.74  tff(c_1356, plain, (~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1342])).
% 4.15/1.74  tff(c_1391, plain, (![A_221, B_222]: (m1_pre_topc(k1_tex_2(A_221, B_222), A_221) | ~m1_subset_1(B_222, u1_struct_0(A_221)) | ~l1_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.15/1.74  tff(c_1396, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1391])).
% 4.15/1.74  tff(c_1400, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1396])).
% 4.15/1.74  tff(c_1402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1356, c_1400])).
% 4.15/1.74  tff(c_1404, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_1342])).
% 4.15/1.74  tff(c_1407, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1404, c_8])).
% 4.15/1.74  tff(c_1410, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1407])).
% 4.15/1.74  tff(c_1403, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))!=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1342])).
% 4.15/1.74  tff(c_1411, plain, (![A_223, B_224]: (~v2_struct_0(k1_tex_2(A_223, B_224)) | ~m1_subset_1(B_224, u1_struct_0(A_223)) | ~l1_pre_topc(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.15/1.74  tff(c_1418, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1411])).
% 4.15/1.74  tff(c_1422, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1418])).
% 4.15/1.74  tff(c_1423, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_1422])).
% 4.15/1.74  tff(c_1033, plain, (![A_160, B_161]: (v1_zfmisc_1(A_160) | k6_domain_1(A_160, B_161)!=A_160 | ~m1_subset_1(B_161, A_160) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.15/1.74  tff(c_1041, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_1033])).
% 4.15/1.74  tff(c_1061, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1041])).
% 4.15/1.74  tff(c_1062, plain, (![A_165, B_166]: (m1_subset_1(k6_domain_1(A_165, B_166), k1_zfmisc_1(A_165)) | ~m1_subset_1(B_166, A_165) | v1_xboole_0(A_165))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.15/1.74  tff(c_1229, plain, (![A_202, B_203]: (v1_subset_1(k6_domain_1(A_202, B_203), A_202) | k6_domain_1(A_202, B_203)=A_202 | ~m1_subset_1(B_203, A_202) | v1_xboole_0(A_202))), inference(resolution, [status(thm)], [c_1062, c_34])).
% 4.15/1.74  tff(c_1001, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 4.15/1.74  tff(c_1236, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1229, c_1001])).
% 4.15/1.74  tff(c_1243, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1236])).
% 4.15/1.74  tff(c_1244, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1061, c_1243])).
% 4.15/1.74  tff(c_1249, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1244, c_12])).
% 4.15/1.74  tff(c_1255, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_1249])).
% 4.15/1.74  tff(c_1258, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1255])).
% 4.15/1.74  tff(c_1262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1258])).
% 4.15/1.74  tff(c_1264, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1041])).
% 4.15/1.74  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(k6_domain_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.15/1.74  tff(c_1286, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_14])).
% 4.15/1.74  tff(c_1290, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1286])).
% 4.15/1.74  tff(c_1292, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1290])).
% 4.15/1.74  tff(c_1295, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1292, c_12])).
% 4.15/1.74  tff(c_1298, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_1295])).
% 4.15/1.74  tff(c_1301, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1298])).
% 4.15/1.74  tff(c_1305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1301])).
% 4.15/1.74  tff(c_1307, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1290])).
% 4.15/1.74  tff(c_1263, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1041])).
% 4.15/1.74  tff(c_1265, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1263])).
% 4.15/1.74  tff(c_18, plain, (![B_18, A_16]: (r1_tarski(u1_struct_0(B_18), u1_struct_0(A_16)) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.15/1.74  tff(c_1028, plain, (![B_158, A_159]: (B_158=A_159 | ~r1_tarski(A_159, B_158) | ~v1_zfmisc_1(B_158) | v1_xboole_0(B_158) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.15/1.74  tff(c_1617, plain, (![B_266, A_267]: (u1_struct_0(B_266)=u1_struct_0(A_267) | ~v1_zfmisc_1(u1_struct_0(A_267)) | v1_xboole_0(u1_struct_0(A_267)) | v1_xboole_0(u1_struct_0(B_266)) | ~m1_pre_topc(B_266, A_267) | ~l1_pre_topc(A_267))), inference(resolution, [status(thm)], [c_18, c_1028])).
% 4.15/1.74  tff(c_1619, plain, (![B_266]: (u1_struct_0(B_266)=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0(B_266)) | ~m1_pre_topc(B_266, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_1265, c_1617])).
% 4.15/1.74  tff(c_1625, plain, (![B_266]: (u1_struct_0(B_266)=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0(B_266)) | ~m1_pre_topc(B_266, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1619])).
% 4.15/1.74  tff(c_1628, plain, (![B_268]: (u1_struct_0(B_268)=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(B_268)) | ~m1_pre_topc(B_268, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1307, c_1625])).
% 4.15/1.74  tff(c_1643, plain, (![B_269]: (~l1_struct_0(B_269) | v2_struct_0(B_269) | u1_struct_0(B_269)=u1_struct_0('#skF_3') | ~m1_pre_topc(B_269, '#skF_3'))), inference(resolution, [status(thm)], [c_1628, c_12])).
% 4.15/1.74  tff(c_1650, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1404, c_1643])).
% 4.15/1.74  tff(c_1657, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1403, c_1423, c_1650])).
% 4.15/1.74  tff(c_1660, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1657])).
% 4.15/1.74  tff(c_1664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1410, c_1660])).
% 4.15/1.74  tff(c_1665, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1263])).
% 4.15/1.74  tff(c_1669, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1665, c_12])).
% 4.15/1.74  tff(c_1672, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_1669])).
% 4.15/1.74  tff(c_1675, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1672])).
% 4.15/1.74  tff(c_1679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1675])).
% 4.15/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.74  
% 4.15/1.74  Inference rules
% 4.15/1.74  ----------------------
% 4.15/1.74  #Ref     : 0
% 4.15/1.74  #Sup     : 293
% 4.15/1.74  #Fact    : 0
% 4.15/1.74  #Define  : 0
% 4.15/1.74  #Split   : 15
% 4.15/1.74  #Chain   : 0
% 4.15/1.74  #Close   : 0
% 4.15/1.74  
% 4.15/1.74  Ordering : KBO
% 4.15/1.74  
% 4.15/1.74  Simplification rules
% 4.15/1.74  ----------------------
% 4.15/1.74  #Subsume      : 76
% 4.15/1.74  #Demod        : 193
% 4.15/1.74  #Tautology    : 39
% 4.15/1.74  #SimpNegUnit  : 75
% 4.15/1.74  #BackRed      : 14
% 4.15/1.74  
% 4.15/1.74  #Partial instantiations: 0
% 4.15/1.74  #Strategies tried      : 1
% 4.15/1.74  
% 4.15/1.74  Timing (in seconds)
% 4.15/1.74  ----------------------
% 4.15/1.74  Preprocessing        : 0.36
% 4.15/1.74  Parsing              : 0.19
% 4.15/1.74  CNF conversion       : 0.03
% 4.15/1.74  Main loop            : 0.59
% 4.15/1.74  Inferencing          : 0.23
% 4.15/1.74  Reduction            : 0.17
% 4.15/1.74  Demodulation         : 0.11
% 4.15/1.74  BG Simplification    : 0.03
% 4.15/1.74  Subsumption          : 0.11
% 4.15/1.74  Abstraction          : 0.03
% 4.15/1.74  MUC search           : 0.00
% 4.15/1.74  Cooper               : 0.00
% 4.15/1.74  Total                : 1.01
% 4.15/1.74  Index Insertion      : 0.00
% 4.15/1.74  Index Deletion       : 0.00
% 4.15/1.74  Index Matching       : 0.00
% 4.15/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------

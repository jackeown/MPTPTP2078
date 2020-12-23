%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:01 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 539 expanded)
%              Number of leaves         :   37 ( 189 expanded)
%              Depth                    :   15
%              Number of atoms          :  353 (1498 expanded)
%              Number of equality atoms :   28 (  69 expanded)
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

tff(f_176,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_150,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_122,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

tff(f_101,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1068,plain,(
    ! [A_173,B_174] :
      ( m1_pre_topc(k1_tex_2(A_173,B_174),A_173)
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ l1_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1073,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1068])).

tff(c_1077,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1073])).

tff(c_1078,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1077])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1081,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1078,c_6])).

tff(c_1084,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1081])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_750,plain,(
    ! [A_132,B_133] :
      ( ~ v2_struct_0(k1_tex_2(A_132,B_133))
      | ~ m1_subset_1(B_133,u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_757,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_750])).

tff(c_761,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_757])).

tff(c_762,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_761])).

tff(c_791,plain,(
    ! [A_140,B_141] :
      ( m1_pre_topc(k1_tex_2(A_140,B_141),A_140)
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_796,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_791])).

tff(c_800,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_796])).

tff(c_801,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_800])).

tff(c_64,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_75,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_367,plain,(
    ! [A_87,B_88] :
      ( ~ v7_struct_0(A_87)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_87),B_88),u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_380,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_367])).

tff(c_389,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_380])).

tff(c_390,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_389])).

tff(c_391,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_394,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_391])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_394])).

tff(c_399,plain,(
    ~ v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_400,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_190,plain,(
    ! [A_69,B_70] :
      ( m1_pre_topc(k1_tex_2(A_69,B_70),A_69)
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_195,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_190])).

tff(c_199,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_195])).

tff(c_200,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_199])).

tff(c_215,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_2'(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | v1_tex_2(B_79,A_78)
      | ~ m1_pre_topc(B_79,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ! [B_33,A_32] :
      ( v1_subset_1(B_33,A_32)
      | B_33 = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_613,plain,(
    ! [A_116,B_117] :
      ( v1_subset_1('#skF_2'(A_116,B_117),u1_struct_0(A_116))
      | u1_struct_0(A_116) = '#skF_2'(A_116,B_117)
      | v1_tex_2(B_117,A_116)
      | ~ m1_pre_topc(B_117,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_215,c_34])).

tff(c_28,plain,(
    ! [A_22,B_28] :
      ( ~ v1_subset_1('#skF_2'(A_22,B_28),u1_struct_0(A_22))
      | v1_tex_2(B_28,A_22)
      | ~ m1_pre_topc(B_28,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_623,plain,(
    ! [A_118,B_119] :
      ( u1_struct_0(A_118) = '#skF_2'(A_118,B_119)
      | v1_tex_2(B_119,A_118)
      | ~ m1_pre_topc(B_119,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_613,c_28])).

tff(c_58,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_155,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_58])).

tff(c_633,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_623,c_155])).

tff(c_638,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_200,c_633])).

tff(c_203,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_200,c_6])).

tff(c_206,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_203])).

tff(c_169,plain,(
    ! [A_65,B_66] :
      ( v7_struct_0(k1_tex_2(A_65,B_66))
      | ~ m1_subset_1(B_66,u1_struct_0(A_65))
      | ~ l1_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_176,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_169])).

tff(c_180,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_176])).

tff(c_181,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_180])).

tff(c_182,plain,(
    ! [B_67,A_68] :
      ( u1_struct_0(B_67) = '#skF_2'(A_68,B_67)
      | v1_tex_2(B_67,A_68)
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_185,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_182,c_155])).

tff(c_188,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_185])).

tff(c_246,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_188])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_296,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_10])).

tff(c_330,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_296])).

tff(c_357,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_360,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_357])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_360])).

tff(c_365,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_651,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_365])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_671,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_651,c_8])).

tff(c_674,plain,(
    v7_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_671])).

tff(c_676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_674])).

tff(c_677,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_808,plain,(
    ! [B_142,A_143] :
      ( ~ v1_tex_2(B_142,A_143)
      | v2_struct_0(B_142)
      | ~ m1_pre_topc(B_142,A_143)
      | ~ l1_pre_topc(A_143)
      | ~ v7_struct_0(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_814,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_677,c_808])).

tff(c_818,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_801,c_814])).

tff(c_819,plain,(
    ~ v7_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_762,c_818])).

tff(c_804,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_801,c_6])).

tff(c_807,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_804])).

tff(c_776,plain,(
    ! [A_136,B_137] :
      ( v7_struct_0(k1_tex_2(A_136,B_137))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_783,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_776])).

tff(c_787,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_783])).

tff(c_788,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_787])).

tff(c_718,plain,(
    ! [A_127,B_128] :
      ( v1_zfmisc_1(A_127)
      | k6_domain_1(A_127,B_128) != A_127
      | ~ m1_subset_1(B_128,A_127)
      | v1_xboole_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_730,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_718])).

tff(c_789,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_730])).

tff(c_706,plain,(
    ! [A_125,B_126] :
      ( m1_subset_1(k6_domain_1(A_125,B_126),k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,A_125)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_835,plain,(
    ! [A_153,B_154] :
      ( v1_subset_1(k6_domain_1(A_153,B_154),A_153)
      | k6_domain_1(A_153,B_154) = A_153
      | ~ m1_subset_1(B_154,A_153)
      | v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_706,c_34])).

tff(c_679,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_679])).

tff(c_682,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_838,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_835,c_682])).

tff(c_844,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_838])).

tff(c_845,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_789,c_844])).

tff(c_731,plain,(
    ! [B_129,A_130] :
      ( m1_subset_1(u1_struct_0(B_129),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_823,plain,(
    ! [B_149,A_150] :
      ( v1_subset_1(u1_struct_0(B_149),u1_struct_0(A_150))
      | u1_struct_0(B_149) = u1_struct_0(A_150)
      | ~ m1_pre_topc(B_149,A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(resolution,[status(thm)],[c_731,c_34])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( ~ v1_subset_1(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_746,plain,(
    ! [B_129,A_130] :
      ( ~ v1_subset_1(u1_struct_0(B_129),u1_struct_0(A_130))
      | ~ v1_xboole_0(u1_struct_0(A_130))
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_731,c_2])).

tff(c_831,plain,(
    ! [A_150,B_149] :
      ( ~ v1_xboole_0(u1_struct_0(A_150))
      | u1_struct_0(B_149) = u1_struct_0(A_150)
      | ~ m1_pre_topc(B_149,A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(resolution,[status(thm)],[c_823,c_746])).

tff(c_847,plain,(
    ! [B_149] :
      ( u1_struct_0(B_149) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_149,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_845,c_831])).

tff(c_851,plain,(
    ! [B_155] :
      ( u1_struct_0(B_155) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_155,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_847])).

tff(c_855,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_801,c_851])).

tff(c_918,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_855,c_10])).

tff(c_952,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_918])).

tff(c_954,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_952])).

tff(c_957,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_954])).

tff(c_961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_957])).

tff(c_962,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_967,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_962,c_8])).

tff(c_970,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_967])).

tff(c_973,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_970])).

tff(c_977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_973])).

tff(c_978,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_730])).

tff(c_980,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_978])).

tff(c_984,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_980,c_8])).

tff(c_985,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_984])).

tff(c_999,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_985])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_999])).

tff(c_1004,plain,(
    v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_984])).

tff(c_1018,plain,(
    ! [A_163,B_164] :
      ( m1_pre_topc(k1_tex_2(A_163,B_164),A_163)
      | ~ m1_subset_1(B_164,u1_struct_0(A_163))
      | ~ l1_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1023,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1018])).

tff(c_1027,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1023])).

tff(c_1028,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1027])).

tff(c_1037,plain,(
    ! [B_169,A_170] :
      ( ~ v1_tex_2(B_169,A_170)
      | v2_struct_0(B_169)
      | ~ m1_pre_topc(B_169,A_170)
      | ~ l1_pre_topc(A_170)
      | ~ v7_struct_0(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1043,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_677,c_1037])).

tff(c_1047,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_54,c_1028,c_1043])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_762,c_1047])).

tff(c_1051,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_978])).

tff(c_1050,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_978])).

tff(c_1163,plain,(
    ! [B_191,A_192] :
      ( v1_subset_1(u1_struct_0(B_191),u1_struct_0(A_192))
      | u1_struct_0(B_191) = u1_struct_0(A_192)
      | ~ m1_pre_topc(B_191,A_192)
      | ~ l1_pre_topc(A_192) ) ),
    inference(resolution,[status(thm)],[c_731,c_34])).

tff(c_1187,plain,(
    ! [A_193,B_194] :
      ( ~ v1_xboole_0(u1_struct_0(A_193))
      | u1_struct_0(B_194) = u1_struct_0(A_193)
      | ~ m1_pre_topc(B_194,A_193)
      | ~ l1_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_1163,c_746])).

tff(c_1189,plain,(
    ! [B_194] :
      ( u1_struct_0(B_194) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_194,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1050,c_1187])).

tff(c_1193,plain,(
    ! [B_195] :
      ( u1_struct_0(B_195) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_195,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1189])).

tff(c_1197,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1078,c_1193])).

tff(c_1253,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1197,c_10])).

tff(c_1293,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_1253])).

tff(c_1294,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1051,c_1293])).

tff(c_1298,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_1294])).

tff(c_1302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.56  
% 3.45/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.56  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.45/1.56  
% 3.45/1.56  %Foreground sorts:
% 3.45/1.56  
% 3.45/1.56  
% 3.45/1.56  %Background operators:
% 3.45/1.56  
% 3.45/1.56  
% 3.45/1.56  %Foreground operators:
% 3.45/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.45/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.56  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.45/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.45/1.56  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.45/1.56  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.45/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.45/1.56  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.45/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.56  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.45/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.45/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.56  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.45/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.45/1.56  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.45/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.45/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.45/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.45/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.56  
% 3.45/1.58  tff(f_176, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 3.45/1.58  tff(f_136, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.45/1.58  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.45/1.58  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.45/1.58  tff(f_150, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.45/1.58  tff(f_163, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 3.45/1.58  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 3.45/1.58  tff(f_122, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.45/1.58  tff(f_58, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.45/1.58  tff(f_52, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.45/1.58  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 3.45/1.58  tff(f_101, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 3.45/1.58  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.45/1.58  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.45/1.58  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 3.45/1.58  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 3.45/1.58  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 3.45/1.58  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 3.45/1.58  tff(c_1068, plain, (![A_173, B_174]: (m1_pre_topc(k1_tex_2(A_173, B_174), A_173) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~l1_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.45/1.58  tff(c_1073, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1068])).
% 3.45/1.58  tff(c_1077, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1073])).
% 3.45/1.58  tff(c_1078, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_1077])).
% 3.45/1.58  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.45/1.58  tff(c_1081, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1078, c_6])).
% 3.45/1.58  tff(c_1084, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1081])).
% 3.45/1.58  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.45/1.58  tff(c_750, plain, (![A_132, B_133]: (~v2_struct_0(k1_tex_2(A_132, B_133)) | ~m1_subset_1(B_133, u1_struct_0(A_132)) | ~l1_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.45/1.58  tff(c_757, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_750])).
% 3.45/1.58  tff(c_761, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_757])).
% 3.45/1.58  tff(c_762, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_761])).
% 3.45/1.58  tff(c_791, plain, (![A_140, B_141]: (m1_pre_topc(k1_tex_2(A_140, B_141), A_140) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.45/1.58  tff(c_796, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_791])).
% 3.45/1.58  tff(c_800, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_796])).
% 3.45/1.58  tff(c_801, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_800])).
% 3.45/1.58  tff(c_64, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 3.45/1.58  tff(c_75, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 3.45/1.58  tff(c_367, plain, (![A_87, B_88]: (~v7_struct_0(A_87) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_87), B_88), u1_struct_0(A_87)) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.45/1.58  tff(c_380, plain, (~v7_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_75, c_367])).
% 3.45/1.58  tff(c_389, plain, (~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_380])).
% 3.45/1.58  tff(c_390, plain, (~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_389])).
% 3.45/1.58  tff(c_391, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_390])).
% 3.45/1.58  tff(c_394, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_391])).
% 3.45/1.58  tff(c_398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_394])).
% 3.45/1.58  tff(c_399, plain, (~v7_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_390])).
% 3.45/1.58  tff(c_400, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_390])).
% 3.45/1.58  tff(c_190, plain, (![A_69, B_70]: (m1_pre_topc(k1_tex_2(A_69, B_70), A_69) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l1_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.45/1.58  tff(c_195, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_190])).
% 3.45/1.58  tff(c_199, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_195])).
% 3.45/1.58  tff(c_200, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_199])).
% 3.45/1.58  tff(c_215, plain, (![A_78, B_79]: (m1_subset_1('#skF_2'(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | v1_tex_2(B_79, A_78) | ~m1_pre_topc(B_79, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.45/1.58  tff(c_34, plain, (![B_33, A_32]: (v1_subset_1(B_33, A_32) | B_33=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.45/1.58  tff(c_613, plain, (![A_116, B_117]: (v1_subset_1('#skF_2'(A_116, B_117), u1_struct_0(A_116)) | u1_struct_0(A_116)='#skF_2'(A_116, B_117) | v1_tex_2(B_117, A_116) | ~m1_pre_topc(B_117, A_116) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_215, c_34])).
% 3.45/1.58  tff(c_28, plain, (![A_22, B_28]: (~v1_subset_1('#skF_2'(A_22, B_28), u1_struct_0(A_22)) | v1_tex_2(B_28, A_22) | ~m1_pre_topc(B_28, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.45/1.58  tff(c_623, plain, (![A_118, B_119]: (u1_struct_0(A_118)='#skF_2'(A_118, B_119) | v1_tex_2(B_119, A_118) | ~m1_pre_topc(B_119, A_118) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_613, c_28])).
% 3.45/1.58  tff(c_58, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 3.45/1.58  tff(c_155, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58])).
% 3.45/1.58  tff(c_633, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_623, c_155])).
% 3.45/1.58  tff(c_638, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_200, c_633])).
% 3.45/1.58  tff(c_203, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_200, c_6])).
% 3.45/1.58  tff(c_206, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_203])).
% 3.45/1.58  tff(c_169, plain, (![A_65, B_66]: (v7_struct_0(k1_tex_2(A_65, B_66)) | ~m1_subset_1(B_66, u1_struct_0(A_65)) | ~l1_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.45/1.58  tff(c_176, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_169])).
% 3.45/1.58  tff(c_180, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_176])).
% 3.45/1.58  tff(c_181, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_180])).
% 3.45/1.58  tff(c_182, plain, (![B_67, A_68]: (u1_struct_0(B_67)='#skF_2'(A_68, B_67) | v1_tex_2(B_67, A_68) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.45/1.58  tff(c_185, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_182, c_155])).
% 3.45/1.58  tff(c_188, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_185])).
% 3.45/1.58  tff(c_246, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_188])).
% 3.45/1.58  tff(c_10, plain, (![A_9]: (v1_zfmisc_1(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.45/1.58  tff(c_296, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_10])).
% 3.45/1.58  tff(c_330, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_296])).
% 3.45/1.58  tff(c_357, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_330])).
% 3.45/1.58  tff(c_360, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_357])).
% 3.45/1.58  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_360])).
% 3.45/1.58  tff(c_365, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_330])).
% 3.45/1.58  tff(c_651, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_638, c_365])).
% 3.45/1.58  tff(c_8, plain, (![A_8]: (~v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.45/1.58  tff(c_671, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_651, c_8])).
% 3.45/1.58  tff(c_674, plain, (v7_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_671])).
% 3.45/1.58  tff(c_676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_399, c_674])).
% 3.45/1.58  tff(c_677, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 3.45/1.58  tff(c_808, plain, (![B_142, A_143]: (~v1_tex_2(B_142, A_143) | v2_struct_0(B_142) | ~m1_pre_topc(B_142, A_143) | ~l1_pre_topc(A_143) | ~v7_struct_0(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.45/1.58  tff(c_814, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_677, c_808])).
% 3.45/1.58  tff(c_818, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_801, c_814])).
% 3.45/1.58  tff(c_819, plain, (~v7_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_762, c_818])).
% 3.45/1.58  tff(c_804, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_801, c_6])).
% 3.45/1.58  tff(c_807, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_804])).
% 3.45/1.58  tff(c_776, plain, (![A_136, B_137]: (v7_struct_0(k1_tex_2(A_136, B_137)) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.45/1.58  tff(c_783, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_776])).
% 3.45/1.58  tff(c_787, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_783])).
% 3.45/1.58  tff(c_788, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_787])).
% 3.45/1.58  tff(c_718, plain, (![A_127, B_128]: (v1_zfmisc_1(A_127) | k6_domain_1(A_127, B_128)!=A_127 | ~m1_subset_1(B_128, A_127) | v1_xboole_0(A_127))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.45/1.58  tff(c_730, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_718])).
% 3.45/1.58  tff(c_789, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_730])).
% 3.45/1.58  tff(c_706, plain, (![A_125, B_126]: (m1_subset_1(k6_domain_1(A_125, B_126), k1_zfmisc_1(A_125)) | ~m1_subset_1(B_126, A_125) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.45/1.58  tff(c_835, plain, (![A_153, B_154]: (v1_subset_1(k6_domain_1(A_153, B_154), A_153) | k6_domain_1(A_153, B_154)=A_153 | ~m1_subset_1(B_154, A_153) | v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_706, c_34])).
% 3.45/1.58  tff(c_679, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 3.45/1.58  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_677, c_679])).
% 3.45/1.58  tff(c_682, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 3.45/1.58  tff(c_838, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_835, c_682])).
% 3.45/1.58  tff(c_844, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_838])).
% 3.45/1.58  tff(c_845, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_789, c_844])).
% 3.45/1.58  tff(c_731, plain, (![B_129, A_130]: (m1_subset_1(u1_struct_0(B_129), k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.45/1.58  tff(c_823, plain, (![B_149, A_150]: (v1_subset_1(u1_struct_0(B_149), u1_struct_0(A_150)) | u1_struct_0(B_149)=u1_struct_0(A_150) | ~m1_pre_topc(B_149, A_150) | ~l1_pre_topc(A_150))), inference(resolution, [status(thm)], [c_731, c_34])).
% 3.45/1.58  tff(c_2, plain, (![B_3, A_1]: (~v1_subset_1(B_3, A_1) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.45/1.58  tff(c_746, plain, (![B_129, A_130]: (~v1_subset_1(u1_struct_0(B_129), u1_struct_0(A_130)) | ~v1_xboole_0(u1_struct_0(A_130)) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_731, c_2])).
% 3.45/1.58  tff(c_831, plain, (![A_150, B_149]: (~v1_xboole_0(u1_struct_0(A_150)) | u1_struct_0(B_149)=u1_struct_0(A_150) | ~m1_pre_topc(B_149, A_150) | ~l1_pre_topc(A_150))), inference(resolution, [status(thm)], [c_823, c_746])).
% 3.45/1.58  tff(c_847, plain, (![B_149]: (u1_struct_0(B_149)=u1_struct_0('#skF_3') | ~m1_pre_topc(B_149, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_845, c_831])).
% 3.45/1.58  tff(c_851, plain, (![B_155]: (u1_struct_0(B_155)=u1_struct_0('#skF_3') | ~m1_pre_topc(B_155, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_847])).
% 3.45/1.58  tff(c_855, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_801, c_851])).
% 3.45/1.58  tff(c_918, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_855, c_10])).
% 3.45/1.58  tff(c_952, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_788, c_918])).
% 3.45/1.58  tff(c_954, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_952])).
% 3.45/1.58  tff(c_957, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_954])).
% 3.45/1.58  tff(c_961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_807, c_957])).
% 3.45/1.58  tff(c_962, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_952])).
% 3.45/1.58  tff(c_967, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_962, c_8])).
% 3.45/1.58  tff(c_970, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_819, c_967])).
% 3.45/1.58  tff(c_973, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_970])).
% 3.45/1.58  tff(c_977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_973])).
% 3.45/1.58  tff(c_978, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_730])).
% 3.45/1.58  tff(c_980, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_978])).
% 3.45/1.58  tff(c_984, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_980, c_8])).
% 3.45/1.58  tff(c_985, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_984])).
% 3.45/1.58  tff(c_999, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_985])).
% 3.45/1.58  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_999])).
% 3.45/1.58  tff(c_1004, plain, (v7_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_984])).
% 3.45/1.58  tff(c_1018, plain, (![A_163, B_164]: (m1_pre_topc(k1_tex_2(A_163, B_164), A_163) | ~m1_subset_1(B_164, u1_struct_0(A_163)) | ~l1_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.45/1.58  tff(c_1023, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1018])).
% 3.45/1.58  tff(c_1027, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1023])).
% 3.45/1.58  tff(c_1028, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_1027])).
% 3.45/1.58  tff(c_1037, plain, (![B_169, A_170]: (~v1_tex_2(B_169, A_170) | v2_struct_0(B_169) | ~m1_pre_topc(B_169, A_170) | ~l1_pre_topc(A_170) | ~v7_struct_0(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.45/1.58  tff(c_1043, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_677, c_1037])).
% 3.45/1.58  tff(c_1047, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_54, c_1028, c_1043])).
% 3.45/1.58  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_762, c_1047])).
% 3.45/1.58  tff(c_1051, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_978])).
% 3.45/1.58  tff(c_1050, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_978])).
% 3.45/1.58  tff(c_1163, plain, (![B_191, A_192]: (v1_subset_1(u1_struct_0(B_191), u1_struct_0(A_192)) | u1_struct_0(B_191)=u1_struct_0(A_192) | ~m1_pre_topc(B_191, A_192) | ~l1_pre_topc(A_192))), inference(resolution, [status(thm)], [c_731, c_34])).
% 3.45/1.58  tff(c_1187, plain, (![A_193, B_194]: (~v1_xboole_0(u1_struct_0(A_193)) | u1_struct_0(B_194)=u1_struct_0(A_193) | ~m1_pre_topc(B_194, A_193) | ~l1_pre_topc(A_193))), inference(resolution, [status(thm)], [c_1163, c_746])).
% 3.45/1.58  tff(c_1189, plain, (![B_194]: (u1_struct_0(B_194)=u1_struct_0('#skF_3') | ~m1_pre_topc(B_194, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_1050, c_1187])).
% 3.45/1.58  tff(c_1193, plain, (![B_195]: (u1_struct_0(B_195)=u1_struct_0('#skF_3') | ~m1_pre_topc(B_195, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1189])).
% 3.45/1.58  tff(c_1197, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1078, c_1193])).
% 3.45/1.58  tff(c_1253, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1197, c_10])).
% 3.45/1.58  tff(c_1293, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_788, c_1253])).
% 3.45/1.58  tff(c_1294, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1051, c_1293])).
% 3.45/1.58  tff(c_1298, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_1294])).
% 3.45/1.58  tff(c_1302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1298])).
% 3.45/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.58  
% 3.45/1.58  Inference rules
% 3.45/1.58  ----------------------
% 3.45/1.58  #Ref     : 0
% 3.45/1.58  #Sup     : 226
% 3.45/1.58  #Fact    : 0
% 3.45/1.58  #Define  : 0
% 3.45/1.58  #Split   : 13
% 3.45/1.58  #Chain   : 0
% 3.45/1.58  #Close   : 0
% 3.45/1.58  
% 3.45/1.58  Ordering : KBO
% 3.45/1.58  
% 3.45/1.58  Simplification rules
% 3.45/1.58  ----------------------
% 3.45/1.58  #Subsume      : 24
% 3.45/1.58  #Demod        : 186
% 3.45/1.58  #Tautology    : 42
% 3.45/1.58  #SimpNegUnit  : 52
% 3.45/1.58  #BackRed      : 16
% 3.45/1.58  
% 3.45/1.58  #Partial instantiations: 0
% 3.45/1.58  #Strategies tried      : 1
% 3.45/1.58  
% 3.45/1.58  Timing (in seconds)
% 3.45/1.58  ----------------------
% 3.45/1.59  Preprocessing        : 0.35
% 3.45/1.59  Parsing              : 0.19
% 3.45/1.59  CNF conversion       : 0.02
% 3.45/1.59  Main loop            : 0.46
% 3.45/1.59  Inferencing          : 0.18
% 3.45/1.59  Reduction            : 0.14
% 3.45/1.59  Demodulation         : 0.09
% 3.45/1.59  BG Simplification    : 0.03
% 3.45/1.59  Subsumption          : 0.08
% 3.45/1.59  Abstraction          : 0.03
% 3.45/1.59  MUC search           : 0.00
% 3.45/1.59  Cooper               : 0.00
% 3.45/1.59  Total                : 0.86
% 3.45/1.59  Index Insertion      : 0.00
% 3.45/1.59  Index Deletion       : 0.00
% 3.45/1.59  Index Matching       : 0.00
% 3.45/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

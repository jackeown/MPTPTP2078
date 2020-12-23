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
% DateTime   : Thu Dec  3 10:29:06 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 339 expanded)
%              Number of leaves         :   34 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  269 ( 937 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_162,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_136,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_90,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ v1_xboole_0(B)
           => ( ~ v1_xboole_0(B)
              & ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tex_2)).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_531,plain,(
    ! [A_114,B_115] :
      ( m1_pre_topc(k1_tex_2(A_114,B_115),A_114)
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_533,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_531])).

tff(c_536,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_533])).

tff(c_537,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_536])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_540,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_537,c_4])).

tff(c_543,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_540])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_505,plain,(
    ! [A_104,B_105] :
      ( ~ v2_struct_0(k1_tex_2(A_104,B_105))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_508,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_505])).

tff(c_511,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_508])).

tff(c_512,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_511])).

tff(c_566,plain,(
    ! [A_124,B_125] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(A_124),B_125),u1_struct_0(A_124))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_struct_0(A_124)
      | v7_struct_0(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_52,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_65,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_101,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_58])).

tff(c_102,plain,(
    ! [A_56,B_57] :
      ( ~ v1_zfmisc_1(A_56)
      | ~ v1_subset_1(k6_domain_1(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_105,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_101,c_102])).

tff(c_108,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_105])).

tff(c_109,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_122,plain,(
    ! [A_60,B_61] :
      ( m1_pre_topc(k1_tex_2(A_60,B_61),A_60)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_124,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_122])).

tff(c_127,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_124])).

tff(c_128,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_127])).

tff(c_244,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1('#skF_1'(A_72,B_73),k1_zfmisc_1(u1_struct_0(A_72)))
      | v1_tex_2(B_73,A_72)
      | ~ m1_pre_topc(B_73,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [B_24,A_23] :
      ( v1_subset_1(B_24,A_23)
      | B_24 = A_23
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_407,plain,(
    ! [A_95,B_96] :
      ( v1_subset_1('#skF_1'(A_95,B_96),u1_struct_0(A_95))
      | u1_struct_0(A_95) = '#skF_1'(A_95,B_96)
      | v1_tex_2(B_96,A_95)
      | ~ m1_pre_topc(B_96,A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_244,c_24])).

tff(c_18,plain,(
    ! [A_13,B_19] :
      ( ~ v1_subset_1('#skF_1'(A_13,B_19),u1_struct_0(A_13))
      | v1_tex_2(B_19,A_13)
      | ~ m1_pre_topc(B_19,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_417,plain,(
    ! [A_97,B_98] :
      ( u1_struct_0(A_97) = '#skF_1'(A_97,B_98)
      | v1_tex_2(B_98,A_97)
      | ~ m1_pre_topc(B_98,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_407,c_18])).

tff(c_428,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_417,c_65])).

tff(c_435,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_128,c_428])).

tff(c_131,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_134,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_131])).

tff(c_77,plain,(
    ! [A_50,B_51] :
      ( ~ v2_struct_0(k1_tex_2(A_50,B_51))
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l1_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_80,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_77])).

tff(c_83,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80])).

tff(c_84,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_83])).

tff(c_115,plain,(
    ! [B_58,A_59] :
      ( u1_struct_0(B_58) = '#skF_1'(A_59,B_58)
      | v1_tex_2(B_58,A_59)
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_118,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_65])).

tff(c_121,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_118])).

tff(c_136,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_121])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_163,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_6])).

tff(c_187,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_163])).

tff(c_191,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_194,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_194])).

tff(c_200,plain,(
    l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_85,plain,(
    ! [A_52,B_53] :
      ( v7_struct_0(k1_tex_2(A_52,B_53))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_88,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_85])).

tff(c_91,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_88])).

tff(c_92,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_91])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | ~ v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_166,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_8])).

tff(c_189,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_166])).

tff(c_202,plain,(
    v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_189])).

tff(c_467,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_202])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_467])).

tff(c_472,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_476,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_472,c_6])).

tff(c_479,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_476])).

tff(c_482,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_479])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_482])).

tff(c_487,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_489,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_489])).

tff(c_492,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_572,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_566,c_492])).

tff(c_576,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_572])).

tff(c_577,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_576])).

tff(c_583,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_586,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_583])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_586])).

tff(c_591,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_592,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_488,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( m1_subset_1(u1_struct_0(B_9),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_601,plain,(
    ! [B_130,A_131] :
      ( v1_subset_1(u1_struct_0(B_130),u1_struct_0(A_131))
      | ~ m1_subset_1(u1_struct_0(B_130),k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v1_tex_2(B_130,A_131)
      | ~ m1_pre_topc(B_130,A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_605,plain,(
    ! [B_9,A_7] :
      ( v1_subset_1(u1_struct_0(B_9),u1_struct_0(A_7))
      | ~ v1_tex_2(B_9,A_7)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_601])).

tff(c_557,plain,(
    ! [B_122,A_123] :
      ( ~ v1_subset_1(B_122,u1_struct_0(A_123))
      | v1_xboole_0(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_struct_0(A_123)
      | ~ v7_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_619,plain,(
    ! [B_136,A_137] :
      ( ~ v1_subset_1(u1_struct_0(B_136),u1_struct_0(A_137))
      | v1_xboole_0(u1_struct_0(B_136))
      | ~ l1_struct_0(A_137)
      | ~ v7_struct_0(A_137)
      | v2_struct_0(A_137)
      | ~ m1_pre_topc(B_136,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_10,c_557])).

tff(c_628,plain,(
    ! [B_138,A_139] :
      ( v1_xboole_0(u1_struct_0(B_138))
      | ~ l1_struct_0(A_139)
      | ~ v7_struct_0(A_139)
      | v2_struct_0(A_139)
      | ~ v1_tex_2(B_138,A_139)
      | ~ m1_pre_topc(B_138,A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_605,c_619])).

tff(c_632,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_488,c_628])).

tff(c_636,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_537,c_591,c_592,c_632])).

tff(c_637,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_636])).

tff(c_640,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_637,c_6])).

tff(c_643,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_512,c_640])).

tff(c_646,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_643])).

tff(c_650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.52  
% 3.09/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.52  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.22/1.52  
% 3.22/1.52  %Foreground sorts:
% 3.22/1.52  
% 3.22/1.52  
% 3.22/1.52  %Background operators:
% 3.22/1.52  
% 3.22/1.52  
% 3.22/1.52  %Foreground operators:
% 3.22/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.52  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.22/1.52  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.22/1.52  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.22/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.22/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.22/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.52  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.22/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.52  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.52  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.22/1.52  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.22/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.52  
% 3.23/1.54  tff(f_175, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 3.23/1.54  tff(f_111, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.23/1.54  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.23/1.54  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.23/1.54  tff(f_125, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.23/1.54  tff(f_162, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tex_2)).
% 3.23/1.54  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.23/1.54  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 3.23/1.54  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.23/1.54  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.23/1.54  tff(f_50, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.23/1.54  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.23/1.54  tff(f_76, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~v1_xboole_0(B) => (~v1_xboole_0(B) & ~v1_subset_1(B, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tex_2)).
% 3.23/1.54  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.23/1.54  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.23/1.54  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.23/1.54  tff(c_531, plain, (![A_114, B_115]: (m1_pre_topc(k1_tex_2(A_114, B_115), A_114) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.23/1.54  tff(c_533, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_531])).
% 3.23/1.54  tff(c_536, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_533])).
% 3.23/1.54  tff(c_537, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_536])).
% 3.23/1.54  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.54  tff(c_540, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_537, c_4])).
% 3.23/1.54  tff(c_543, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_540])).
% 3.23/1.54  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.54  tff(c_505, plain, (![A_104, B_105]: (~v2_struct_0(k1_tex_2(A_104, B_105)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.23/1.54  tff(c_508, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_505])).
% 3.23/1.54  tff(c_511, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_508])).
% 3.23/1.54  tff(c_512, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_511])).
% 3.23/1.54  tff(c_566, plain, (![A_124, B_125]: (v1_subset_1(k6_domain_1(u1_struct_0(A_124), B_125), u1_struct_0(A_124)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_struct_0(A_124) | v7_struct_0(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.23/1.54  tff(c_52, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.23/1.54  tff(c_65, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 3.23/1.54  tff(c_58, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.23/1.54  tff(c_101, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_65, c_58])).
% 3.23/1.54  tff(c_102, plain, (![A_56, B_57]: (~v1_zfmisc_1(A_56) | ~v1_subset_1(k6_domain_1(A_56, B_57), A_56) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.23/1.54  tff(c_105, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_101, c_102])).
% 3.23/1.54  tff(c_108, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_105])).
% 3.23/1.54  tff(c_109, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_108])).
% 3.23/1.54  tff(c_122, plain, (![A_60, B_61]: (m1_pre_topc(k1_tex_2(A_60, B_61), A_60) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.23/1.54  tff(c_124, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_122])).
% 3.23/1.54  tff(c_127, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_124])).
% 3.23/1.54  tff(c_128, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_127])).
% 3.23/1.54  tff(c_244, plain, (![A_72, B_73]: (m1_subset_1('#skF_1'(A_72, B_73), k1_zfmisc_1(u1_struct_0(A_72))) | v1_tex_2(B_73, A_72) | ~m1_pre_topc(B_73, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.23/1.54  tff(c_24, plain, (![B_24, A_23]: (v1_subset_1(B_24, A_23) | B_24=A_23 | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.54  tff(c_407, plain, (![A_95, B_96]: (v1_subset_1('#skF_1'(A_95, B_96), u1_struct_0(A_95)) | u1_struct_0(A_95)='#skF_1'(A_95, B_96) | v1_tex_2(B_96, A_95) | ~m1_pre_topc(B_96, A_95) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_244, c_24])).
% 3.23/1.54  tff(c_18, plain, (![A_13, B_19]: (~v1_subset_1('#skF_1'(A_13, B_19), u1_struct_0(A_13)) | v1_tex_2(B_19, A_13) | ~m1_pre_topc(B_19, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.23/1.54  tff(c_417, plain, (![A_97, B_98]: (u1_struct_0(A_97)='#skF_1'(A_97, B_98) | v1_tex_2(B_98, A_97) | ~m1_pre_topc(B_98, A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_407, c_18])).
% 3.23/1.54  tff(c_428, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_417, c_65])).
% 3.23/1.54  tff(c_435, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_128, c_428])).
% 3.23/1.54  tff(c_131, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_128, c_4])).
% 3.23/1.54  tff(c_134, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_131])).
% 3.23/1.54  tff(c_77, plain, (![A_50, B_51]: (~v2_struct_0(k1_tex_2(A_50, B_51)) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.23/1.54  tff(c_80, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_77])).
% 3.23/1.54  tff(c_83, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80])).
% 3.23/1.54  tff(c_84, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_83])).
% 3.23/1.54  tff(c_115, plain, (![B_58, A_59]: (u1_struct_0(B_58)='#skF_1'(A_59, B_58) | v1_tex_2(B_58, A_59) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.23/1.54  tff(c_118, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_115, c_65])).
% 3.23/1.54  tff(c_121, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_118])).
% 3.23/1.54  tff(c_136, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_121])).
% 3.23/1.54  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.54  tff(c_163, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_6])).
% 3.23/1.54  tff(c_187, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_84, c_163])).
% 3.23/1.54  tff(c_191, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_187])).
% 3.23/1.54  tff(c_194, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_191])).
% 3.23/1.54  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_194])).
% 3.23/1.54  tff(c_200, plain, (l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_187])).
% 3.23/1.54  tff(c_85, plain, (![A_52, B_53]: (v7_struct_0(k1_tex_2(A_52, B_53)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.23/1.54  tff(c_88, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_85])).
% 3.23/1.54  tff(c_91, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_88])).
% 3.23/1.54  tff(c_92, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_91])).
% 3.23/1.54  tff(c_8, plain, (![A_6]: (v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | ~v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/1.54  tff(c_166, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_8])).
% 3.23/1.54  tff(c_189, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_166])).
% 3.23/1.54  tff(c_202, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_189])).
% 3.23/1.54  tff(c_467, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_202])).
% 3.23/1.54  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_467])).
% 3.23/1.54  tff(c_472, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_108])).
% 3.23/1.54  tff(c_476, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_472, c_6])).
% 3.23/1.54  tff(c_479, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_476])).
% 3.23/1.54  tff(c_482, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_479])).
% 3.23/1.54  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_482])).
% 3.23/1.54  tff(c_487, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 3.23/1.54  tff(c_489, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_58])).
% 3.23/1.54  tff(c_490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_487, c_489])).
% 3.23/1.54  tff(c_492, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_58])).
% 3.23/1.54  tff(c_572, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_566, c_492])).
% 3.23/1.54  tff(c_576, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_572])).
% 3.23/1.54  tff(c_577, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_576])).
% 3.23/1.54  tff(c_583, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_577])).
% 3.23/1.54  tff(c_586, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_583])).
% 3.23/1.54  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_586])).
% 3.23/1.54  tff(c_591, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_577])).
% 3.23/1.54  tff(c_592, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_577])).
% 3.23/1.54  tff(c_488, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 3.23/1.54  tff(c_10, plain, (![B_9, A_7]: (m1_subset_1(u1_struct_0(B_9), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.23/1.54  tff(c_601, plain, (![B_130, A_131]: (v1_subset_1(u1_struct_0(B_130), u1_struct_0(A_131)) | ~m1_subset_1(u1_struct_0(B_130), k1_zfmisc_1(u1_struct_0(A_131))) | ~v1_tex_2(B_130, A_131) | ~m1_pre_topc(B_130, A_131) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.23/1.54  tff(c_605, plain, (![B_9, A_7]: (v1_subset_1(u1_struct_0(B_9), u1_struct_0(A_7)) | ~v1_tex_2(B_9, A_7) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_10, c_601])).
% 3.23/1.54  tff(c_557, plain, (![B_122, A_123]: (~v1_subset_1(B_122, u1_struct_0(A_123)) | v1_xboole_0(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_struct_0(A_123) | ~v7_struct_0(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.54  tff(c_619, plain, (![B_136, A_137]: (~v1_subset_1(u1_struct_0(B_136), u1_struct_0(A_137)) | v1_xboole_0(u1_struct_0(B_136)) | ~l1_struct_0(A_137) | ~v7_struct_0(A_137) | v2_struct_0(A_137) | ~m1_pre_topc(B_136, A_137) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_10, c_557])).
% 3.23/1.54  tff(c_628, plain, (![B_138, A_139]: (v1_xboole_0(u1_struct_0(B_138)) | ~l1_struct_0(A_139) | ~v7_struct_0(A_139) | v2_struct_0(A_139) | ~v1_tex_2(B_138, A_139) | ~m1_pre_topc(B_138, A_139) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_605, c_619])).
% 3.23/1.54  tff(c_632, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_488, c_628])).
% 3.23/1.54  tff(c_636, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_537, c_591, c_592, c_632])).
% 3.23/1.54  tff(c_637, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_636])).
% 3.23/1.54  tff(c_640, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_637, c_6])).
% 3.23/1.54  tff(c_643, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_512, c_640])).
% 3.23/1.54  tff(c_646, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_643])).
% 3.23/1.54  tff(c_650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_543, c_646])).
% 3.23/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.54  
% 3.23/1.54  Inference rules
% 3.23/1.54  ----------------------
% 3.23/1.54  #Ref     : 0
% 3.23/1.54  #Sup     : 96
% 3.23/1.54  #Fact    : 0
% 3.23/1.54  #Define  : 0
% 3.23/1.54  #Split   : 7
% 3.23/1.54  #Chain   : 0
% 3.23/1.54  #Close   : 0
% 3.23/1.54  
% 3.23/1.54  Ordering : KBO
% 3.23/1.54  
% 3.23/1.54  Simplification rules
% 3.23/1.54  ----------------------
% 3.23/1.54  #Subsume      : 15
% 3.23/1.54  #Demod        : 101
% 3.23/1.54  #Tautology    : 14
% 3.23/1.54  #SimpNegUnit  : 33
% 3.23/1.54  #BackRed      : 14
% 3.23/1.54  
% 3.23/1.54  #Partial instantiations: 0
% 3.23/1.54  #Strategies tried      : 1
% 3.23/1.54  
% 3.23/1.54  Timing (in seconds)
% 3.23/1.54  ----------------------
% 3.23/1.55  Preprocessing        : 0.37
% 3.23/1.55  Parsing              : 0.20
% 3.23/1.55  CNF conversion       : 0.03
% 3.23/1.55  Main loop            : 0.35
% 3.23/1.55  Inferencing          : 0.13
% 3.23/1.55  Reduction            : 0.11
% 3.23/1.55  Demodulation         : 0.07
% 3.23/1.55  BG Simplification    : 0.02
% 3.23/1.55  Subsumption          : 0.06
% 3.23/1.55  Abstraction          : 0.02
% 3.23/1.55  MUC search           : 0.00
% 3.23/1.55  Cooper               : 0.00
% 3.23/1.55  Total                : 0.76
% 3.23/1.55  Index Insertion      : 0.00
% 3.23/1.55  Index Deletion       : 0.00
% 3.23/1.55  Index Matching       : 0.00
% 3.23/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

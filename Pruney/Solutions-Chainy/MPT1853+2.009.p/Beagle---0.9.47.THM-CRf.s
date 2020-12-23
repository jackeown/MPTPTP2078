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

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 306 expanded)
%              Number of leaves         :   40 ( 116 expanded)
%              Depth                    :   11
%              Number of atoms          :  301 ( 803 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_217,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_168,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_154,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_193,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_182,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_34,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( ~ v1_xboole_0(B)
              & ~ v1_subset_1(B,u1_struct_0(A)) )
           => ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc7_tex_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

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

tff(f_204,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_tex_2)).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_12,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_465,plain,(
    ! [A_109,B_110] :
      ( ~ v2_struct_0(k1_tex_2(A_109,B_110))
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_468,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_465])).

tff(c_471,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_468])).

tff(c_472,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_471])).

tff(c_520,plain,(
    ! [A_117,B_118] :
      ( m1_pre_topc(k1_tex_2(A_117,B_118),A_117)
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_522,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_520])).

tff(c_525,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_522])).

tff(c_526,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_525])).

tff(c_171,plain,(
    ! [A_70,B_71] :
      ( m1_pre_topc(k1_tex_2(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l1_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_173,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_171])).

tff(c_176,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_173])).

tff(c_177,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_176])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( l1_pre_topc(B_9)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_180,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_14])).

tff(c_183,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_180])).

tff(c_125,plain,(
    ! [A_60,B_61] :
      ( ~ v2_struct_0(k1_tex_2(A_60,B_61))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_128,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_131,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_128])).

tff(c_132,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_131])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_86,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_133,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_70])).

tff(c_142,plain,(
    ! [A_64,B_65] :
      ( ~ v1_zfmisc_1(A_64)
      | ~ v1_subset_1(k6_domain_1(A_64,B_65),A_64)
      | ~ m1_subset_1(B_65,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_145,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_133,c_142])).

tff(c_148,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_145])).

tff(c_149,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_158,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_149])).

tff(c_134,plain,(
    ! [A_62,B_63] :
      ( v7_struct_0(k1_tex_2(A_62,B_63))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_137,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_134])).

tff(c_140,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_137])).

tff(c_141,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_140])).

tff(c_101,plain,(
    ! [B_56,A_57] :
      ( m1_subset_1(u1_struct_0(B_56),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [B_25,A_24] :
      ( v1_subset_1(B_25,A_24)
      | B_25 = A_24
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_105,plain,(
    ! [B_56,A_57] :
      ( v1_subset_1(u1_struct_0(B_56),u1_struct_0(A_57))
      | u1_struct_0(B_56) = u1_struct_0(A_57)
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_101,c_34])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( m1_subset_1(u1_struct_0(B_14),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_222,plain,(
    ! [B_82,A_83] :
      ( v1_tex_2(B_82,A_83)
      | ~ v1_subset_1(u1_struct_0(B_82),u1_struct_0(A_83))
      | ~ m1_subset_1(u1_struct_0(B_82),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_pre_topc(B_82,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_238,plain,(
    ! [B_86,A_87] :
      ( v1_tex_2(B_86,A_87)
      | ~ v1_subset_1(u1_struct_0(B_86),u1_struct_0(A_87))
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_20,c_222])).

tff(c_247,plain,(
    ! [B_88,A_89] :
      ( v1_tex_2(B_88,A_89)
      | u1_struct_0(B_88) = u1_struct_0(A_89)
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_105,c_238])).

tff(c_257,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_247,c_86])).

tff(c_263,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_177,c_257])).

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : ~ v1_subset_1(k2_subset_1(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_3] : ~ v1_subset_1(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_8,plain,(
    ! [A_4] : ~ v1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    ! [B_54,A_55] :
      ( v1_subset_1(B_54,A_55)
      | B_54 = A_55
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_97,plain,(
    ! [A_4] :
      ( v1_subset_1('#skF_1'(A_4),A_4)
      | '#skF_1'(A_4) = A_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_94])).

tff(c_100,plain,(
    ! [A_4] : '#skF_1'(A_4) = A_4 ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_97])).

tff(c_106,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_10])).

tff(c_343,plain,(
    ! [B_91,A_92] :
      ( v1_zfmisc_1(B_91)
      | v1_subset_1(B_91,u1_struct_0(A_92))
      | v1_xboole_0(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_struct_0(A_92)
      | ~ v7_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_350,plain,(
    ! [A_92] :
      ( v1_zfmisc_1(u1_struct_0(A_92))
      | v1_subset_1(u1_struct_0(A_92),u1_struct_0(A_92))
      | v1_xboole_0(u1_struct_0(A_92))
      | ~ l1_struct_0(A_92)
      | ~ v7_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_106,c_343])).

tff(c_385,plain,(
    ! [A_96] :
      ( v1_zfmisc_1(u1_struct_0(A_96))
      | v1_xboole_0(u1_struct_0(A_96))
      | ~ l1_struct_0(A_96)
      | ~ v7_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_350])).

tff(c_394,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_385])).

tff(c_399,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_263,c_394])).

tff(c_400,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_158,c_149,c_399])).

tff(c_403,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_400])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_403])).

tff(c_408,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_412,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_408,c_18])).

tff(c_415,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_412])).

tff(c_418,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_415])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_418])).

tff(c_424,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_533,plain,(
    ! [B_119,A_120] :
      ( ~ v1_tex_2(B_119,A_120)
      | v2_struct_0(B_119)
      | ~ m1_pre_topc(B_119,A_120)
      | ~ l1_pre_topc(A_120)
      | ~ v7_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_536,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_424,c_533])).

tff(c_539,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_526,c_536])).

tff(c_540,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_472,c_539])).

tff(c_473,plain,(
    ! [A_111,B_112] :
      ( v1_subset_1(k6_domain_1(A_111,B_112),A_111)
      | ~ m1_subset_1(B_112,A_111)
      | v1_zfmisc_1(A_111)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_423,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_479,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_473,c_423])).

tff(c_483,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_479])).

tff(c_484,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_483])).

tff(c_487,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_484,c_18])).

tff(c_490,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_487])).

tff(c_493,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_490])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_493])).

tff(c_499,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_498,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_433,plain,(
    ! [B_101,A_102] :
      ( v1_subset_1(B_101,A_102)
      | B_101 = A_102
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_436,plain,(
    ! [A_4] :
      ( v1_subset_1('#skF_1'(A_4),A_4)
      | '#skF_1'(A_4) = A_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_433])).

tff(c_439,plain,(
    ! [A_4] : '#skF_1'(A_4) = A_4 ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_436])).

tff(c_440,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_10])).

tff(c_548,plain,(
    ! [B_123,A_124] :
      ( v1_subset_1(B_123,u1_struct_0(A_124))
      | ~ v1_zfmisc_1(B_123)
      | v1_xboole_0(B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_struct_0(A_124)
      | v7_struct_0(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_555,plain,(
    ! [A_124] :
      ( v1_subset_1(u1_struct_0(A_124),u1_struct_0(A_124))
      | ~ v1_zfmisc_1(u1_struct_0(A_124))
      | v1_xboole_0(u1_struct_0(A_124))
      | ~ l1_struct_0(A_124)
      | v7_struct_0(A_124)
      | v2_struct_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_440,c_548])).

tff(c_570,plain,(
    ! [A_127] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_127))
      | v1_xboole_0(u1_struct_0(A_127))
      | ~ l1_struct_0(A_127)
      | v7_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_555])).

tff(c_573,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_498,c_570])).

tff(c_579,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_540,c_499,c_573])).

tff(c_583,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_579])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.41  
% 2.75/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.41  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.75/1.41  
% 2.75/1.41  %Foreground sorts:
% 2.75/1.41  
% 2.75/1.41  
% 2.75/1.41  %Background operators:
% 2.75/1.41  
% 2.75/1.41  
% 2.75/1.41  %Foreground operators:
% 2.75/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.75/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.75/1.41  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.75/1.41  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.75/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.75/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.41  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.75/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.41  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.41  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.75/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.75/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.75/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.41  
% 2.75/1.43  tff(f_217, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.75/1.43  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.75/1.43  tff(f_168, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.75/1.43  tff(f_154, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.75/1.43  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.75/1.43  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.75/1.43  tff(f_193, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.75/1.43  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.75/1.43  tff(f_140, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.75/1.43  tff(f_182, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tex_2)).
% 2.75/1.43  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.75/1.43  tff(f_34, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.75/1.43  tff(f_40, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.75/1.43  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((~v1_xboole_0(B) & ~v1_subset_1(B, u1_struct_0(A))) => (~v1_xboole_0(B) & v1_zfmisc_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc7_tex_2)).
% 2.75/1.43  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.75/1.43  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.75/1.43  tff(f_204, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 2.75/1.43  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc8_tex_2)).
% 2.75/1.43  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 2.75/1.43  tff(c_12, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.75/1.43  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 2.75/1.43  tff(c_58, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 2.75/1.43  tff(c_465, plain, (![A_109, B_110]: (~v2_struct_0(k1_tex_2(A_109, B_110)) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.43  tff(c_468, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_465])).
% 2.75/1.43  tff(c_471, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_468])).
% 2.75/1.43  tff(c_472, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_471])).
% 2.75/1.43  tff(c_520, plain, (![A_117, B_118]: (m1_pre_topc(k1_tex_2(A_117, B_118), A_117) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.43  tff(c_522, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_520])).
% 2.75/1.43  tff(c_525, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_522])).
% 2.75/1.43  tff(c_526, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_525])).
% 2.75/1.43  tff(c_171, plain, (![A_70, B_71]: (m1_pre_topc(k1_tex_2(A_70, B_71), A_70) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l1_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.43  tff(c_173, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_171])).
% 2.75/1.43  tff(c_176, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_173])).
% 2.75/1.43  tff(c_177, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_176])).
% 2.75/1.43  tff(c_14, plain, (![B_9, A_7]: (l1_pre_topc(B_9) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.75/1.43  tff(c_180, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_177, c_14])).
% 2.75/1.43  tff(c_183, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_180])).
% 2.75/1.43  tff(c_125, plain, (![A_60, B_61]: (~v2_struct_0(k1_tex_2(A_60, B_61)) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.43  tff(c_128, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_125])).
% 2.75/1.43  tff(c_131, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_128])).
% 2.75/1.43  tff(c_132, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_131])).
% 2.75/1.43  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.43  tff(c_64, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 2.75/1.43  tff(c_86, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 2.75/1.43  tff(c_70, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 2.75/1.43  tff(c_133, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_86, c_70])).
% 2.75/1.43  tff(c_142, plain, (![A_64, B_65]: (~v1_zfmisc_1(A_64) | ~v1_subset_1(k6_domain_1(A_64, B_65), A_64) | ~m1_subset_1(B_65, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.75/1.43  tff(c_145, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_133, c_142])).
% 2.75/1.43  tff(c_148, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_145])).
% 2.75/1.43  tff(c_149, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_148])).
% 2.75/1.43  tff(c_158, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2, c_149])).
% 2.75/1.43  tff(c_134, plain, (![A_62, B_63]: (v7_struct_0(k1_tex_2(A_62, B_63)) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.43  tff(c_137, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_134])).
% 2.75/1.43  tff(c_140, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_137])).
% 2.75/1.43  tff(c_141, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_140])).
% 2.75/1.43  tff(c_101, plain, (![B_56, A_57]: (m1_subset_1(u1_struct_0(B_56), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.43  tff(c_34, plain, (![B_25, A_24]: (v1_subset_1(B_25, A_24) | B_25=A_24 | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.75/1.43  tff(c_105, plain, (![B_56, A_57]: (v1_subset_1(u1_struct_0(B_56), u1_struct_0(A_57)) | u1_struct_0(B_56)=u1_struct_0(A_57) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_101, c_34])).
% 2.75/1.43  tff(c_20, plain, (![B_14, A_12]: (m1_subset_1(u1_struct_0(B_14), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.43  tff(c_222, plain, (![B_82, A_83]: (v1_tex_2(B_82, A_83) | ~v1_subset_1(u1_struct_0(B_82), u1_struct_0(A_83)) | ~m1_subset_1(u1_struct_0(B_82), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_pre_topc(B_82, A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.75/1.43  tff(c_238, plain, (![B_86, A_87]: (v1_tex_2(B_86, A_87) | ~v1_subset_1(u1_struct_0(B_86), u1_struct_0(A_87)) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_20, c_222])).
% 2.75/1.43  tff(c_247, plain, (![B_88, A_89]: (v1_tex_2(B_88, A_89) | u1_struct_0(B_88)=u1_struct_0(A_89) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_105, c_238])).
% 2.75/1.43  tff(c_257, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_247, c_86])).
% 2.75/1.43  tff(c_263, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_177, c_257])).
% 2.75/1.43  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.43  tff(c_6, plain, (![A_3]: (~v1_subset_1(k2_subset_1(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.75/1.43  tff(c_71, plain, (![A_3]: (~v1_subset_1(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.75/1.43  tff(c_8, plain, (![A_4]: (~v1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.43  tff(c_10, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.43  tff(c_94, plain, (![B_54, A_55]: (v1_subset_1(B_54, A_55) | B_54=A_55 | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.75/1.43  tff(c_97, plain, (![A_4]: (v1_subset_1('#skF_1'(A_4), A_4) | '#skF_1'(A_4)=A_4)), inference(resolution, [status(thm)], [c_10, c_94])).
% 2.75/1.43  tff(c_100, plain, (![A_4]: ('#skF_1'(A_4)=A_4)), inference(negUnitSimplification, [status(thm)], [c_8, c_97])).
% 2.75/1.43  tff(c_106, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_10])).
% 2.75/1.43  tff(c_343, plain, (![B_91, A_92]: (v1_zfmisc_1(B_91) | v1_subset_1(B_91, u1_struct_0(A_92)) | v1_xboole_0(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_struct_0(A_92) | ~v7_struct_0(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.75/1.43  tff(c_350, plain, (![A_92]: (v1_zfmisc_1(u1_struct_0(A_92)) | v1_subset_1(u1_struct_0(A_92), u1_struct_0(A_92)) | v1_xboole_0(u1_struct_0(A_92)) | ~l1_struct_0(A_92) | ~v7_struct_0(A_92) | v2_struct_0(A_92))), inference(resolution, [status(thm)], [c_106, c_343])).
% 2.75/1.43  tff(c_385, plain, (![A_96]: (v1_zfmisc_1(u1_struct_0(A_96)) | v1_xboole_0(u1_struct_0(A_96)) | ~l1_struct_0(A_96) | ~v7_struct_0(A_96) | v2_struct_0(A_96))), inference(negUnitSimplification, [status(thm)], [c_71, c_350])).
% 2.75/1.43  tff(c_394, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_385])).
% 2.75/1.43  tff(c_399, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_263, c_394])).
% 2.75/1.43  tff(c_400, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_132, c_158, c_149, c_399])).
% 2.75/1.43  tff(c_403, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_400])).
% 2.75/1.43  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_403])).
% 2.75/1.43  tff(c_408, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_148])).
% 2.75/1.43  tff(c_18, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.75/1.43  tff(c_412, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_408, c_18])).
% 2.75/1.43  tff(c_415, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_412])).
% 2.75/1.43  tff(c_418, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_415])).
% 2.75/1.43  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_418])).
% 2.75/1.43  tff(c_424, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 2.75/1.43  tff(c_533, plain, (![B_119, A_120]: (~v1_tex_2(B_119, A_120) | v2_struct_0(B_119) | ~m1_pre_topc(B_119, A_120) | ~l1_pre_topc(A_120) | ~v7_struct_0(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.75/1.43  tff(c_536, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_424, c_533])).
% 2.75/1.43  tff(c_539, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_526, c_536])).
% 2.75/1.43  tff(c_540, plain, (~v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_472, c_539])).
% 2.75/1.43  tff(c_473, plain, (![A_111, B_112]: (v1_subset_1(k6_domain_1(A_111, B_112), A_111) | ~m1_subset_1(B_112, A_111) | v1_zfmisc_1(A_111) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.75/1.43  tff(c_423, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_64])).
% 2.75/1.43  tff(c_479, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_473, c_423])).
% 2.75/1.43  tff(c_483, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_479])).
% 2.75/1.43  tff(c_484, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_483])).
% 2.75/1.43  tff(c_487, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_484, c_18])).
% 2.75/1.43  tff(c_490, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_487])).
% 2.75/1.43  tff(c_493, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_490])).
% 2.75/1.43  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_493])).
% 2.75/1.43  tff(c_499, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_483])).
% 2.75/1.43  tff(c_498, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_483])).
% 2.75/1.43  tff(c_433, plain, (![B_101, A_102]: (v1_subset_1(B_101, A_102) | B_101=A_102 | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.75/1.43  tff(c_436, plain, (![A_4]: (v1_subset_1('#skF_1'(A_4), A_4) | '#skF_1'(A_4)=A_4)), inference(resolution, [status(thm)], [c_10, c_433])).
% 2.75/1.43  tff(c_439, plain, (![A_4]: ('#skF_1'(A_4)=A_4)), inference(negUnitSimplification, [status(thm)], [c_8, c_436])).
% 2.75/1.43  tff(c_440, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_10])).
% 2.75/1.43  tff(c_548, plain, (![B_123, A_124]: (v1_subset_1(B_123, u1_struct_0(A_124)) | ~v1_zfmisc_1(B_123) | v1_xboole_0(B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_struct_0(A_124) | v7_struct_0(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.75/1.43  tff(c_555, plain, (![A_124]: (v1_subset_1(u1_struct_0(A_124), u1_struct_0(A_124)) | ~v1_zfmisc_1(u1_struct_0(A_124)) | v1_xboole_0(u1_struct_0(A_124)) | ~l1_struct_0(A_124) | v7_struct_0(A_124) | v2_struct_0(A_124))), inference(resolution, [status(thm)], [c_440, c_548])).
% 2.75/1.43  tff(c_570, plain, (![A_127]: (~v1_zfmisc_1(u1_struct_0(A_127)) | v1_xboole_0(u1_struct_0(A_127)) | ~l1_struct_0(A_127) | v7_struct_0(A_127) | v2_struct_0(A_127))), inference(negUnitSimplification, [status(thm)], [c_71, c_555])).
% 2.75/1.43  tff(c_573, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_498, c_570])).
% 2.75/1.43  tff(c_579, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_540, c_499, c_573])).
% 2.75/1.43  tff(c_583, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_579])).
% 2.75/1.43  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_583])).
% 2.75/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  
% 2.75/1.43  Inference rules
% 2.75/1.43  ----------------------
% 2.75/1.43  #Ref     : 0
% 2.75/1.43  #Sup     : 87
% 2.75/1.43  #Fact    : 0
% 2.75/1.43  #Define  : 0
% 2.75/1.43  #Split   : 4
% 2.75/1.43  #Chain   : 0
% 2.75/1.43  #Close   : 0
% 2.75/1.43  
% 2.75/1.43  Ordering : KBO
% 2.75/1.43  
% 2.75/1.43  Simplification rules
% 2.75/1.43  ----------------------
% 2.75/1.44  #Subsume      : 18
% 2.75/1.44  #Demod        : 45
% 2.75/1.44  #Tautology    : 27
% 2.75/1.44  #SimpNegUnit  : 34
% 2.75/1.44  #BackRed      : 4
% 2.75/1.44  
% 2.75/1.44  #Partial instantiations: 0
% 2.75/1.44  #Strategies tried      : 1
% 2.75/1.44  
% 2.75/1.44  Timing (in seconds)
% 2.75/1.44  ----------------------
% 2.75/1.44  Preprocessing        : 0.33
% 2.75/1.44  Parsing              : 0.18
% 2.75/1.44  CNF conversion       : 0.02
% 2.75/1.44  Main loop            : 0.30
% 2.75/1.44  Inferencing          : 0.11
% 2.75/1.44  Reduction            : 0.09
% 2.75/1.44  Demodulation         : 0.06
% 2.75/1.44  BG Simplification    : 0.02
% 2.75/1.44  Subsumption          : 0.06
% 2.75/1.44  Abstraction          : 0.01
% 2.75/1.44  MUC search           : 0.00
% 2.75/1.44  Cooper               : 0.00
% 2.75/1.44  Total                : 0.68
% 2.75/1.44  Index Insertion      : 0.00
% 2.75/1.44  Index Deletion       : 0.00
% 2.75/1.44  Index Matching       : 0.00
% 2.75/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

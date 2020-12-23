%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:53 EST 2020

% Result     : Theorem 8.17s
% Output     : CNFRefutation 8.31s
% Verified   : 
% Statistics : Number of formulae       :  172 (1463 expanded)
%              Number of leaves         :   44 ( 541 expanded)
%              Depth                    :   29
%              Number of atoms          :  489 (5617 expanded)
%              Number of equality atoms :   35 ( 320 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(f_221,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_34,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_160,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_201,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_189,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_402,plain,(
    ! [A_97,B_98] :
      ( m1_pre_topc('#skF_2'(A_97,B_98),A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | v1_xboole_0(B_98)
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_416,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_402])).

tff(c_425,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_416])).

tff(c_426,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_425])).

tff(c_207,plain,(
    ! [A_83,B_84] :
      ( ~ v2_struct_0('#skF_2'(A_83,B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | v1_xboole_0(B_84)
      | ~ l1_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_222,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_207])).

tff(c_228,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_222])).

tff(c_229,plain,(
    ~ v2_struct_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_228])).

tff(c_464,plain,(
    ! [A_104,B_105] :
      ( u1_struct_0('#skF_2'(A_104,B_105)) = B_105
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | v1_xboole_0(B_105)
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_483,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_464])).

tff(c_492,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_483])).

tff(c_493,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_492])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(A_58,B_59)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_879,plain,(
    ! [C_131,A_132,B_133] :
      ( m1_subset_1(C_131,u1_struct_0(A_132))
      | ~ m1_subset_1(C_131,u1_struct_0(B_133))
      | ~ m1_pre_topc(B_133,A_132)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2578,plain,(
    ! [B_167,A_168] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_167)),u1_struct_0(A_168))
      | ~ m1_pre_topc(B_167,A_168)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_168)
      | v2_struct_0(A_168)
      | v1_xboole_0(u1_struct_0(B_167)) ) ),
    inference(resolution,[status(thm)],[c_97,c_879])).

tff(c_2664,plain,(
    ! [A_168] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_168))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_168)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_168)
      | v2_struct_0(A_168)
      | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_2578])).

tff(c_2700,plain,(
    ! [A_168] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_168))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_168)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_168)
      | v2_struct_0(A_168)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_2664])).

tff(c_2701,plain,(
    ! [A_168] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_168))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_168)
      | ~ l1_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_229,c_2700])).

tff(c_74,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_77,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_80,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68])).

tff(c_18,plain,(
    ! [B_16,A_14] :
      ( l1_pre_topc(B_16)
      | ~ m1_pre_topc(B_16,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_429,plain,
    ( l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_426,c_18])).

tff(c_432,plain,(
    l1_pre_topc('#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_429])).

tff(c_6,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [A_73,B_74] :
      ( k6_domain_1(A_73,B_74) = k1_tarski(B_74)
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_154,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_97,c_143])).

tff(c_167,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k6_domain_1(A_77,B_78),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_182,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k6_domain_1(A_77,B_78),A_77)
      | ~ m1_subset_1(B_78,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_167,c_12])).

tff(c_191,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(A_82,B_81)
      | ~ v1_zfmisc_1(B_81)
      | v1_xboole_0(B_81)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_454,plain,(
    ! [A_101,B_102] :
      ( k6_domain_1(A_101,B_102) = A_101
      | ~ v1_zfmisc_1(A_101)
      | v1_xboole_0(k6_domain_1(A_101,B_102))
      | ~ m1_subset_1(B_102,A_101)
      | v1_xboole_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_182,c_191])).

tff(c_460,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(k1_tarski('#skF_1'(A_1)))
      | ~ m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_454])).

tff(c_687,plain,(
    ! [A_120] :
      ( k6_domain_1(A_120,'#skF_1'(A_120)) = A_120
      | ~ v1_zfmisc_1(A_120)
      | ~ m1_subset_1('#skF_1'(A_120),A_120)
      | v1_xboole_0(A_120)
      | v1_xboole_0(A_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_460])).

tff(c_697,plain,(
    ! [A_121] :
      ( k6_domain_1(A_121,'#skF_1'(A_121)) = A_121
      | ~ v1_zfmisc_1(A_121)
      | v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_97,c_687])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k6_domain_1(A_25,B_26),k1_zfmisc_1(A_25))
      | ~ m1_subset_1(B_26,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_795,plain,(
    ! [A_126] :
      ( m1_subset_1(A_126,k1_zfmisc_1(A_126))
      | ~ m1_subset_1('#skF_1'(A_126),A_126)
      | v1_xboole_0(A_126)
      | ~ v1_zfmisc_1(A_126)
      | v1_xboole_0(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_24])).

tff(c_806,plain,(
    ! [A_128] :
      ( m1_subset_1(A_128,k1_zfmisc_1(A_128))
      | ~ v1_zfmisc_1(A_128)
      | v1_xboole_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_97,c_795])).

tff(c_36,plain,(
    ! [A_33,B_37] :
      ( m1_pre_topc('#skF_2'(A_33,B_37),A_33)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_33)))
      | v1_xboole_0(B_37)
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_924,plain,(
    ! [A_137] :
      ( m1_pre_topc('#skF_2'(A_137,u1_struct_0(A_137)),A_137)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137)
      | ~ v1_zfmisc_1(u1_struct_0(A_137))
      | v1_xboole_0(u1_struct_0(A_137)) ) ),
    inference(resolution,[status(thm)],[c_806,c_36])).

tff(c_939,plain,
    ( m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_924])).

tff(c_943,plain,
    ( m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_77,c_493,c_432,c_939])).

tff(c_944,plain,(
    m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_229,c_943])).

tff(c_733,plain,(
    ! [A_122] :
      ( r1_tarski(A_122,A_122)
      | ~ m1_subset_1('#skF_1'(A_122),A_122)
      | v1_xboole_0(A_122)
      | ~ v1_zfmisc_1(A_122)
      | v1_xboole_0(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_182])).

tff(c_743,plain,(
    ! [A_123] :
      ( r1_tarski(A_123,A_123)
      | ~ v1_zfmisc_1(A_123)
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_97,c_733])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_224,plain,(
    ! [A_83,A_11] :
      ( ~ v2_struct_0('#skF_2'(A_83,A_11))
      | v1_xboole_0(A_11)
      | ~ l1_pre_topc(A_83)
      | v2_struct_0(A_83)
      | ~ r1_tarski(A_11,u1_struct_0(A_83)) ) ),
    inference(resolution,[status(thm)],[c_14,c_207])).

tff(c_891,plain,(
    ! [A_134] :
      ( ~ v2_struct_0('#skF_2'(A_134,u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | v2_struct_0(A_134)
      | ~ v1_zfmisc_1(u1_struct_0(A_134))
      | v1_xboole_0(u1_struct_0(A_134)) ) ),
    inference(resolution,[status(thm)],[c_743,c_224])).

tff(c_900,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_891])).

tff(c_902,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_77,c_493,c_432,c_900])).

tff(c_903,plain,(
    ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_229,c_902])).

tff(c_34,plain,(
    ! [A_33,B_37] :
      ( u1_struct_0('#skF_2'(A_33,B_37)) = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_33)))
      | v1_xboole_0(B_37)
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1019,plain,(
    ! [A_142] :
      ( u1_struct_0('#skF_2'(A_142,u1_struct_0(A_142))) = u1_struct_0(A_142)
      | ~ l1_pre_topc(A_142)
      | v2_struct_0(A_142)
      | ~ v1_zfmisc_1(u1_struct_0(A_142))
      | v1_xboole_0(u1_struct_0(A_142)) ) ),
    inference(resolution,[status(thm)],[c_806,c_34])).

tff(c_1104,plain,
    ( u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) = u1_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_1019])).

tff(c_1120,plain,
    ( u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_77,c_493,c_432,c_493,c_1104])).

tff(c_1121,plain,(
    u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_229,c_1120])).

tff(c_2640,plain,(
    ! [A_168] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_168))
      | ~ m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),A_168)
      | v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
      | ~ l1_pre_topc(A_168)
      | v2_struct_0(A_168)
      | v1_xboole_0(u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1121,c_2578])).

tff(c_2695,plain,(
    ! [A_168] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_168))
      | ~ m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),A_168)
      | v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
      | ~ l1_pre_topc(A_168)
      | v2_struct_0(A_168)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_2640])).

tff(c_2777,plain,(
    ! [A_170] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_170))
      | ~ m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),A_170)
      | ~ l1_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_903,c_2695])).

tff(c_2824,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | ~ m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_2777])).

tff(c_2846,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_944,c_2824])).

tff(c_2847,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_2846])).

tff(c_26,plain,(
    ! [A_27,B_28] :
      ( k6_domain_1(A_27,B_28) = k1_tarski(B_28)
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2850,plain,
    ( k6_domain_1('#skF_5','#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2847,c_26])).

tff(c_2853,plain,(
    k6_domain_1('#skF_5','#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2850])).

tff(c_696,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_97,c_687])).

tff(c_2860,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2853,c_696])).

tff(c_2885,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2860])).

tff(c_2886,plain,(
    k1_tarski('#skF_1'('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2885])).

tff(c_116,plain,(
    ! [B_68,A_69] :
      ( v1_xboole_0(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_116])).

tff(c_131,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_126])).

tff(c_885,plain,(
    ! [C_131,A_132] :
      ( m1_subset_1(C_131,u1_struct_0(A_132))
      | ~ m1_subset_1(C_131,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_132)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_879])).

tff(c_904,plain,(
    ! [C_135,A_136] :
      ( m1_subset_1(C_135,u1_struct_0(A_136))
      | ~ m1_subset_1(C_135,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_136)
      | ~ l1_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_885])).

tff(c_6541,plain,(
    ! [A_249,C_250] :
      ( k6_domain_1(u1_struct_0(A_249),C_250) = k1_tarski(C_250)
      | v1_xboole_0(u1_struct_0(A_249))
      | ~ m1_subset_1(C_250,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_249)
      | ~ l1_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_904,c_26])).

tff(c_6543,plain,(
    ! [C_250] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_250) = k1_tarski(C_250)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_250,'#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_426,c_6541])).

tff(c_6546,plain,(
    ! [C_250] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_250) = k1_tarski(C_250)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_250,'#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6543])).

tff(c_6548,plain,(
    ! [C_251] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_251) = k1_tarski(C_251)
      | ~ m1_subset_1(C_251,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_131,c_6546])).

tff(c_54,plain,(
    ! [A_48,B_50] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_48),B_50),A_48)
      | ~ m1_subset_1(B_50,u1_struct_0(A_48))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_6580,plain,(
    ! [C_251] :
      ( v2_tex_2(k1_tarski(C_251),'#skF_4')
      | ~ m1_subset_1(C_251,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_251,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6548,c_54])).

tff(c_6632,plain,(
    ! [C_251] :
      ( v2_tex_2(k1_tarski(C_251),'#skF_4')
      | ~ m1_subset_1(C_251,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_251,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_6580])).

tff(c_6751,plain,(
    ! [C_254] :
      ( v2_tex_2(k1_tarski(C_254),'#skF_4')
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_254,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6632])).

tff(c_6754,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2886,c_6751])).

tff(c_6759,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_6754])).

tff(c_6760,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6759])).

tff(c_6766,plain,
    ( ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2701,c_6760])).

tff(c_6776,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_426,c_6766])).

tff(c_6778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6776])).

tff(c_6779,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_8293,plain,(
    ! [A_369,B_370] :
      ( m1_pre_topc('#skF_3'(A_369,B_370),A_369)
      | ~ v2_tex_2(B_370,A_369)
      | ~ m1_subset_1(B_370,k1_zfmisc_1(u1_struct_0(A_369)))
      | v1_xboole_0(B_370)
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_8322,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_8293])).

tff(c_8339,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_6779,c_8322])).

tff(c_8340,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_8339])).

tff(c_8346,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8340,c_18])).

tff(c_8353,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8346])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6780,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_7659,plain,(
    ! [A_340,B_341] :
      ( ~ v2_struct_0('#skF_3'(A_340,B_341))
      | ~ v2_tex_2(B_341,A_340)
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0(A_340)))
      | v1_xboole_0(B_341)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_7691,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_7659])).

tff(c_7704,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_6779,c_7691])).

tff(c_7705,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_7704])).

tff(c_62,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_7872,plain,(
    ! [A_348,B_349] :
      ( v1_tdlat_3('#skF_3'(A_348,B_349))
      | ~ v2_tex_2(B_349,A_348)
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0(A_348)))
      | v1_xboole_0(B_349)
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348)
      | v2_struct_0(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_7907,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_7872])).

tff(c_7920,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_6779,c_7907])).

tff(c_7921,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_7920])).

tff(c_30,plain,(
    ! [B_32,A_30] :
      ( ~ v1_tdlat_3(B_32)
      | v7_struct_0(B_32)
      | v2_struct_0(B_32)
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_tdlat_3(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8343,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8340,c_30])).

tff(c_8349,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_7921,c_8343])).

tff(c_8350,plain,(
    v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7705,c_8349])).

tff(c_8401,plain,(
    ! [A_377,B_378] :
      ( u1_struct_0('#skF_3'(A_377,B_378)) = B_378
      | ~ v2_tex_2(B_378,A_377)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | v1_xboole_0(B_378)
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_8442,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_8401])).

tff(c_8459,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_6779,c_8442])).

tff(c_8460,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_8459])).

tff(c_20,plain,(
    ! [A_17] :
      ( v1_zfmisc_1(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | ~ v7_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8523,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8460,c_20])).

tff(c_8588,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8350,c_8523])).

tff(c_8589,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_6780,c_8588])).

tff(c_8593,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_8589])).

tff(c_8597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8353,c_8593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.17/2.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/3.01  
% 8.31/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/3.01  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 8.31/3.01  
% 8.31/3.01  %Foreground sorts:
% 8.31/3.01  
% 8.31/3.01  
% 8.31/3.01  %Background operators:
% 8.31/3.01  
% 8.31/3.01  
% 8.31/3.01  %Foreground operators:
% 8.31/3.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.31/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.31/3.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.31/3.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.31/3.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.31/3.01  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 8.31/3.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.31/3.01  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 8.31/3.01  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.31/3.01  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.31/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.31/3.01  tff('#skF_5', type, '#skF_5': $i).
% 8.31/3.01  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.31/3.01  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.31/3.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.31/3.01  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.31/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.31/3.01  tff('#skF_4', type, '#skF_4': $i).
% 8.31/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.31/3.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.31/3.01  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 8.31/3.01  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.31/3.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.31/3.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.31/3.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.31/3.01  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 8.31/3.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.31/3.01  
% 8.31/3.03  tff(f_221, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 8.31/3.03  tff(f_147, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 8.31/3.03  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.31/3.03  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 8.31/3.03  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 8.31/3.03  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.31/3.03  tff(f_34, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 8.31/3.03  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 8.31/3.03  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 8.31/3.03  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.31/3.03  tff(f_160, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 8.31/3.03  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.31/3.03  tff(f_201, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 8.31/3.03  tff(f_189, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 8.31/3.03  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.31/3.03  tff(f_126, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 8.31/3.03  tff(f_66, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 8.31/3.03  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.31/3.03  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.31/3.03  tff(c_58, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.31/3.03  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.31/3.03  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.31/3.03  tff(c_402, plain, (![A_97, B_98]: (m1_pre_topc('#skF_2'(A_97, B_98), A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | v1_xboole_0(B_98) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.31/3.03  tff(c_416, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_402])).
% 8.31/3.03  tff(c_425, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_416])).
% 8.31/3.03  tff(c_426, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_425])).
% 8.31/3.03  tff(c_207, plain, (![A_83, B_84]: (~v2_struct_0('#skF_2'(A_83, B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | v1_xboole_0(B_84) | ~l1_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.31/3.03  tff(c_222, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_207])).
% 8.31/3.03  tff(c_228, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_222])).
% 8.31/3.03  tff(c_229, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_228])).
% 8.31/3.03  tff(c_464, plain, (![A_104, B_105]: (u1_struct_0('#skF_2'(A_104, B_105))=B_105 | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | v1_xboole_0(B_105) | ~l1_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.31/3.03  tff(c_483, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_464])).
% 8.31/3.03  tff(c_492, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_483])).
% 8.31/3.03  tff(c_493, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_492])).
% 8.31/3.03  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.31/3.03  tff(c_93, plain, (![A_58, B_59]: (m1_subset_1(A_58, B_59) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.31/3.03  tff(c_97, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_93])).
% 8.31/3.03  tff(c_879, plain, (![C_131, A_132, B_133]: (m1_subset_1(C_131, u1_struct_0(A_132)) | ~m1_subset_1(C_131, u1_struct_0(B_133)) | ~m1_pre_topc(B_133, A_132) | v2_struct_0(B_133) | ~l1_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.31/3.03  tff(c_2578, plain, (![B_167, A_168]: (m1_subset_1('#skF_1'(u1_struct_0(B_167)), u1_struct_0(A_168)) | ~m1_pre_topc(B_167, A_168) | v2_struct_0(B_167) | ~l1_pre_topc(A_168) | v2_struct_0(A_168) | v1_xboole_0(u1_struct_0(B_167)))), inference(resolution, [status(thm)], [c_97, c_879])).
% 8.31/3.03  tff(c_2664, plain, (![A_168]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_168)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_168) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_168) | v2_struct_0(A_168) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_493, c_2578])).
% 8.31/3.03  tff(c_2700, plain, (![A_168]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_168)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_168) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_168) | v2_struct_0(A_168) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_2664])).
% 8.31/3.03  tff(c_2701, plain, (![A_168]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_168)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_168) | ~l1_pre_topc(A_168) | v2_struct_0(A_168))), inference(negUnitSimplification, [status(thm)], [c_58, c_229, c_2700])).
% 8.31/3.03  tff(c_74, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.31/3.03  tff(c_77, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 8.31/3.03  tff(c_68, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.31/3.03  tff(c_80, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_68])).
% 8.31/3.03  tff(c_18, plain, (![B_16, A_14]: (l1_pre_topc(B_16) | ~m1_pre_topc(B_16, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.31/3.03  tff(c_429, plain, (l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_426, c_18])).
% 8.31/3.03  tff(c_432, plain, (l1_pre_topc('#skF_2'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_429])).
% 8.31/3.03  tff(c_6, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.31/3.03  tff(c_143, plain, (![A_73, B_74]: (k6_domain_1(A_73, B_74)=k1_tarski(B_74) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.31/3.03  tff(c_154, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_97, c_143])).
% 8.31/3.03  tff(c_167, plain, (![A_77, B_78]: (m1_subset_1(k6_domain_1(A_77, B_78), k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, A_77) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.31/3.03  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.31/3.03  tff(c_182, plain, (![A_77, B_78]: (r1_tarski(k6_domain_1(A_77, B_78), A_77) | ~m1_subset_1(B_78, A_77) | v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_167, c_12])).
% 8.31/3.03  tff(c_191, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(A_82, B_81) | ~v1_zfmisc_1(B_81) | v1_xboole_0(B_81) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.31/3.03  tff(c_454, plain, (![A_101, B_102]: (k6_domain_1(A_101, B_102)=A_101 | ~v1_zfmisc_1(A_101) | v1_xboole_0(k6_domain_1(A_101, B_102)) | ~m1_subset_1(B_102, A_101) | v1_xboole_0(A_101))), inference(resolution, [status(thm)], [c_182, c_191])).
% 8.31/3.03  tff(c_460, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(k1_tarski('#skF_1'(A_1))) | ~m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1) | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_154, c_454])).
% 8.31/3.03  tff(c_687, plain, (![A_120]: (k6_domain_1(A_120, '#skF_1'(A_120))=A_120 | ~v1_zfmisc_1(A_120) | ~m1_subset_1('#skF_1'(A_120), A_120) | v1_xboole_0(A_120) | v1_xboole_0(A_120))), inference(negUnitSimplification, [status(thm)], [c_6, c_460])).
% 8.31/3.03  tff(c_697, plain, (![A_121]: (k6_domain_1(A_121, '#skF_1'(A_121))=A_121 | ~v1_zfmisc_1(A_121) | v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_97, c_687])).
% 8.31/3.03  tff(c_24, plain, (![A_25, B_26]: (m1_subset_1(k6_domain_1(A_25, B_26), k1_zfmisc_1(A_25)) | ~m1_subset_1(B_26, A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.31/3.03  tff(c_795, plain, (![A_126]: (m1_subset_1(A_126, k1_zfmisc_1(A_126)) | ~m1_subset_1('#skF_1'(A_126), A_126) | v1_xboole_0(A_126) | ~v1_zfmisc_1(A_126) | v1_xboole_0(A_126))), inference(superposition, [status(thm), theory('equality')], [c_697, c_24])).
% 8.31/3.03  tff(c_806, plain, (![A_128]: (m1_subset_1(A_128, k1_zfmisc_1(A_128)) | ~v1_zfmisc_1(A_128) | v1_xboole_0(A_128))), inference(resolution, [status(thm)], [c_97, c_795])).
% 8.31/3.03  tff(c_36, plain, (![A_33, B_37]: (m1_pre_topc('#skF_2'(A_33, B_37), A_33) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_33))) | v1_xboole_0(B_37) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.31/3.03  tff(c_924, plain, (![A_137]: (m1_pre_topc('#skF_2'(A_137, u1_struct_0(A_137)), A_137) | ~l1_pre_topc(A_137) | v2_struct_0(A_137) | ~v1_zfmisc_1(u1_struct_0(A_137)) | v1_xboole_0(u1_struct_0(A_137)))), inference(resolution, [status(thm)], [c_806, c_36])).
% 8.31/3.03  tff(c_939, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_493, c_924])).
% 8.31/3.03  tff(c_943, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_77, c_493, c_432, c_939])).
% 8.31/3.03  tff(c_944, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_229, c_943])).
% 8.31/3.03  tff(c_733, plain, (![A_122]: (r1_tarski(A_122, A_122) | ~m1_subset_1('#skF_1'(A_122), A_122) | v1_xboole_0(A_122) | ~v1_zfmisc_1(A_122) | v1_xboole_0(A_122))), inference(superposition, [status(thm), theory('equality')], [c_697, c_182])).
% 8.31/3.03  tff(c_743, plain, (![A_123]: (r1_tarski(A_123, A_123) | ~v1_zfmisc_1(A_123) | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_97, c_733])).
% 8.31/3.03  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.31/3.03  tff(c_224, plain, (![A_83, A_11]: (~v2_struct_0('#skF_2'(A_83, A_11)) | v1_xboole_0(A_11) | ~l1_pre_topc(A_83) | v2_struct_0(A_83) | ~r1_tarski(A_11, u1_struct_0(A_83)))), inference(resolution, [status(thm)], [c_14, c_207])).
% 8.31/3.03  tff(c_891, plain, (![A_134]: (~v2_struct_0('#skF_2'(A_134, u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | v2_struct_0(A_134) | ~v1_zfmisc_1(u1_struct_0(A_134)) | v1_xboole_0(u1_struct_0(A_134)))), inference(resolution, [status(thm)], [c_743, c_224])).
% 8.31/3.03  tff(c_900, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_493, c_891])).
% 8.31/3.03  tff(c_902, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_77, c_493, c_432, c_900])).
% 8.31/3.03  tff(c_903, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_229, c_902])).
% 8.31/3.03  tff(c_34, plain, (![A_33, B_37]: (u1_struct_0('#skF_2'(A_33, B_37))=B_37 | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_33))) | v1_xboole_0(B_37) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.31/3.03  tff(c_1019, plain, (![A_142]: (u1_struct_0('#skF_2'(A_142, u1_struct_0(A_142)))=u1_struct_0(A_142) | ~l1_pre_topc(A_142) | v2_struct_0(A_142) | ~v1_zfmisc_1(u1_struct_0(A_142)) | v1_xboole_0(u1_struct_0(A_142)))), inference(resolution, [status(thm)], [c_806, c_34])).
% 8.31/3.03  tff(c_1104, plain, (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))=u1_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_493, c_1019])).
% 8.31/3.03  tff(c_1120, plain, (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))='#skF_5' | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_77, c_493, c_432, c_493, c_1104])).
% 8.31/3.03  tff(c_1121, plain, (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_58, c_229, c_1120])).
% 8.31/3.03  tff(c_2640, plain, (![A_168]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_168)) | ~m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), A_168) | v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | ~l1_pre_topc(A_168) | v2_struct_0(A_168) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_1121, c_2578])).
% 8.31/3.03  tff(c_2695, plain, (![A_168]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_168)) | ~m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), A_168) | v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | ~l1_pre_topc(A_168) | v2_struct_0(A_168) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_2640])).
% 8.31/3.03  tff(c_2777, plain, (![A_170]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_170)) | ~m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), A_170) | ~l1_pre_topc(A_170) | v2_struct_0(A_170))), inference(negUnitSimplification, [status(thm)], [c_58, c_903, c_2695])).
% 8.31/3.03  tff(c_2824, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_2777])).
% 8.31/3.03  tff(c_2846, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | v2_struct_0('#skF_2'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_944, c_2824])).
% 8.31/3.03  tff(c_2847, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_229, c_2846])).
% 8.31/3.03  tff(c_26, plain, (![A_27, B_28]: (k6_domain_1(A_27, B_28)=k1_tarski(B_28) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.31/3.03  tff(c_2850, plain, (k6_domain_1('#skF_5', '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_2847, c_26])).
% 8.31/3.03  tff(c_2853, plain, (k6_domain_1('#skF_5', '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_2850])).
% 8.31/3.03  tff(c_696, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_97, c_687])).
% 8.31/3.03  tff(c_2860, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2853, c_696])).
% 8.31/3.03  tff(c_2885, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2860])).
% 8.31/3.03  tff(c_2886, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_58, c_2885])).
% 8.31/3.03  tff(c_116, plain, (![B_68, A_69]: (v1_xboole_0(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.31/3.03  tff(c_126, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_116])).
% 8.31/3.03  tff(c_131, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_126])).
% 8.31/3.03  tff(c_885, plain, (![C_131, A_132]: (m1_subset_1(C_131, u1_struct_0(A_132)) | ~m1_subset_1(C_131, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_132) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_132) | v2_struct_0(A_132))), inference(superposition, [status(thm), theory('equality')], [c_493, c_879])).
% 8.31/3.03  tff(c_904, plain, (![C_135, A_136]: (m1_subset_1(C_135, u1_struct_0(A_136)) | ~m1_subset_1(C_135, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_136) | ~l1_pre_topc(A_136) | v2_struct_0(A_136))), inference(negUnitSimplification, [status(thm)], [c_229, c_885])).
% 8.31/3.03  tff(c_6541, plain, (![A_249, C_250]: (k6_domain_1(u1_struct_0(A_249), C_250)=k1_tarski(C_250) | v1_xboole_0(u1_struct_0(A_249)) | ~m1_subset_1(C_250, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_249) | ~l1_pre_topc(A_249) | v2_struct_0(A_249))), inference(resolution, [status(thm)], [c_904, c_26])).
% 8.31/3.03  tff(c_6543, plain, (![C_250]: (k6_domain_1(u1_struct_0('#skF_4'), C_250)=k1_tarski(C_250) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_250, '#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_426, c_6541])).
% 8.31/3.03  tff(c_6546, plain, (![C_250]: (k6_domain_1(u1_struct_0('#skF_4'), C_250)=k1_tarski(C_250) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_250, '#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6543])).
% 8.31/3.03  tff(c_6548, plain, (![C_251]: (k6_domain_1(u1_struct_0('#skF_4'), C_251)=k1_tarski(C_251) | ~m1_subset_1(C_251, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_131, c_6546])).
% 8.31/3.03  tff(c_54, plain, (![A_48, B_50]: (v2_tex_2(k6_domain_1(u1_struct_0(A_48), B_50), A_48) | ~m1_subset_1(B_50, u1_struct_0(A_48)) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.31/3.03  tff(c_6580, plain, (![C_251]: (v2_tex_2(k1_tarski(C_251), '#skF_4') | ~m1_subset_1(C_251, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(C_251, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6548, c_54])).
% 8.31/3.03  tff(c_6632, plain, (![C_251]: (v2_tex_2(k1_tarski(C_251), '#skF_4') | ~m1_subset_1(C_251, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_subset_1(C_251, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_6580])).
% 8.31/3.03  tff(c_6751, plain, (![C_254]: (v2_tex_2(k1_tarski(C_254), '#skF_4') | ~m1_subset_1(C_254, u1_struct_0('#skF_4')) | ~m1_subset_1(C_254, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_6632])).
% 8.31/3.03  tff(c_6754, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2886, c_6751])).
% 8.31/3.03  tff(c_6759, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_6754])).
% 8.31/3.03  tff(c_6760, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_6759])).
% 8.31/3.03  tff(c_6766, plain, (~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2701, c_6760])).
% 8.31/3.03  tff(c_6776, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_426, c_6766])).
% 8.31/3.03  tff(c_6778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_6776])).
% 8.31/3.03  tff(c_6779, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 8.31/3.03  tff(c_8293, plain, (![A_369, B_370]: (m1_pre_topc('#skF_3'(A_369, B_370), A_369) | ~v2_tex_2(B_370, A_369) | ~m1_subset_1(B_370, k1_zfmisc_1(u1_struct_0(A_369))) | v1_xboole_0(B_370) | ~l1_pre_topc(A_369) | ~v2_pre_topc(A_369) | v2_struct_0(A_369))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.31/3.03  tff(c_8322, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_8293])).
% 8.31/3.03  tff(c_8339, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_6779, c_8322])).
% 8.31/3.03  tff(c_8340, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_8339])).
% 8.31/3.03  tff(c_8346, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8340, c_18])).
% 8.31/3.03  tff(c_8353, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_8346])).
% 8.31/3.03  tff(c_16, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.31/3.03  tff(c_6780, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 8.31/3.03  tff(c_7659, plain, (![A_340, B_341]: (~v2_struct_0('#skF_3'(A_340, B_341)) | ~v2_tex_2(B_341, A_340) | ~m1_subset_1(B_341, k1_zfmisc_1(u1_struct_0(A_340))) | v1_xboole_0(B_341) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.31/3.03  tff(c_7691, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_7659])).
% 8.31/3.03  tff(c_7704, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_6779, c_7691])).
% 8.31/3.03  tff(c_7705, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_7704])).
% 8.31/3.03  tff(c_62, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.31/3.03  tff(c_7872, plain, (![A_348, B_349]: (v1_tdlat_3('#skF_3'(A_348, B_349)) | ~v2_tex_2(B_349, A_348) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0(A_348))) | v1_xboole_0(B_349) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348) | v2_struct_0(A_348))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.31/3.03  tff(c_7907, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_7872])).
% 8.31/3.03  tff(c_7920, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_6779, c_7907])).
% 8.31/3.03  tff(c_7921, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_7920])).
% 8.31/3.03  tff(c_30, plain, (![B_32, A_30]: (~v1_tdlat_3(B_32) | v7_struct_0(B_32) | v2_struct_0(B_32) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30) | ~v2_tdlat_3(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.31/3.03  tff(c_8343, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_8340, c_30])).
% 8.31/3.03  tff(c_8349, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_7921, c_8343])).
% 8.31/3.03  tff(c_8350, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_7705, c_8349])).
% 8.31/3.03  tff(c_8401, plain, (![A_377, B_378]: (u1_struct_0('#skF_3'(A_377, B_378))=B_378 | ~v2_tex_2(B_378, A_377) | ~m1_subset_1(B_378, k1_zfmisc_1(u1_struct_0(A_377))) | v1_xboole_0(B_378) | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.31/3.03  tff(c_8442, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_8401])).
% 8.31/3.03  tff(c_8459, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_6779, c_8442])).
% 8.31/3.03  tff(c_8460, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_8459])).
% 8.31/3.03  tff(c_20, plain, (![A_17]: (v1_zfmisc_1(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | ~v7_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.31/3.03  tff(c_8523, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8460, c_20])).
% 8.31/3.03  tff(c_8588, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8350, c_8523])).
% 8.31/3.03  tff(c_8589, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_6780, c_8588])).
% 8.31/3.03  tff(c_8593, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_8589])).
% 8.31/3.03  tff(c_8597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8353, c_8593])).
% 8.31/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/3.03  
% 8.31/3.03  Inference rules
% 8.31/3.03  ----------------------
% 8.31/3.03  #Ref     : 0
% 8.31/3.03  #Sup     : 1902
% 8.31/3.03  #Fact    : 0
% 8.31/3.03  #Define  : 0
% 8.31/3.03  #Split   : 15
% 8.31/3.03  #Chain   : 0
% 8.31/3.03  #Close   : 0
% 8.31/3.03  
% 8.31/3.03  Ordering : KBO
% 8.31/3.03  
% 8.31/3.03  Simplification rules
% 8.31/3.03  ----------------------
% 8.31/3.03  #Subsume      : 164
% 8.31/3.03  #Demod        : 1694
% 8.31/3.03  #Tautology    : 386
% 8.31/3.03  #SimpNegUnit  : 706
% 8.31/3.03  #BackRed      : 1
% 8.31/3.03  
% 8.31/3.03  #Partial instantiations: 0
% 8.31/3.03  #Strategies tried      : 1
% 8.31/3.03  
% 8.31/3.03  Timing (in seconds)
% 8.31/3.03  ----------------------
% 8.31/3.04  Preprocessing        : 0.34
% 8.31/3.04  Parsing              : 0.18
% 8.31/3.04  CNF conversion       : 0.02
% 8.31/3.04  Main loop            : 1.90
% 8.31/3.04  Inferencing          : 0.53
% 8.31/3.04  Reduction            : 0.67
% 8.31/3.04  Demodulation         : 0.45
% 8.31/3.04  BG Simplification    : 0.07
% 8.31/3.04  Subsumption          : 0.50
% 8.31/3.04  Abstraction          : 0.09
% 8.31/3.04  MUC search           : 0.00
% 8.31/3.04  Cooper               : 0.00
% 8.31/3.04  Total                : 2.30
% 8.31/3.04  Index Insertion      : 0.00
% 8.31/3.04  Index Deletion       : 0.00
% 8.31/3.04  Index Matching       : 0.00
% 8.31/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------

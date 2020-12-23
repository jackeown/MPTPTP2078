%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:01 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 272 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  273 ( 711 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_165,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_154,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_95,axiom,(
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

tff(f_105,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_440,plain,(
    ! [A_97,B_98] :
      ( ~ v2_struct_0(k1_tex_2(A_97,B_98))
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_447,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_440])).

tff(c_451,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_447])).

tff(c_452,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_451])).

tff(c_467,plain,(
    ! [A_101,B_102] :
      ( m1_pre_topc(k1_tex_2(A_101,B_102),A_101)
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_472,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_467])).

tff(c_476,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_472])).

tff(c_477,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_476])).

tff(c_194,plain,(
    ! [A_66,B_67] :
      ( m1_pre_topc(k1_tex_2(A_66,B_67),A_66)
      | ~ m1_subset_1(B_67,u1_struct_0(A_66))
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_199,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_194])).

tff(c_203,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_199])).

tff(c_204,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_203])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( l1_pre_topc(B_5)
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_207,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_204,c_6])).

tff(c_210,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_207])).

tff(c_62,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_69,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_173,plain,(
    ! [A_64,B_65] :
      ( ~ v1_zfmisc_1(A_64)
      | ~ v1_subset_1(k6_domain_1(A_64,B_65),A_64)
      | ~ m1_subset_1(B_65,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_179,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_69,c_173])).

tff(c_182,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_179])).

tff(c_183,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_147,plain,(
    ! [A_60,B_61] :
      ( v7_struct_0(k1_tex_2(A_60,B_61))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_154,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_147])).

tff(c_158,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_154])).

tff(c_159,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_158])).

tff(c_105,plain,(
    ! [B_53,A_54] :
      ( m1_subset_1(u1_struct_0(B_53),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( v1_subset_1(B_22,A_21)
      | B_22 = A_21
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_218,plain,(
    ! [B_74,A_75] :
      ( v1_subset_1(u1_struct_0(B_74),u1_struct_0(A_75))
      | u1_struct_0(B_74) = u1_struct_0(A_75)
      | ~ m1_pre_topc(B_74,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_105,c_28])).

tff(c_16,plain,(
    ! [B_13,A_11] :
      ( m1_subset_1(u1_struct_0(B_13),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_212,plain,(
    ! [B_70,A_71] :
      ( v1_tex_2(B_70,A_71)
      | ~ v1_subset_1(u1_struct_0(B_70),u1_struct_0(A_71))
      | ~ m1_subset_1(u1_struct_0(B_70),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_216,plain,(
    ! [B_13,A_11] :
      ( v1_tex_2(B_13,A_11)
      | ~ v1_subset_1(u1_struct_0(B_13),u1_struct_0(A_11))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_212])).

tff(c_229,plain,(
    ! [B_76,A_77] :
      ( v1_tex_2(B_76,A_77)
      | u1_struct_0(B_76) = u1_struct_0(A_77)
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_218,c_216])).

tff(c_56,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_121,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_56])).

tff(c_235,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_229,c_121])).

tff(c_239,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_204,c_235])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | ~ v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_287,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_12])).

tff(c_317,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_287])).

tff(c_318,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_317])).

tff(c_322,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_318])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_322])).

tff(c_327,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_345,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_327,c_8])).

tff(c_349,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_345])).

tff(c_352,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_349])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_352])).

tff(c_357,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_484,plain,(
    ! [B_103,A_104] :
      ( ~ v1_tex_2(B_103,A_104)
      | v2_struct_0(B_103)
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104)
      | ~ v7_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_487,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_357,c_484])).

tff(c_490,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_477,c_487])).

tff(c_491,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_452,c_490])).

tff(c_406,plain,(
    ! [A_91,B_92] :
      ( v1_zfmisc_1(A_91)
      | k6_domain_1(A_91,B_92) != A_91
      | ~ m1_subset_1(B_92,A_91)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_422,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') != u1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_406])).

tff(c_466,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_422])).

tff(c_387,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k6_domain_1(A_86,B_87),k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_572,plain,(
    ! [A_121,B_122] :
      ( v1_subset_1(k6_domain_1(A_121,B_122),A_121)
      | k6_domain_1(A_121,B_122) = A_121
      | ~ m1_subset_1(B_122,A_121)
      | v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_387,c_28])).

tff(c_360,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_56])).

tff(c_578,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_572,c_360])).

tff(c_585,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_578])).

tff(c_586,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_466,c_585])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_361,plain,(
    ! [A_80] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_80))
      | ~ l1_struct_0(A_80)
      | v7_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_369,plain,(
    ! [A_80] :
      ( ~ l1_struct_0(A_80)
      | v7_struct_0(A_80)
      | ~ v1_xboole_0(u1_struct_0(A_80)) ) ),
    inference(resolution,[status(thm)],[c_2,c_361])).

tff(c_589,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_586,c_369])).

tff(c_595,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_589])).

tff(c_601,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_595])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_601])).

tff(c_606,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_422])).

tff(c_608,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_10,plain,(
    ! [A_7] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v7_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_627,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_608,c_10])).

tff(c_628,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_627])).

tff(c_631,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_628])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_631])).

tff(c_636,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_638,plain,(
    ! [A_123,B_124] :
      ( m1_pre_topc(k1_tex_2(A_123,B_124),A_123)
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_643,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_638])).

tff(c_647,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_643])).

tff(c_648,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_647])).

tff(c_690,plain,(
    ! [B_125,A_126] :
      ( ~ v1_tex_2(B_125,A_126)
      | v2_struct_0(B_125)
      | ~ m1_pre_topc(B_125,A_126)
      | ~ l1_pre_topc(A_126)
      | ~ v7_struct_0(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_693,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_357,c_690])).

tff(c_696,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_52,c_648,c_693])).

tff(c_698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_452,c_696])).

tff(c_699,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_717,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_699,c_8])).

tff(c_721,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_717])).

tff(c_724,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_721])).

tff(c_728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/2.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/2.63  
% 3.92/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/2.63  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.92/2.63  
% 3.92/2.63  %Foreground sorts:
% 3.92/2.63  
% 3.92/2.63  
% 3.92/2.63  %Background operators:
% 3.92/2.63  
% 3.92/2.63  
% 3.92/2.63  %Foreground operators:
% 3.92/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.92/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/2.63  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.92/2.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.92/2.63  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.92/2.63  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.92/2.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.92/2.63  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.92/2.63  tff('#skF_2', type, '#skF_2': $i).
% 3.92/2.63  tff('#skF_3', type, '#skF_3': $i).
% 3.92/2.63  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.92/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/2.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.92/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/2.63  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.92/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/2.63  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.92/2.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.92/2.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.92/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.92/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/2.63  
% 3.92/2.67  tff(f_178, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 3.92/2.67  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.92/2.67  tff(f_140, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.92/2.67  tff(f_126, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.92/2.67  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.92/2.67  tff(f_165, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.92/2.67  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.92/2.67  tff(f_112, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.92/2.67  tff(f_154, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tex_2)).
% 3.92/2.67  tff(f_62, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.92/2.67  tff(f_48, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.92/2.67  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 3.92/2.67  tff(f_105, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 3.92/2.67  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.92/2.67  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 3.92/2.67  tff(f_56, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.92/2.67  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.92/2.67  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.92/2.67  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.92/2.67  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.92/2.67  tff(c_440, plain, (![A_97, B_98]: (~v2_struct_0(k1_tex_2(A_97, B_98)) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.92/2.67  tff(c_447, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_440])).
% 3.92/2.67  tff(c_451, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_447])).
% 3.92/2.67  tff(c_452, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_451])).
% 3.92/2.67  tff(c_467, plain, (![A_101, B_102]: (m1_pre_topc(k1_tex_2(A_101, B_102), A_101) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.92/2.67  tff(c_472, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_467])).
% 3.92/2.67  tff(c_476, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_472])).
% 3.92/2.67  tff(c_477, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_476])).
% 3.92/2.67  tff(c_194, plain, (![A_66, B_67]: (m1_pre_topc(k1_tex_2(A_66, B_67), A_66) | ~m1_subset_1(B_67, u1_struct_0(A_66)) | ~l1_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.92/2.67  tff(c_199, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_194])).
% 3.92/2.67  tff(c_203, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_199])).
% 3.92/2.67  tff(c_204, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_203])).
% 3.92/2.67  tff(c_6, plain, (![B_5, A_3]: (l1_pre_topc(B_5) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.92/2.67  tff(c_207, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_204, c_6])).
% 3.92/2.67  tff(c_210, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_207])).
% 3.92/2.67  tff(c_62, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.92/2.67  tff(c_69, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.92/2.67  tff(c_173, plain, (![A_64, B_65]: (~v1_zfmisc_1(A_64) | ~v1_subset_1(k6_domain_1(A_64, B_65), A_64) | ~m1_subset_1(B_65, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.92/2.67  tff(c_179, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_69, c_173])).
% 3.92/2.67  tff(c_182, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_179])).
% 3.92/2.67  tff(c_183, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_182])).
% 3.92/2.67  tff(c_147, plain, (![A_60, B_61]: (v7_struct_0(k1_tex_2(A_60, B_61)) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.92/2.67  tff(c_154, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_147])).
% 3.92/2.67  tff(c_158, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_154])).
% 3.92/2.67  tff(c_159, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_158])).
% 3.92/2.67  tff(c_105, plain, (![B_53, A_54]: (m1_subset_1(u1_struct_0(B_53), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.92/2.67  tff(c_28, plain, (![B_22, A_21]: (v1_subset_1(B_22, A_21) | B_22=A_21 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.92/2.67  tff(c_218, plain, (![B_74, A_75]: (v1_subset_1(u1_struct_0(B_74), u1_struct_0(A_75)) | u1_struct_0(B_74)=u1_struct_0(A_75) | ~m1_pre_topc(B_74, A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_105, c_28])).
% 3.92/2.67  tff(c_16, plain, (![B_13, A_11]: (m1_subset_1(u1_struct_0(B_13), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.92/2.67  tff(c_212, plain, (![B_70, A_71]: (v1_tex_2(B_70, A_71) | ~v1_subset_1(u1_struct_0(B_70), u1_struct_0(A_71)) | ~m1_subset_1(u1_struct_0(B_70), k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.92/2.67  tff(c_216, plain, (![B_13, A_11]: (v1_tex_2(B_13, A_11) | ~v1_subset_1(u1_struct_0(B_13), u1_struct_0(A_11)) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_16, c_212])).
% 3.92/2.67  tff(c_229, plain, (![B_76, A_77]: (v1_tex_2(B_76, A_77) | u1_struct_0(B_76)=u1_struct_0(A_77) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_218, c_216])).
% 3.92/2.67  tff(c_56, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.92/2.67  tff(c_121, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_56])).
% 3.92/2.67  tff(c_235, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_229, c_121])).
% 3.92/2.67  tff(c_239, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_204, c_235])).
% 3.92/2.67  tff(c_12, plain, (![A_8]: (v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | ~v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.92/2.67  tff(c_287, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_239, c_12])).
% 3.92/2.67  tff(c_317, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_287])).
% 3.92/2.67  tff(c_318, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_183, c_317])).
% 3.92/2.67  tff(c_322, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_318])).
% 3.92/2.67  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_322])).
% 3.92/2.67  tff(c_327, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_182])).
% 3.92/2.67  tff(c_8, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.92/2.67  tff(c_345, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_327, c_8])).
% 3.92/2.67  tff(c_349, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_345])).
% 3.92/2.67  tff(c_352, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_349])).
% 3.92/2.67  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_352])).
% 3.92/2.67  tff(c_357, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 3.92/2.67  tff(c_484, plain, (![B_103, A_104]: (~v1_tex_2(B_103, A_104) | v2_struct_0(B_103) | ~m1_pre_topc(B_103, A_104) | ~l1_pre_topc(A_104) | ~v7_struct_0(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.92/2.67  tff(c_487, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_357, c_484])).
% 3.92/2.67  tff(c_490, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_477, c_487])).
% 3.92/2.67  tff(c_491, plain, (~v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_452, c_490])).
% 3.92/2.67  tff(c_406, plain, (![A_91, B_92]: (v1_zfmisc_1(A_91) | k6_domain_1(A_91, B_92)!=A_91 | ~m1_subset_1(B_92, A_91) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.92/2.67  tff(c_422, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')!=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_406])).
% 3.92/2.67  tff(c_466, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')!=u1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_422])).
% 3.92/2.67  tff(c_387, plain, (![A_86, B_87]: (m1_subset_1(k6_domain_1(A_86, B_87), k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.92/2.67  tff(c_572, plain, (![A_121, B_122]: (v1_subset_1(k6_domain_1(A_121, B_122), A_121) | k6_domain_1(A_121, B_122)=A_121 | ~m1_subset_1(B_122, A_121) | v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_387, c_28])).
% 3.92/2.67  tff(c_360, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_56])).
% 3.92/2.67  tff(c_578, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_572, c_360])).
% 3.92/2.67  tff(c_585, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_578])).
% 3.92/2.67  tff(c_586, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_466, c_585])).
% 3.92/2.67  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.92/2.67  tff(c_361, plain, (![A_80]: (~v1_zfmisc_1(u1_struct_0(A_80)) | ~l1_struct_0(A_80) | v7_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.92/2.67  tff(c_369, plain, (![A_80]: (~l1_struct_0(A_80) | v7_struct_0(A_80) | ~v1_xboole_0(u1_struct_0(A_80)))), inference(resolution, [status(thm)], [c_2, c_361])).
% 3.92/2.67  tff(c_589, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_586, c_369])).
% 3.92/2.67  tff(c_595, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_491, c_589])).
% 3.92/2.67  tff(c_601, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_595])).
% 3.92/2.67  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_601])).
% 3.92/2.67  tff(c_606, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_422])).
% 3.92/2.67  tff(c_608, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_606])).
% 3.92/2.67  tff(c_10, plain, (![A_7]: (~v1_zfmisc_1(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v7_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.92/2.67  tff(c_627, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_608, c_10])).
% 3.92/2.67  tff(c_628, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_627])).
% 3.92/2.67  tff(c_631, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_628])).
% 3.92/2.67  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_631])).
% 3.92/2.67  tff(c_636, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_627])).
% 3.92/2.67  tff(c_638, plain, (![A_123, B_124]: (m1_pre_topc(k1_tex_2(A_123, B_124), A_123) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.92/2.67  tff(c_643, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_638])).
% 3.92/2.67  tff(c_647, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_643])).
% 3.92/2.67  tff(c_648, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_647])).
% 3.92/2.67  tff(c_690, plain, (![B_125, A_126]: (~v1_tex_2(B_125, A_126) | v2_struct_0(B_125) | ~m1_pre_topc(B_125, A_126) | ~l1_pre_topc(A_126) | ~v7_struct_0(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.92/2.67  tff(c_693, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_357, c_690])).
% 3.92/2.67  tff(c_696, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_636, c_52, c_648, c_693])).
% 3.92/2.67  tff(c_698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_452, c_696])).
% 3.92/2.67  tff(c_699, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_606])).
% 3.92/2.67  tff(c_717, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_699, c_8])).
% 3.92/2.67  tff(c_721, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_717])).
% 3.92/2.67  tff(c_724, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_721])).
% 3.92/2.67  tff(c_728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_724])).
% 3.92/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/2.67  
% 3.92/2.67  Inference rules
% 3.92/2.67  ----------------------
% 3.92/2.67  #Ref     : 0
% 3.92/2.67  #Sup     : 120
% 3.92/2.67  #Fact    : 0
% 3.92/2.67  #Define  : 0
% 3.92/2.67  #Split   : 8
% 3.92/2.67  #Chain   : 0
% 3.92/2.67  #Close   : 0
% 3.92/2.67  
% 3.92/2.67  Ordering : KBO
% 3.92/2.67  
% 3.92/2.67  Simplification rules
% 3.92/2.67  ----------------------
% 3.92/2.67  #Subsume      : 14
% 3.92/2.67  #Demod        : 53
% 3.92/2.67  #Tautology    : 23
% 3.92/2.67  #SimpNegUnit  : 27
% 3.92/2.67  #BackRed      : 1
% 3.92/2.67  
% 3.92/2.67  #Partial instantiations: 0
% 3.92/2.67  #Strategies tried      : 1
% 3.92/2.67  
% 3.92/2.67  Timing (in seconds)
% 3.92/2.67  ----------------------
% 3.92/2.67  Preprocessing        : 0.73
% 3.92/2.67  Parsing              : 0.39
% 3.92/2.67  CNF conversion       : 0.07
% 3.92/2.67  Main loop            : 0.83
% 3.92/2.67  Inferencing          : 0.32
% 3.92/2.67  Reduction            : 0.24
% 3.92/2.67  Demodulation         : 0.15
% 3.92/2.67  BG Simplification    : 0.05
% 3.92/2.67  Subsumption          : 0.16
% 3.92/2.67  Abstraction          : 0.03
% 3.92/2.67  MUC search           : 0.00
% 3.92/2.67  Cooper               : 0.00
% 3.92/2.68  Total                : 1.64
% 3.92/2.68  Index Insertion      : 0.00
% 3.92/2.68  Index Deletion       : 0.00
% 3.92/2.68  Index Matching       : 0.00
% 3.92/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------

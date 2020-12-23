%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:02 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 515 expanded)
%              Number of leaves         :   39 ( 177 expanded)
%              Depth                    :   14
%              Number of atoms          :  332 (1331 expanded)
%              Number of equality atoms :   16 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_166,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_107,axiom,(
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

tff(f_128,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_114,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_zfmisc_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_1)).

tff(f_93,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_627,plain,(
    ! [A_169,B_170] :
      ( ~ v2_struct_0(k1_tex_2(A_169,B_170))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l1_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_630,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_627])).

tff(c_633,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_630])).

tff(c_634,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_633])).

tff(c_12,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_635,plain,(
    ! [A_171,B_172] :
      ( v1_subset_1(k6_domain_1(A_171,B_172),A_171)
      | ~ m1_subset_1(B_172,A_171)
      | v1_zfmisc_1(A_171)
      | v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_64,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_78,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_353,plain,(
    ! [A_114,B_115] :
      ( ~ v7_struct_0(A_114)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_114),B_115),u1_struct_0(A_114))
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_366,plain,
    ( ~ v7_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_353])).

tff(c_376,plain,
    ( ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_366])).

tff(c_377,plain,
    ( ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_376])).

tff(c_378,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_381,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_378])).

tff(c_385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_381])).

tff(c_386,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_387,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_212,plain,(
    ! [B_90,A_91] :
      ( u1_struct_0(B_90) = '#skF_1'(A_91,B_90)
      | v1_tex_2(B_90,A_91)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_58,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_185,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58])).

tff(c_215,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_185])).

tff(c_218,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_215])).

tff(c_219,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_220,plain,(
    ! [A_92,B_93] :
      ( m1_pre_topc(k1_tex_2(A_92,B_93),A_92)
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l1_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_222,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_220])).

tff(c_225,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_222])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_219,c_225])).

tff(c_229,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_303,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1('#skF_1'(A_103,B_104),k1_zfmisc_1(u1_struct_0(A_103)))
      | v1_tex_2(B_104,A_103)
      | ~ m1_pre_topc(B_104,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    ! [B_30,A_29] :
      ( v1_subset_1(B_30,A_29)
      | B_30 = A_29
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_406,plain,(
    ! [A_122,B_123] :
      ( v1_subset_1('#skF_1'(A_122,B_123),u1_struct_0(A_122))
      | u1_struct_0(A_122) = '#skF_1'(A_122,B_123)
      | v1_tex_2(B_123,A_122)
      | ~ m1_pre_topc(B_123,A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(resolution,[status(thm)],[c_303,c_32])).

tff(c_26,plain,(
    ! [A_19,B_25] :
      ( ~ v1_subset_1('#skF_1'(A_19,B_25),u1_struct_0(A_19))
      | v1_tex_2(B_25,A_19)
      | ~ m1_pre_topc(B_25,A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_416,plain,(
    ! [A_124,B_125] :
      ( u1_struct_0(A_124) = '#skF_1'(A_124,B_125)
      | v1_tex_2(B_125,A_124)
      | ~ m1_pre_topc(B_125,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_406,c_26])).

tff(c_422,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_416,c_185])).

tff(c_426,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_229,c_422])).

tff(c_14,plain,(
    ! [B_13,A_11] :
      ( l1_pre_topc(B_13)
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_232,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_229,c_14])).

tff(c_235,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232])).

tff(c_203,plain,(
    ! [A_86,B_87] :
      ( v7_struct_0(k1_tex_2(A_86,B_87))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_206,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_203])).

tff(c_209,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_206])).

tff(c_210,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_209])).

tff(c_228,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_18,plain,(
    ! [A_15] :
      ( v1_zfmisc_1(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | ~ v7_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_251,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_18])).

tff(c_265,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_251])).

tff(c_279,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_282,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_279])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_282])).

tff(c_287,plain,(
    v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_432,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_287])).

tff(c_16,plain,(
    ! [A_14] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v7_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_467,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_432,c_16])).

tff(c_473,plain,(
    v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_467])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_386,c_473])).

tff(c_477,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_638,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_635,c_477])).

tff(c_641,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_638])).

tff(c_642,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | B_44 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_2,c_67])).

tff(c_648,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_642,c_70])).

tff(c_652,plain,(
    m1_subset_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_52])).

tff(c_708,plain,(
    ! [A_182,B_183] :
      ( m1_pre_topc(k1_tex_2(A_182,B_183),A_182)
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_710,plain,(
    ! [B_183] :
      ( m1_pre_topc(k1_tex_2('#skF_2',B_183),'#skF_2')
      | ~ m1_subset_1(B_183,k1_xboole_0)
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_708])).

tff(c_712,plain,(
    ! [B_183] :
      ( m1_pre_topc(k1_tex_2('#skF_2',B_183),'#skF_2')
      | ~ m1_subset_1(B_183,k1_xboole_0)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_710])).

tff(c_713,plain,(
    ! [B_183] :
      ( m1_pre_topc(k1_tex_2('#skF_2',B_183),'#skF_2')
      | ~ m1_subset_1(B_183,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_712])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_492,plain,(
    ! [B_130,A_131] :
      ( v1_zfmisc_1(B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_131))
      | ~ v1_zfmisc_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_496,plain,(
    ! [A_3] :
      ( v1_zfmisc_1(k1_xboole_0)
      | ~ v1_zfmisc_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_492])).

tff(c_497,plain,(
    ! [A_3] : ~ v1_zfmisc_1(A_3) ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_48,plain,(
    ! [A_35,B_37] :
      ( v1_subset_1(k6_domain_1(A_35,B_37),A_35)
      | ~ m1_subset_1(B_37,A_35)
      | v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_527,plain,(
    ! [A_144,B_145] :
      ( v1_subset_1(k6_domain_1(A_144,B_145),A_144)
      | ~ m1_subset_1(B_145,A_144)
      | v1_xboole_0(A_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_48])).

tff(c_530,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_527,c_477])).

tff(c_533,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_530])).

tff(c_539,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_533,c_70])).

tff(c_590,plain,(
    ! [A_157,B_158] :
      ( m1_pre_topc(k1_tex_2(A_157,B_158),A_157)
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l1_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_592,plain,(
    ! [B_158] :
      ( m1_pre_topc(k1_tex_2('#skF_2',B_158),'#skF_2')
      | ~ m1_subset_1(B_158,k1_xboole_0)
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_590])).

tff(c_594,plain,(
    ! [B_158] :
      ( m1_pre_topc(k1_tex_2('#skF_2',B_158),'#skF_2')
      | ~ m1_subset_1(B_158,k1_xboole_0)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_592])).

tff(c_596,plain,(
    ! [B_159] :
      ( m1_pre_topc(k1_tex_2('#skF_2',B_159),'#skF_2')
      | ~ m1_subset_1(B_159,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_594])).

tff(c_599,plain,(
    ! [B_159] :
      ( l1_pre_topc(k1_tex_2('#skF_2',B_159))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_159,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_596,c_14])).

tff(c_603,plain,(
    ! [B_160] :
      ( l1_pre_topc(k1_tex_2('#skF_2',B_160))
      | ~ m1_subset_1(B_160,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_599])).

tff(c_555,plain,(
    ! [A_146,B_147] :
      ( v7_struct_0(k1_tex_2(A_146,B_147))
      | ~ m1_subset_1(B_147,u1_struct_0(A_146))
      | ~ l1_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_558,plain,(
    ! [B_147] :
      ( v7_struct_0(k1_tex_2('#skF_2',B_147))
      | ~ m1_subset_1(B_147,k1_xboole_0)
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_555])).

tff(c_560,plain,(
    ! [B_147] :
      ( v7_struct_0(k1_tex_2('#skF_2',B_147))
      | ~ m1_subset_1(B_147,k1_xboole_0)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_558])).

tff(c_570,plain,(
    ! [B_149] :
      ( v7_struct_0(k1_tex_2('#skF_2',B_149))
      | ~ m1_subset_1(B_149,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_560])).

tff(c_499,plain,(
    ! [A_15] :
      ( ~ l1_struct_0(A_15)
      | ~ v7_struct_0(A_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_18])).

tff(c_575,plain,(
    ! [B_150] :
      ( ~ l1_struct_0(k1_tex_2('#skF_2',B_150))
      | ~ m1_subset_1(B_150,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_570,c_499])).

tff(c_579,plain,(
    ! [B_150] :
      ( ~ m1_subset_1(B_150,k1_xboole_0)
      | ~ l1_pre_topc(k1_tex_2('#skF_2',B_150)) ) ),
    inference(resolution,[status(thm)],[c_12,c_575])).

tff(c_607,plain,(
    ! [B_160] : ~ m1_subset_1(B_160,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_603,c_579])).

tff(c_543,plain,(
    m1_subset_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_52])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_607,c_543])).

tff(c_610,plain,(
    v1_zfmisc_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_660,plain,
    ( ~ v1_zfmisc_1(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_16])).

tff(c_670,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_660])).

tff(c_673,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_670])).

tff(c_676,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_673])).

tff(c_680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_676])).

tff(c_681,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_670])).

tff(c_476,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_729,plain,(
    ! [B_189,A_190] :
      ( ~ v1_tex_2(B_189,A_190)
      | v2_struct_0(B_189)
      | ~ m1_pre_topc(B_189,A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v7_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_735,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_476,c_729])).

tff(c_739,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_54,c_735])).

tff(c_740,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_634,c_739])).

tff(c_743,plain,(
    ~ m1_subset_1('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_713,c_740])).

tff(c_747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_743])).

tff(c_748,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_753,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_748,c_16])).

tff(c_754,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_757,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_754])).

tff(c_761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_757])).

tff(c_762,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_780,plain,(
    ! [A_195,B_196] :
      ( m1_pre_topc(k1_tex_2(A_195,B_196),A_195)
      | ~ m1_subset_1(B_196,u1_struct_0(A_195))
      | ~ l1_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_782,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_780])).

tff(c_785,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_782])).

tff(c_786,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_785])).

tff(c_795,plain,(
    ! [B_201,A_202] :
      ( ~ v1_tex_2(B_201,A_202)
      | v2_struct_0(B_201)
      | ~ m1_pre_topc(B_201,A_202)
      | ~ l1_pre_topc(A_202)
      | ~ v7_struct_0(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_801,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_476,c_795])).

tff(c_805,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_54,c_786,c_801])).

tff(c_807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_634,c_805])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:16:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.46  
% 3.23/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.24/1.47  
% 3.24/1.47  %Foreground sorts:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Background operators:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Foreground operators:
% 3.24/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.24/1.47  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.24/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.47  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.24/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.24/1.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.24/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.47  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.24/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.47  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.47  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.24/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.24/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.24/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.24/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.47  
% 3.24/1.49  tff(f_179, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 3.24/1.49  tff(f_142, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.24/1.49  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.24/1.49  tff(f_153, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 3.24/1.49  tff(f_166, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 3.24/1.49  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 3.24/1.49  tff(f_128, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.24/1.49  tff(f_114, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.24/1.49  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.24/1.49  tff(f_74, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.24/1.49  tff(f_68, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.24/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.24/1.49  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.24/1.49  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.24/1.49  tff(f_49, axiom, (![A]: (v1_zfmisc_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_zfmisc_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_1)).
% 3.24/1.49  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 3.24/1.49  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.24/1.49  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.24/1.49  tff(c_52, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.24/1.49  tff(c_627, plain, (![A_169, B_170]: (~v2_struct_0(k1_tex_2(A_169, B_170)) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l1_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.24/1.49  tff(c_630, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_627])).
% 3.24/1.49  tff(c_633, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_630])).
% 3.24/1.49  tff(c_634, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_633])).
% 3.24/1.49  tff(c_12, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.49  tff(c_635, plain, (![A_171, B_172]: (v1_subset_1(k6_domain_1(A_171, B_172), A_171) | ~m1_subset_1(B_172, A_171) | v1_zfmisc_1(A_171) | v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.24/1.49  tff(c_64, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.24/1.49  tff(c_78, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_64])).
% 3.24/1.49  tff(c_353, plain, (![A_114, B_115]: (~v7_struct_0(A_114) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_114), B_115), u1_struct_0(A_114)) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.24/1.49  tff(c_366, plain, (~v7_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_353])).
% 3.24/1.49  tff(c_376, plain, (~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_366])).
% 3.24/1.49  tff(c_377, plain, (~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_376])).
% 3.24/1.49  tff(c_378, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_377])).
% 3.24/1.49  tff(c_381, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_378])).
% 3.24/1.49  tff(c_385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_381])).
% 3.24/1.49  tff(c_386, plain, (~v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_377])).
% 3.24/1.49  tff(c_387, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_377])).
% 3.24/1.49  tff(c_212, plain, (![B_90, A_91]: (u1_struct_0(B_90)='#skF_1'(A_91, B_90) | v1_tex_2(B_90, A_91) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.24/1.49  tff(c_58, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.24/1.49  tff(c_185, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58])).
% 3.24/1.49  tff(c_215, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_212, c_185])).
% 3.24/1.49  tff(c_218, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_215])).
% 3.24/1.49  tff(c_219, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_218])).
% 3.24/1.49  tff(c_220, plain, (![A_92, B_93]: (m1_pre_topc(k1_tex_2(A_92, B_93), A_92) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l1_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.24/1.49  tff(c_222, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_220])).
% 3.24/1.49  tff(c_225, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_222])).
% 3.24/1.49  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_219, c_225])).
% 3.24/1.49  tff(c_229, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_218])).
% 3.24/1.49  tff(c_303, plain, (![A_103, B_104]: (m1_subset_1('#skF_1'(A_103, B_104), k1_zfmisc_1(u1_struct_0(A_103))) | v1_tex_2(B_104, A_103) | ~m1_pre_topc(B_104, A_103) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.24/1.49  tff(c_32, plain, (![B_30, A_29]: (v1_subset_1(B_30, A_29) | B_30=A_29 | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.24/1.49  tff(c_406, plain, (![A_122, B_123]: (v1_subset_1('#skF_1'(A_122, B_123), u1_struct_0(A_122)) | u1_struct_0(A_122)='#skF_1'(A_122, B_123) | v1_tex_2(B_123, A_122) | ~m1_pre_topc(B_123, A_122) | ~l1_pre_topc(A_122))), inference(resolution, [status(thm)], [c_303, c_32])).
% 3.24/1.49  tff(c_26, plain, (![A_19, B_25]: (~v1_subset_1('#skF_1'(A_19, B_25), u1_struct_0(A_19)) | v1_tex_2(B_25, A_19) | ~m1_pre_topc(B_25, A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.24/1.49  tff(c_416, plain, (![A_124, B_125]: (u1_struct_0(A_124)='#skF_1'(A_124, B_125) | v1_tex_2(B_125, A_124) | ~m1_pre_topc(B_125, A_124) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_406, c_26])).
% 3.24/1.49  tff(c_422, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_416, c_185])).
% 3.24/1.49  tff(c_426, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_229, c_422])).
% 3.24/1.49  tff(c_14, plain, (![B_13, A_11]: (l1_pre_topc(B_13) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.24/1.49  tff(c_232, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_229, c_14])).
% 3.24/1.49  tff(c_235, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232])).
% 3.24/1.49  tff(c_203, plain, (![A_86, B_87]: (v7_struct_0(k1_tex_2(A_86, B_87)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.24/1.49  tff(c_206, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_203])).
% 3.24/1.49  tff(c_209, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_206])).
% 3.24/1.49  tff(c_210, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_209])).
% 3.24/1.49  tff(c_228, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_218])).
% 3.24/1.49  tff(c_18, plain, (![A_15]: (v1_zfmisc_1(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | ~v7_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.24/1.49  tff(c_251, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_18])).
% 3.24/1.49  tff(c_265, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_251])).
% 3.24/1.49  tff(c_279, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_265])).
% 3.24/1.49  tff(c_282, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_279])).
% 3.24/1.49  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_235, c_282])).
% 3.24/1.49  tff(c_287, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_265])).
% 3.24/1.49  tff(c_432, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_287])).
% 3.24/1.49  tff(c_16, plain, (![A_14]: (~v1_zfmisc_1(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v7_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.24/1.49  tff(c_467, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_432, c_16])).
% 3.24/1.49  tff(c_473, plain, (v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_467])).
% 3.24/1.49  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_386, c_473])).
% 3.24/1.49  tff(c_477, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_64])).
% 3.24/1.49  tff(c_638, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_635, c_477])).
% 3.24/1.49  tff(c_641, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_638])).
% 3.24/1.49  tff(c_642, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_641])).
% 3.24/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.24/1.49  tff(c_67, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | B_44=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.49  tff(c_70, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_2, c_67])).
% 3.24/1.49  tff(c_648, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_642, c_70])).
% 3.24/1.49  tff(c_652, plain, (m1_subset_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_648, c_52])).
% 3.24/1.49  tff(c_708, plain, (![A_182, B_183]: (m1_pre_topc(k1_tex_2(A_182, B_183), A_182) | ~m1_subset_1(B_183, u1_struct_0(A_182)) | ~l1_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.24/1.49  tff(c_710, plain, (![B_183]: (m1_pre_topc(k1_tex_2('#skF_2', B_183), '#skF_2') | ~m1_subset_1(B_183, k1_xboole_0) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_648, c_708])).
% 3.24/1.49  tff(c_712, plain, (![B_183]: (m1_pre_topc(k1_tex_2('#skF_2', B_183), '#skF_2') | ~m1_subset_1(B_183, k1_xboole_0) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_710])).
% 3.24/1.49  tff(c_713, plain, (![B_183]: (m1_pre_topc(k1_tex_2('#skF_2', B_183), '#skF_2') | ~m1_subset_1(B_183, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_56, c_712])).
% 3.24/1.49  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.24/1.49  tff(c_492, plain, (![B_130, A_131]: (v1_zfmisc_1(B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_131)) | ~v1_zfmisc_1(A_131))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.49  tff(c_496, plain, (![A_3]: (v1_zfmisc_1(k1_xboole_0) | ~v1_zfmisc_1(A_3))), inference(resolution, [status(thm)], [c_6, c_492])).
% 3.24/1.49  tff(c_497, plain, (![A_3]: (~v1_zfmisc_1(A_3))), inference(splitLeft, [status(thm)], [c_496])).
% 3.24/1.49  tff(c_48, plain, (![A_35, B_37]: (v1_subset_1(k6_domain_1(A_35, B_37), A_35) | ~m1_subset_1(B_37, A_35) | v1_zfmisc_1(A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.24/1.49  tff(c_527, plain, (![A_144, B_145]: (v1_subset_1(k6_domain_1(A_144, B_145), A_144) | ~m1_subset_1(B_145, A_144) | v1_xboole_0(A_144))), inference(negUnitSimplification, [status(thm)], [c_497, c_48])).
% 3.24/1.49  tff(c_530, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_527, c_477])).
% 3.24/1.49  tff(c_533, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_530])).
% 3.24/1.49  tff(c_539, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_533, c_70])).
% 3.24/1.49  tff(c_590, plain, (![A_157, B_158]: (m1_pre_topc(k1_tex_2(A_157, B_158), A_157) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l1_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.24/1.49  tff(c_592, plain, (![B_158]: (m1_pre_topc(k1_tex_2('#skF_2', B_158), '#skF_2') | ~m1_subset_1(B_158, k1_xboole_0) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_539, c_590])).
% 3.24/1.49  tff(c_594, plain, (![B_158]: (m1_pre_topc(k1_tex_2('#skF_2', B_158), '#skF_2') | ~m1_subset_1(B_158, k1_xboole_0) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_592])).
% 3.24/1.49  tff(c_596, plain, (![B_159]: (m1_pre_topc(k1_tex_2('#skF_2', B_159), '#skF_2') | ~m1_subset_1(B_159, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_56, c_594])).
% 3.24/1.49  tff(c_599, plain, (![B_159]: (l1_pre_topc(k1_tex_2('#skF_2', B_159)) | ~l1_pre_topc('#skF_2') | ~m1_subset_1(B_159, k1_xboole_0))), inference(resolution, [status(thm)], [c_596, c_14])).
% 3.24/1.49  tff(c_603, plain, (![B_160]: (l1_pre_topc(k1_tex_2('#skF_2', B_160)) | ~m1_subset_1(B_160, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_599])).
% 3.24/1.49  tff(c_555, plain, (![A_146, B_147]: (v7_struct_0(k1_tex_2(A_146, B_147)) | ~m1_subset_1(B_147, u1_struct_0(A_146)) | ~l1_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.24/1.49  tff(c_558, plain, (![B_147]: (v7_struct_0(k1_tex_2('#skF_2', B_147)) | ~m1_subset_1(B_147, k1_xboole_0) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_539, c_555])).
% 3.24/1.49  tff(c_560, plain, (![B_147]: (v7_struct_0(k1_tex_2('#skF_2', B_147)) | ~m1_subset_1(B_147, k1_xboole_0) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_558])).
% 3.24/1.49  tff(c_570, plain, (![B_149]: (v7_struct_0(k1_tex_2('#skF_2', B_149)) | ~m1_subset_1(B_149, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_56, c_560])).
% 3.24/1.49  tff(c_499, plain, (![A_15]: (~l1_struct_0(A_15) | ~v7_struct_0(A_15))), inference(negUnitSimplification, [status(thm)], [c_497, c_18])).
% 3.24/1.49  tff(c_575, plain, (![B_150]: (~l1_struct_0(k1_tex_2('#skF_2', B_150)) | ~m1_subset_1(B_150, k1_xboole_0))), inference(resolution, [status(thm)], [c_570, c_499])).
% 3.24/1.49  tff(c_579, plain, (![B_150]: (~m1_subset_1(B_150, k1_xboole_0) | ~l1_pre_topc(k1_tex_2('#skF_2', B_150)))), inference(resolution, [status(thm)], [c_12, c_575])).
% 3.24/1.49  tff(c_607, plain, (![B_160]: (~m1_subset_1(B_160, k1_xboole_0))), inference(resolution, [status(thm)], [c_603, c_579])).
% 3.24/1.49  tff(c_543, plain, (m1_subset_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_539, c_52])).
% 3.24/1.49  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_607, c_543])).
% 3.24/1.49  tff(c_610, plain, (v1_zfmisc_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_496])).
% 3.24/1.49  tff(c_660, plain, (~v1_zfmisc_1(k1_xboole_0) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_648, c_16])).
% 3.24/1.49  tff(c_670, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_610, c_660])).
% 3.24/1.49  tff(c_673, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_670])).
% 3.24/1.49  tff(c_676, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_673])).
% 3.24/1.49  tff(c_680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_676])).
% 3.24/1.49  tff(c_681, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_670])).
% 3.24/1.49  tff(c_476, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 3.24/1.49  tff(c_729, plain, (![B_189, A_190]: (~v1_tex_2(B_189, A_190) | v2_struct_0(B_189) | ~m1_pre_topc(B_189, A_190) | ~l1_pre_topc(A_190) | ~v7_struct_0(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.24/1.49  tff(c_735, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_476, c_729])).
% 3.24/1.49  tff(c_739, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_54, c_735])).
% 3.24/1.49  tff(c_740, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_634, c_739])).
% 3.24/1.49  tff(c_743, plain, (~m1_subset_1('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_713, c_740])).
% 3.24/1.49  tff(c_747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_652, c_743])).
% 3.24/1.49  tff(c_748, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_641])).
% 3.24/1.49  tff(c_753, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_748, c_16])).
% 3.24/1.49  tff(c_754, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_753])).
% 3.24/1.49  tff(c_757, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_754])).
% 3.24/1.49  tff(c_761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_757])).
% 3.24/1.49  tff(c_762, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_753])).
% 3.24/1.49  tff(c_780, plain, (![A_195, B_196]: (m1_pre_topc(k1_tex_2(A_195, B_196), A_195) | ~m1_subset_1(B_196, u1_struct_0(A_195)) | ~l1_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.24/1.49  tff(c_782, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_780])).
% 3.24/1.49  tff(c_785, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_782])).
% 3.24/1.49  tff(c_786, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_785])).
% 3.24/1.49  tff(c_795, plain, (![B_201, A_202]: (~v1_tex_2(B_201, A_202) | v2_struct_0(B_201) | ~m1_pre_topc(B_201, A_202) | ~l1_pre_topc(A_202) | ~v7_struct_0(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.24/1.49  tff(c_801, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_476, c_795])).
% 3.24/1.49  tff(c_805, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_762, c_54, c_786, c_801])).
% 3.24/1.49  tff(c_807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_634, c_805])).
% 3.24/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.49  
% 3.24/1.49  Inference rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Ref     : 0
% 3.24/1.49  #Sup     : 116
% 3.24/1.49  #Fact    : 0
% 3.24/1.49  #Define  : 0
% 3.24/1.49  #Split   : 9
% 3.24/1.49  #Chain   : 0
% 3.24/1.49  #Close   : 0
% 3.24/1.49  
% 3.24/1.49  Ordering : KBO
% 3.24/1.49  
% 3.24/1.49  Simplification rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Subsume      : 19
% 3.24/1.49  #Demod        : 117
% 3.24/1.49  #Tautology    : 27
% 3.24/1.49  #SimpNegUnit  : 46
% 3.24/1.49  #BackRed      : 17
% 3.24/1.49  
% 3.24/1.49  #Partial instantiations: 0
% 3.24/1.49  #Strategies tried      : 1
% 3.24/1.49  
% 3.24/1.49  Timing (in seconds)
% 3.24/1.49  ----------------------
% 3.24/1.49  Preprocessing        : 0.35
% 3.24/1.49  Parsing              : 0.18
% 3.24/1.49  CNF conversion       : 0.02
% 3.24/1.49  Main loop            : 0.36
% 3.24/1.49  Inferencing          : 0.14
% 3.24/1.49  Reduction            : 0.11
% 3.24/1.49  Demodulation         : 0.07
% 3.24/1.49  BG Simplification    : 0.02
% 3.24/1.49  Subsumption          : 0.06
% 3.24/1.49  Abstraction          : 0.02
% 3.24/1.49  MUC search           : 0.00
% 3.24/1.49  Cooper               : 0.00
% 3.24/1.49  Total                : 0.76
% 3.24/1.49  Index Insertion      : 0.00
% 3.24/1.49  Index Deletion       : 0.00
% 3.24/1.49  Index Matching       : 0.00
% 3.24/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

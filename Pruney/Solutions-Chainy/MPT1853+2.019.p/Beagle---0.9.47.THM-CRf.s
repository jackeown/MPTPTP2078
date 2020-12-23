%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:02 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 355 expanded)
%              Number of leaves         :   36 ( 129 expanded)
%              Depth                    :   14
%              Number of atoms          :  265 ( 954 expanded)
%              Number of equality atoms :   18 (  41 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_94,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_156,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_108,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_549,plain,(
    ! [A_103,B_104] :
      ( ~ v2_struct_0(k1_tex_2(A_103,B_104))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_556,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_549])).

tff(c_560,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_556])).

tff(c_561,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_560])).

tff(c_526,plain,(
    ! [A_99,B_100] :
      ( v1_zfmisc_1(A_99)
      | k6_domain_1(A_99,B_100) != A_99
      | ~ m1_subset_1(B_100,A_99)
      | v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_534,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_526])).

tff(c_589,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_534])).

tff(c_535,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1(k6_domain_1(A_101,B_102),k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,A_101)
      | v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [B_28,A_27] :
      ( v1_subset_1(B_28,A_27)
      | B_28 = A_27
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_654,plain,(
    ! [A_124,B_125] :
      ( v1_subset_1(k6_domain_1(A_124,B_125),A_124)
      | k6_domain_1(A_124,B_125) = A_124
      | ~ m1_subset_1(B_125,A_124)
      | v1_xboole_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_535,c_32])).

tff(c_62,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_73,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_353,plain,(
    ! [A_83,B_84] :
      ( ~ v7_struct_0(A_83)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_83),B_84),u1_struct_0(A_83))
      | ~ m1_subset_1(B_84,u1_struct_0(A_83))
      | ~ l1_struct_0(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_370,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_353])).

tff(c_380,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_370])).

tff(c_381,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_380])).

tff(c_382,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_385,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_382])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_385])).

tff(c_390,plain,(
    ~ v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_391,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_160,plain,(
    ! [A_60,B_61] :
      ( m1_pre_topc(k1_tex_2(A_60,B_61),A_60)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_165,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_160])).

tff(c_169,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_165])).

tff(c_170,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_169])).

tff(c_288,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1('#skF_2'(A_71,B_72),k1_zfmisc_1(u1_struct_0(A_71)))
      | v1_tex_2(B_72,A_71)
      | ~ m1_pre_topc(B_72,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_450,plain,(
    ! [A_91,B_92] :
      ( v1_subset_1('#skF_2'(A_91,B_92),u1_struct_0(A_91))
      | u1_struct_0(A_91) = '#skF_2'(A_91,B_92)
      | v1_tex_2(B_92,A_91)
      | ~ m1_pre_topc(B_92,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_288,c_32])).

tff(c_26,plain,(
    ! [A_17,B_23] :
      ( ~ v1_subset_1('#skF_2'(A_17,B_23),u1_struct_0(A_17))
      | v1_tex_2(B_23,A_17)
      | ~ m1_pre_topc(B_23,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_460,plain,(
    ! [A_93,B_94] :
      ( u1_struct_0(A_93) = '#skF_2'(A_93,B_94)
      | v1_tex_2(B_94,A_93)
      | ~ m1_pre_topc(B_94,A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_450,c_26])).

tff(c_56,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_138,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56])).

tff(c_466,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_460,c_138])).

tff(c_470,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_170,c_466])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_173,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_4])).

tff(c_176,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_173])).

tff(c_111,plain,(
    ! [A_52,B_53] :
      ( ~ v2_struct_0(k1_tex_2(A_52,B_53))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_118,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_111])).

tff(c_122,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_118])).

tff(c_123,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_122])).

tff(c_153,plain,(
    ! [B_58,A_59] :
      ( u1_struct_0(B_58) = '#skF_2'(A_59,B_58)
      | v1_tex_2(B_58,A_59)
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_156,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_138])).

tff(c_159,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_156])).

tff(c_178,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_159])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_196,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_6])).

tff(c_215,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_196])).

tff(c_219,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_222,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_222])).

tff(c_228,plain,(
    l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_139,plain,(
    ! [A_56,B_57] :
      ( v7_struct_0(k1_tex_2(A_56,B_57))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_146,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_139])).

tff(c_150,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_146])).

tff(c_151,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_150])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_zfmisc_1(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | ~ v7_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_199,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_10])).

tff(c_217,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_199])).

tff(c_230,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_217])).

tff(c_481,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_230])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_502,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_481,c_8])).

tff(c_505,plain,(
    v7_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_502])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_505])).

tff(c_509,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_661,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_654,c_509])).

tff(c_668,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_661])).

tff(c_669,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_668])).

tff(c_672,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_669,c_6])).

tff(c_675,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_672])).

tff(c_678,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_675])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_678])).

tff(c_683,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_685,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_689,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_685,c_8])).

tff(c_701,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_689])).

tff(c_704,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_701])).

tff(c_708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_704])).

tff(c_709,plain,(
    v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_689])).

tff(c_690,plain,(
    ! [A_126,B_127] :
      ( m1_pre_topc(k1_tex_2(A_126,B_127),A_126)
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l1_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_695,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_690])).

tff(c_699,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_695])).

tff(c_700,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_699])).

tff(c_508,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_728,plain,(
    ! [B_128,A_129] :
      ( ~ v1_tex_2(B_128,A_129)
      | v2_struct_0(B_128)
      | ~ m1_pre_topc(B_128,A_129)
      | ~ l1_pre_topc(A_129)
      | ~ v7_struct_0(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_734,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_508,c_728])).

tff(c_738,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_52,c_700,c_734])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_561,c_738])).

tff(c_741,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_745,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_741,c_6])).

tff(c_748,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_745])).

tff(c_751,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_748])).

tff(c_755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:44:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.47  
% 2.98/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.47  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.98/1.47  
% 2.98/1.47  %Foreground sorts:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Background operators:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Foreground operators:
% 2.98/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.98/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.98/1.47  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.98/1.47  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.98/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.98/1.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.98/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.47  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.98/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.47  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.98/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.98/1.47  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.98/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.98/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.47  
% 3.22/1.49  tff(f_169, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 3.22/1.49  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.22/1.49  tff(f_143, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.22/1.49  tff(f_94, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.22/1.49  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.22/1.49  tff(f_115, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.22/1.49  tff(f_156, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 3.22/1.49  tff(f_129, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.22/1.49  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 3.22/1.49  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.22/1.49  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.22/1.49  tff(f_58, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.22/1.49  tff(f_52, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.22/1.49  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 3.22/1.49  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.22/1.49  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.49  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.22/1.49  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.22/1.49  tff(c_549, plain, (![A_103, B_104]: (~v2_struct_0(k1_tex_2(A_103, B_104)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.22/1.49  tff(c_556, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_549])).
% 3.22/1.49  tff(c_560, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_556])).
% 3.22/1.49  tff(c_561, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_560])).
% 3.22/1.49  tff(c_526, plain, (![A_99, B_100]: (v1_zfmisc_1(A_99) | k6_domain_1(A_99, B_100)!=A_99 | ~m1_subset_1(B_100, A_99) | v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.49  tff(c_534, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_526])).
% 3.22/1.49  tff(c_589, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_534])).
% 3.22/1.49  tff(c_535, plain, (![A_101, B_102]: (m1_subset_1(k6_domain_1(A_101, B_102), k1_zfmisc_1(A_101)) | ~m1_subset_1(B_102, A_101) | v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.49  tff(c_32, plain, (![B_28, A_27]: (v1_subset_1(B_28, A_27) | B_28=A_27 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.22/1.49  tff(c_654, plain, (![A_124, B_125]: (v1_subset_1(k6_domain_1(A_124, B_125), A_124) | k6_domain_1(A_124, B_125)=A_124 | ~m1_subset_1(B_125, A_124) | v1_xboole_0(A_124))), inference(resolution, [status(thm)], [c_535, c_32])).
% 3.22/1.49  tff(c_62, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.22/1.49  tff(c_73, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.22/1.49  tff(c_353, plain, (![A_83, B_84]: (~v7_struct_0(A_83) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_83), B_84), u1_struct_0(A_83)) | ~m1_subset_1(B_84, u1_struct_0(A_83)) | ~l1_struct_0(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.22/1.49  tff(c_370, plain, (~v7_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_73, c_353])).
% 3.22/1.49  tff(c_380, plain, (~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_370])).
% 3.22/1.49  tff(c_381, plain, (~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_380])).
% 3.22/1.49  tff(c_382, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_381])).
% 3.22/1.49  tff(c_385, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_382])).
% 3.22/1.49  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_385])).
% 3.22/1.49  tff(c_390, plain, (~v7_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_381])).
% 3.22/1.49  tff(c_391, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_381])).
% 3.22/1.49  tff(c_160, plain, (![A_60, B_61]: (m1_pre_topc(k1_tex_2(A_60, B_61), A_60) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.22/1.49  tff(c_165, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_160])).
% 3.22/1.49  tff(c_169, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_165])).
% 3.22/1.49  tff(c_170, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_169])).
% 3.22/1.49  tff(c_288, plain, (![A_71, B_72]: (m1_subset_1('#skF_2'(A_71, B_72), k1_zfmisc_1(u1_struct_0(A_71))) | v1_tex_2(B_72, A_71) | ~m1_pre_topc(B_72, A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.22/1.49  tff(c_450, plain, (![A_91, B_92]: (v1_subset_1('#skF_2'(A_91, B_92), u1_struct_0(A_91)) | u1_struct_0(A_91)='#skF_2'(A_91, B_92) | v1_tex_2(B_92, A_91) | ~m1_pre_topc(B_92, A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_288, c_32])).
% 3.22/1.49  tff(c_26, plain, (![A_17, B_23]: (~v1_subset_1('#skF_2'(A_17, B_23), u1_struct_0(A_17)) | v1_tex_2(B_23, A_17) | ~m1_pre_topc(B_23, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.22/1.49  tff(c_460, plain, (![A_93, B_94]: (u1_struct_0(A_93)='#skF_2'(A_93, B_94) | v1_tex_2(B_94, A_93) | ~m1_pre_topc(B_94, A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_450, c_26])).
% 3.22/1.49  tff(c_56, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.22/1.49  tff(c_138, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56])).
% 3.22/1.49  tff(c_466, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_460, c_138])).
% 3.22/1.49  tff(c_470, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_170, c_466])).
% 3.22/1.49  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.22/1.49  tff(c_173, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_170, c_4])).
% 3.22/1.49  tff(c_176, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_173])).
% 3.22/1.49  tff(c_111, plain, (![A_52, B_53]: (~v2_struct_0(k1_tex_2(A_52, B_53)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.22/1.49  tff(c_118, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_111])).
% 3.22/1.49  tff(c_122, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_118])).
% 3.22/1.49  tff(c_123, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_122])).
% 3.22/1.49  tff(c_153, plain, (![B_58, A_59]: (u1_struct_0(B_58)='#skF_2'(A_59, B_58) | v1_tex_2(B_58, A_59) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.22/1.49  tff(c_156, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_153, c_138])).
% 3.22/1.49  tff(c_159, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_156])).
% 3.22/1.49  tff(c_178, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_159])).
% 3.22/1.49  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.22/1.49  tff(c_196, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_6])).
% 3.22/1.49  tff(c_215, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_123, c_196])).
% 3.22/1.49  tff(c_219, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_215])).
% 3.22/1.49  tff(c_222, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_219])).
% 3.22/1.49  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_222])).
% 3.22/1.49  tff(c_228, plain, (l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_215])).
% 3.22/1.49  tff(c_139, plain, (![A_56, B_57]: (v7_struct_0(k1_tex_2(A_56, B_57)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l1_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.22/1.49  tff(c_146, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_139])).
% 3.22/1.49  tff(c_150, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_146])).
% 3.22/1.49  tff(c_151, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_150])).
% 3.22/1.49  tff(c_10, plain, (![A_7]: (v1_zfmisc_1(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | ~v7_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.49  tff(c_199, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_10])).
% 3.22/1.49  tff(c_217, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_199])).
% 3.22/1.49  tff(c_230, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_217])).
% 3.22/1.49  tff(c_481, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_230])).
% 3.22/1.49  tff(c_8, plain, (![A_6]: (~v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.22/1.49  tff(c_502, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_481, c_8])).
% 3.22/1.49  tff(c_505, plain, (v7_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_391, c_502])).
% 3.22/1.49  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_505])).
% 3.22/1.49  tff(c_509, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 3.22/1.49  tff(c_661, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_654, c_509])).
% 3.22/1.49  tff(c_668, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_661])).
% 3.22/1.49  tff(c_669, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_589, c_668])).
% 3.22/1.49  tff(c_672, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_669, c_6])).
% 3.22/1.49  tff(c_675, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_672])).
% 3.22/1.49  tff(c_678, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_675])).
% 3.22/1.49  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_678])).
% 3.22/1.49  tff(c_683, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_534])).
% 3.22/1.49  tff(c_685, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_683])).
% 3.22/1.49  tff(c_689, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_685, c_8])).
% 3.22/1.49  tff(c_701, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_689])).
% 3.22/1.49  tff(c_704, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_701])).
% 3.22/1.49  tff(c_708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_704])).
% 3.22/1.49  tff(c_709, plain, (v7_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_689])).
% 3.22/1.49  tff(c_690, plain, (![A_126, B_127]: (m1_pre_topc(k1_tex_2(A_126, B_127), A_126) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l1_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.22/1.49  tff(c_695, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_690])).
% 3.22/1.49  tff(c_699, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_695])).
% 3.22/1.49  tff(c_700, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_699])).
% 3.22/1.49  tff(c_508, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 3.22/1.49  tff(c_728, plain, (![B_128, A_129]: (~v1_tex_2(B_128, A_129) | v2_struct_0(B_128) | ~m1_pre_topc(B_128, A_129) | ~l1_pre_topc(A_129) | ~v7_struct_0(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.49  tff(c_734, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_508, c_728])).
% 3.22/1.49  tff(c_738, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_709, c_52, c_700, c_734])).
% 3.22/1.49  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_561, c_738])).
% 3.22/1.49  tff(c_741, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_683])).
% 3.22/1.49  tff(c_745, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_741, c_6])).
% 3.22/1.49  tff(c_748, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_745])).
% 3.22/1.49  tff(c_751, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_748])).
% 3.22/1.49  tff(c_755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_751])).
% 3.22/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  
% 3.22/1.49  Inference rules
% 3.22/1.49  ----------------------
% 3.22/1.49  #Ref     : 0
% 3.22/1.49  #Sup     : 116
% 3.22/1.49  #Fact    : 0
% 3.22/1.49  #Define  : 0
% 3.22/1.49  #Split   : 8
% 3.22/1.49  #Chain   : 0
% 3.22/1.49  #Close   : 0
% 3.22/1.49  
% 3.22/1.49  Ordering : KBO
% 3.22/1.49  
% 3.22/1.49  Simplification rules
% 3.22/1.49  ----------------------
% 3.22/1.49  #Subsume      : 11
% 3.22/1.49  #Demod        : 108
% 3.22/1.49  #Tautology    : 24
% 3.22/1.49  #SimpNegUnit  : 37
% 3.22/1.49  #BackRed      : 14
% 3.22/1.49  
% 3.22/1.49  #Partial instantiations: 0
% 3.22/1.49  #Strategies tried      : 1
% 3.22/1.49  
% 3.22/1.49  Timing (in seconds)
% 3.22/1.49  ----------------------
% 3.22/1.50  Preprocessing        : 0.33
% 3.22/1.50  Parsing              : 0.17
% 3.22/1.50  CNF conversion       : 0.02
% 3.22/1.50  Main loop            : 0.34
% 3.22/1.50  Inferencing          : 0.13
% 3.22/1.50  Reduction            : 0.11
% 3.22/1.50  Demodulation         : 0.07
% 3.22/1.50  BG Simplification    : 0.02
% 3.22/1.50  Subsumption          : 0.05
% 3.22/1.50  Abstraction          : 0.02
% 3.22/1.50  MUC search           : 0.00
% 3.22/1.50  Cooper               : 0.00
% 3.22/1.50  Total                : 0.71
% 3.22/1.50  Index Insertion      : 0.00
% 3.22/1.50  Index Deletion       : 0.00
% 3.22/1.50  Index Matching       : 0.00
% 3.22/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

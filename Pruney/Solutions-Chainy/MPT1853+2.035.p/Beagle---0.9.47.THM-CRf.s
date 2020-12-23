%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:05 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 423 expanded)
%              Number of leaves         :   37 ( 148 expanded)
%              Depth                    :   13
%              Number of atoms          :  329 (1153 expanded)
%              Number of equality atoms :   19 (  48 expanded)
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

tff(f_183,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_157,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_122,axiom,(
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

tff(f_129,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_108,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1424,plain,(
    ! [A_193,B_194] :
      ( m1_pre_topc(k1_tex_2(A_193,B_194),A_193)
      | ~ m1_subset_1(B_194,u1_struct_0(A_193))
      | ~ l1_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1429,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1424])).

tff(c_1433,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1429])).

tff(c_1434,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1433])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( l1_pre_topc(B_8)
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1437,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1434,c_8])).

tff(c_1440,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1437])).

tff(c_1211,plain,(
    ! [A_163,B_164] :
      ( ~ v2_struct_0(k1_tex_2(A_163,B_164))
      | ~ m1_subset_1(B_164,u1_struct_0(A_163))
      | ~ l1_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1218,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1211])).

tff(c_1222,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1218])).

tff(c_1223,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1222])).

tff(c_66,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_77,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_399,plain,(
    ! [A_91,B_92] :
      ( ~ v7_struct_0(A_91)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_91),B_92),u1_struct_0(A_91))
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_struct_0(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_412,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_399])).

tff(c_421,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_412])).

tff(c_422,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_421])).

tff(c_423,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_422])).

tff(c_426,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_423])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_426])).

tff(c_431,plain,(
    ~ v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_422])).

tff(c_432,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_422])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k6_domain_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_199,plain,(
    ! [B_74,A_75] :
      ( ~ v1_subset_1(B_74,A_75)
      | v1_xboole_0(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_zfmisc_1(A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_576,plain,(
    ! [A_112,B_113] :
      ( ~ v1_subset_1(k6_domain_1(A_112,B_113),A_112)
      | v1_xboole_0(k6_domain_1(A_112,B_113))
      | ~ v1_zfmisc_1(A_112)
      | ~ m1_subset_1(B_113,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_16,c_199])).

tff(c_585,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_77,c_576])).

tff(c_589,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_585])).

tff(c_590,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_213,plain,(
    ! [A_76,B_77] :
      ( m1_pre_topc(k1_tex_2(A_76,B_77),A_76)
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_218,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_213])).

tff(c_222,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_218])).

tff(c_223,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_222])).

tff(c_348,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1('#skF_2'(A_86,B_87),k1_zfmisc_1(u1_struct_0(A_86)))
      | v1_tex_2(B_87,A_86)
      | ~ m1_pre_topc(B_87,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    ! [B_35,A_34] :
      ( v1_subset_1(B_35,A_34)
      | B_35 = A_34
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1036,plain,(
    ! [A_142,B_143] :
      ( v1_subset_1('#skF_2'(A_142,B_143),u1_struct_0(A_142))
      | u1_struct_0(A_142) = '#skF_2'(A_142,B_143)
      | v1_tex_2(B_143,A_142)
      | ~ m1_pre_topc(B_143,A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_348,c_36])).

tff(c_30,plain,(
    ! [A_24,B_30] :
      ( ~ v1_subset_1('#skF_2'(A_24,B_30),u1_struct_0(A_24))
      | v1_tex_2(B_30,A_24)
      | ~ m1_pre_topc(B_30,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1059,plain,(
    ! [A_144,B_145] :
      ( u1_struct_0(A_144) = '#skF_2'(A_144,B_145)
      | v1_tex_2(B_145,A_144)
      | ~ m1_pre_topc(B_145,A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_1036,c_30])).

tff(c_60,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_133,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_60])).

tff(c_1072,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1059,c_133])).

tff(c_1080,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_223,c_1072])).

tff(c_226,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_223,c_8])).

tff(c_229,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_226])).

tff(c_152,plain,(
    ! [A_66,B_67] :
      ( v7_struct_0(k1_tex_2(A_66,B_67))
      | ~ m1_subset_1(B_67,u1_struct_0(A_66))
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_159,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_152])).

tff(c_163,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_159])).

tff(c_164,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_163])).

tff(c_192,plain,(
    ! [B_72,A_73] :
      ( u1_struct_0(B_72) = '#skF_2'(A_73,B_72)
      | v1_tex_2(B_72,A_73)
      | ~ m1_pre_topc(B_72,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_195,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_192,c_133])).

tff(c_198,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_195])).

tff(c_239,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_198])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_zfmisc_1(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | ~ v7_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_278,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_14])).

tff(c_311,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_278])).

tff(c_338,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_341,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_338])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_341])).

tff(c_346,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_1104,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_346])).

tff(c_1107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_590,c_1104])).

tff(c_1109,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_12,plain,(
    ! [A_10] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v7_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1112,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1109,c_12])).

tff(c_1115,plain,(
    v7_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_1112])).

tff(c_1117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_431,c_1115])).

tff(c_1118,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1154,plain,(
    ! [A_154,B_155] :
      ( v1_zfmisc_1(A_154)
      | k6_domain_1(A_154,B_155) != A_154
      | ~ m1_subset_1(B_155,A_154)
      | v1_xboole_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1162,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_1154])).

tff(c_1237,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1162])).

tff(c_1182,plain,(
    ! [A_159,B_160] :
      ( m1_subset_1(k6_domain_1(A_159,B_160),k1_zfmisc_1(A_159))
      | ~ m1_subset_1(B_160,A_159)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1341,plain,(
    ! [A_189,B_190] :
      ( v1_subset_1(k6_domain_1(A_189,B_190),A_189)
      | k6_domain_1(A_189,B_190) = A_189
      | ~ m1_subset_1(B_190,A_189)
      | v1_xboole_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_1182,c_36])).

tff(c_1120,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_1122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1118,c_1120])).

tff(c_1123,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1348,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1341,c_1123])).

tff(c_1355,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1348])).

tff(c_1356,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1237,c_1355])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1364,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1356,c_10])).

tff(c_1371,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1364])).

tff(c_1374,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1371])).

tff(c_1378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1374])).

tff(c_1379,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1162])).

tff(c_1381,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1379])).

tff(c_1385,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1381,c_12])).

tff(c_1387,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1385])).

tff(c_1390,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1387])).

tff(c_1394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1390])).

tff(c_1396,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1385])).

tff(c_1380,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1162])).

tff(c_1401,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1380,c_16])).

tff(c_1405,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1401])).

tff(c_1407,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1405])).

tff(c_1413,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1407,c_10])).

tff(c_1419,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_1413])).

tff(c_1421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1419])).

tff(c_1423,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1405])).

tff(c_18,plain,(
    ! [B_16,A_14] :
      ( m1_subset_1(u1_struct_0(B_16),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_pre_topc(B_16,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1586,plain,(
    ! [B_216,A_217] :
      ( v1_subset_1(u1_struct_0(B_216),u1_struct_0(A_217))
      | ~ m1_subset_1(u1_struct_0(B_216),k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ v1_tex_2(B_216,A_217)
      | ~ m1_pre_topc(B_216,A_217)
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1602,plain,(
    ! [B_16,A_14] :
      ( v1_subset_1(u1_struct_0(B_16),u1_struct_0(A_14))
      | ~ v1_tex_2(B_16,A_14)
      | ~ m1_pre_topc(B_16,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_1586])).

tff(c_1461,plain,(
    ! [B_195,A_196] :
      ( ~ v1_subset_1(B_195,A_196)
      | v1_xboole_0(B_195)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_196))
      | ~ v1_zfmisc_1(A_196)
      | v1_xboole_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1672,plain,(
    ! [B_235,A_236] :
      ( ~ v1_subset_1(u1_struct_0(B_235),u1_struct_0(A_236))
      | v1_xboole_0(u1_struct_0(B_235))
      | ~ v1_zfmisc_1(u1_struct_0(A_236))
      | v1_xboole_0(u1_struct_0(A_236))
      | ~ m1_pre_topc(B_235,A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(resolution,[status(thm)],[c_18,c_1461])).

tff(c_1681,plain,(
    ! [B_237,A_238] :
      ( v1_xboole_0(u1_struct_0(B_237))
      | ~ v1_zfmisc_1(u1_struct_0(A_238))
      | v1_xboole_0(u1_struct_0(A_238))
      | ~ v1_tex_2(B_237,A_238)
      | ~ m1_pre_topc(B_237,A_238)
      | ~ l1_pre_topc(A_238) ) ),
    inference(resolution,[status(thm)],[c_1602,c_1672])).

tff(c_1683,plain,(
    ! [B_237] :
      ( v1_xboole_0(u1_struct_0(B_237))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_237,'#skF_3')
      | ~ m1_pre_topc(B_237,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1381,c_1681])).

tff(c_1691,plain,(
    ! [B_237] :
      ( v1_xboole_0(u1_struct_0(B_237))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_237,'#skF_3')
      | ~ m1_pre_topc(B_237,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1683])).

tff(c_1695,plain,(
    ! [B_239] :
      ( v1_xboole_0(u1_struct_0(B_239))
      | ~ v1_tex_2(B_239,'#skF_3')
      | ~ m1_pre_topc(B_239,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1423,c_1691])).

tff(c_1738,plain,(
    ! [B_243] :
      ( ~ l1_struct_0(B_243)
      | v2_struct_0(B_243)
      | ~ v1_tex_2(B_243,'#skF_3')
      | ~ m1_pre_topc(B_243,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1695,c_10])).

tff(c_1745,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1118,c_1738])).

tff(c_1751,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1434,c_1745])).

tff(c_1752,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1223,c_1751])).

tff(c_1755,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1752])).

tff(c_1759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_1755])).

tff(c_1760,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1379])).

tff(c_1777,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1760,c_10])).

tff(c_1781,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1777])).

tff(c_1784,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1781])).

tff(c_1788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:09:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.66  
% 3.87/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.66  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.87/1.66  
% 3.87/1.66  %Foreground sorts:
% 3.87/1.66  
% 3.87/1.66  
% 3.87/1.66  %Background operators:
% 3.87/1.66  
% 3.87/1.66  
% 3.87/1.66  %Foreground operators:
% 3.87/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.66  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.87/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.87/1.66  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.87/1.66  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.87/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.87/1.66  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.87/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.87/1.66  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.87/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.66  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.87/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.87/1.66  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.87/1.66  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.87/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.87/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.87/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.66  
% 4.11/1.70  tff(f_183, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 4.11/1.70  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.11/1.70  tff(f_143, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 4.11/1.70  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.11/1.70  tff(f_157, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 4.11/1.70  tff(f_170, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 4.11/1.70  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.11/1.70  tff(f_98, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 4.11/1.70  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 4.11/1.70  tff(f_129, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.11/1.70  tff(f_70, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 4.11/1.70  tff(f_64, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 4.11/1.70  tff(f_108, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 4.11/1.70  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.11/1.70  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.11/1.70  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.11/1.70  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.70  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.11/1.70  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.11/1.70  tff(c_1424, plain, (![A_193, B_194]: (m1_pre_topc(k1_tex_2(A_193, B_194), A_193) | ~m1_subset_1(B_194, u1_struct_0(A_193)) | ~l1_pre_topc(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.11/1.70  tff(c_1429, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1424])).
% 4.11/1.70  tff(c_1433, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1429])).
% 4.11/1.70  tff(c_1434, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_1433])).
% 4.11/1.70  tff(c_8, plain, (![B_8, A_6]: (l1_pre_topc(B_8) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.11/1.70  tff(c_1437, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1434, c_8])).
% 4.11/1.70  tff(c_1440, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1437])).
% 4.11/1.70  tff(c_1211, plain, (![A_163, B_164]: (~v2_struct_0(k1_tex_2(A_163, B_164)) | ~m1_subset_1(B_164, u1_struct_0(A_163)) | ~l1_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.11/1.70  tff(c_1218, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1211])).
% 4.11/1.70  tff(c_1222, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1218])).
% 4.11/1.70  tff(c_1223, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1222])).
% 4.11/1.70  tff(c_66, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.11/1.70  tff(c_77, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 4.11/1.70  tff(c_399, plain, (![A_91, B_92]: (~v7_struct_0(A_91) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_91), B_92), u1_struct_0(A_91)) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_struct_0(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.11/1.70  tff(c_412, plain, (~v7_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_77, c_399])).
% 4.11/1.70  tff(c_421, plain, (~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_412])).
% 4.11/1.70  tff(c_422, plain, (~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_421])).
% 4.11/1.70  tff(c_423, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_422])).
% 4.11/1.70  tff(c_426, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_423])).
% 4.11/1.70  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_426])).
% 4.11/1.70  tff(c_431, plain, (~v7_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_422])).
% 4.11/1.70  tff(c_432, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_422])).
% 4.11/1.70  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k6_domain_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.11/1.70  tff(c_199, plain, (![B_74, A_75]: (~v1_subset_1(B_74, A_75) | v1_xboole_0(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_zfmisc_1(A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.11/1.70  tff(c_576, plain, (![A_112, B_113]: (~v1_subset_1(k6_domain_1(A_112, B_113), A_112) | v1_xboole_0(k6_domain_1(A_112, B_113)) | ~v1_zfmisc_1(A_112) | ~m1_subset_1(B_113, A_112) | v1_xboole_0(A_112))), inference(resolution, [status(thm)], [c_16, c_199])).
% 4.11/1.70  tff(c_585, plain, (v1_xboole_0(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~v1_zfmisc_1(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_77, c_576])).
% 4.11/1.70  tff(c_589, plain, (v1_xboole_0(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_585])).
% 4.11/1.70  tff(c_590, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_589])).
% 4.11/1.70  tff(c_213, plain, (![A_76, B_77]: (m1_pre_topc(k1_tex_2(A_76, B_77), A_76) | ~m1_subset_1(B_77, u1_struct_0(A_76)) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.11/1.70  tff(c_218, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_213])).
% 4.11/1.70  tff(c_222, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_218])).
% 4.11/1.70  tff(c_223, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_222])).
% 4.11/1.70  tff(c_348, plain, (![A_86, B_87]: (m1_subset_1('#skF_2'(A_86, B_87), k1_zfmisc_1(u1_struct_0(A_86))) | v1_tex_2(B_87, A_86) | ~m1_pre_topc(B_87, A_86) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.70  tff(c_36, plain, (![B_35, A_34]: (v1_subset_1(B_35, A_34) | B_35=A_34 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.11/1.70  tff(c_1036, plain, (![A_142, B_143]: (v1_subset_1('#skF_2'(A_142, B_143), u1_struct_0(A_142)) | u1_struct_0(A_142)='#skF_2'(A_142, B_143) | v1_tex_2(B_143, A_142) | ~m1_pre_topc(B_143, A_142) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_348, c_36])).
% 4.11/1.70  tff(c_30, plain, (![A_24, B_30]: (~v1_subset_1('#skF_2'(A_24, B_30), u1_struct_0(A_24)) | v1_tex_2(B_30, A_24) | ~m1_pre_topc(B_30, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.70  tff(c_1059, plain, (![A_144, B_145]: (u1_struct_0(A_144)='#skF_2'(A_144, B_145) | v1_tex_2(B_145, A_144) | ~m1_pre_topc(B_145, A_144) | ~l1_pre_topc(A_144))), inference(resolution, [status(thm)], [c_1036, c_30])).
% 4.11/1.70  tff(c_60, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.11/1.70  tff(c_133, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_60])).
% 4.11/1.70  tff(c_1072, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1059, c_133])).
% 4.11/1.70  tff(c_1080, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_223, c_1072])).
% 4.11/1.70  tff(c_226, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_223, c_8])).
% 4.11/1.70  tff(c_229, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_226])).
% 4.11/1.70  tff(c_152, plain, (![A_66, B_67]: (v7_struct_0(k1_tex_2(A_66, B_67)) | ~m1_subset_1(B_67, u1_struct_0(A_66)) | ~l1_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.11/1.70  tff(c_159, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_152])).
% 4.11/1.70  tff(c_163, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_159])).
% 4.11/1.70  tff(c_164, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_163])).
% 4.11/1.70  tff(c_192, plain, (![B_72, A_73]: (u1_struct_0(B_72)='#skF_2'(A_73, B_72) | v1_tex_2(B_72, A_73) | ~m1_pre_topc(B_72, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.70  tff(c_195, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_192, c_133])).
% 4.11/1.70  tff(c_198, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_195])).
% 4.11/1.70  tff(c_239, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_198])).
% 4.11/1.70  tff(c_14, plain, (![A_11]: (v1_zfmisc_1(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | ~v7_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.11/1.70  tff(c_278, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_239, c_14])).
% 4.11/1.70  tff(c_311, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_278])).
% 4.11/1.70  tff(c_338, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_311])).
% 4.11/1.70  tff(c_341, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_338])).
% 4.11/1.70  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_341])).
% 4.11/1.70  tff(c_346, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_311])).
% 4.11/1.70  tff(c_1104, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_346])).
% 4.11/1.70  tff(c_1107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_590, c_1104])).
% 4.11/1.70  tff(c_1109, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_589])).
% 4.11/1.70  tff(c_12, plain, (![A_10]: (~v1_zfmisc_1(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v7_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.11/1.70  tff(c_1112, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1109, c_12])).
% 4.11/1.70  tff(c_1115, plain, (v7_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_1112])).
% 4.11/1.70  tff(c_1117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_431, c_1115])).
% 4.11/1.70  tff(c_1118, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 4.11/1.70  tff(c_1154, plain, (![A_154, B_155]: (v1_zfmisc_1(A_154) | k6_domain_1(A_154, B_155)!=A_154 | ~m1_subset_1(B_155, A_154) | v1_xboole_0(A_154))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.11/1.70  tff(c_1162, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_1154])).
% 4.11/1.70  tff(c_1237, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1162])).
% 4.11/1.70  tff(c_1182, plain, (![A_159, B_160]: (m1_subset_1(k6_domain_1(A_159, B_160), k1_zfmisc_1(A_159)) | ~m1_subset_1(B_160, A_159) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.11/1.70  tff(c_1341, plain, (![A_189, B_190]: (v1_subset_1(k6_domain_1(A_189, B_190), A_189) | k6_domain_1(A_189, B_190)=A_189 | ~m1_subset_1(B_190, A_189) | v1_xboole_0(A_189))), inference(resolution, [status(thm)], [c_1182, c_36])).
% 4.11/1.70  tff(c_1120, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 4.11/1.70  tff(c_1122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1118, c_1120])).
% 4.11/1.70  tff(c_1123, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 4.11/1.70  tff(c_1348, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1341, c_1123])).
% 4.11/1.70  tff(c_1355, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1348])).
% 4.11/1.70  tff(c_1356, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1237, c_1355])).
% 4.11/1.70  tff(c_10, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.11/1.70  tff(c_1364, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1356, c_10])).
% 4.11/1.70  tff(c_1371, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_1364])).
% 4.11/1.70  tff(c_1374, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1371])).
% 4.11/1.70  tff(c_1378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1374])).
% 4.11/1.70  tff(c_1379, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1162])).
% 4.11/1.70  tff(c_1381, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1379])).
% 4.11/1.70  tff(c_1385, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1381, c_12])).
% 4.11/1.70  tff(c_1387, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1385])).
% 4.11/1.70  tff(c_1390, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1387])).
% 4.11/1.70  tff(c_1394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1390])).
% 4.11/1.70  tff(c_1396, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1385])).
% 4.11/1.70  tff(c_1380, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1162])).
% 4.11/1.70  tff(c_1401, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1380, c_16])).
% 4.11/1.70  tff(c_1405, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1401])).
% 4.11/1.70  tff(c_1407, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1405])).
% 4.11/1.70  tff(c_1413, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1407, c_10])).
% 4.11/1.70  tff(c_1419, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_1413])).
% 4.11/1.70  tff(c_1421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1419])).
% 4.11/1.70  tff(c_1423, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1405])).
% 4.11/1.70  tff(c_18, plain, (![B_16, A_14]: (m1_subset_1(u1_struct_0(B_16), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_pre_topc(B_16, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.11/1.70  tff(c_1586, plain, (![B_216, A_217]: (v1_subset_1(u1_struct_0(B_216), u1_struct_0(A_217)) | ~m1_subset_1(u1_struct_0(B_216), k1_zfmisc_1(u1_struct_0(A_217))) | ~v1_tex_2(B_216, A_217) | ~m1_pre_topc(B_216, A_217) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.70  tff(c_1602, plain, (![B_16, A_14]: (v1_subset_1(u1_struct_0(B_16), u1_struct_0(A_14)) | ~v1_tex_2(B_16, A_14) | ~m1_pre_topc(B_16, A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_18, c_1586])).
% 4.11/1.70  tff(c_1461, plain, (![B_195, A_196]: (~v1_subset_1(B_195, A_196) | v1_xboole_0(B_195) | ~m1_subset_1(B_195, k1_zfmisc_1(A_196)) | ~v1_zfmisc_1(A_196) | v1_xboole_0(A_196))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.11/1.70  tff(c_1672, plain, (![B_235, A_236]: (~v1_subset_1(u1_struct_0(B_235), u1_struct_0(A_236)) | v1_xboole_0(u1_struct_0(B_235)) | ~v1_zfmisc_1(u1_struct_0(A_236)) | v1_xboole_0(u1_struct_0(A_236)) | ~m1_pre_topc(B_235, A_236) | ~l1_pre_topc(A_236))), inference(resolution, [status(thm)], [c_18, c_1461])).
% 4.11/1.70  tff(c_1681, plain, (![B_237, A_238]: (v1_xboole_0(u1_struct_0(B_237)) | ~v1_zfmisc_1(u1_struct_0(A_238)) | v1_xboole_0(u1_struct_0(A_238)) | ~v1_tex_2(B_237, A_238) | ~m1_pre_topc(B_237, A_238) | ~l1_pre_topc(A_238))), inference(resolution, [status(thm)], [c_1602, c_1672])).
% 4.11/1.70  tff(c_1683, plain, (![B_237]: (v1_xboole_0(u1_struct_0(B_237)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~v1_tex_2(B_237, '#skF_3') | ~m1_pre_topc(B_237, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_1381, c_1681])).
% 4.11/1.70  tff(c_1691, plain, (![B_237]: (v1_xboole_0(u1_struct_0(B_237)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~v1_tex_2(B_237, '#skF_3') | ~m1_pre_topc(B_237, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1683])).
% 4.11/1.70  tff(c_1695, plain, (![B_239]: (v1_xboole_0(u1_struct_0(B_239)) | ~v1_tex_2(B_239, '#skF_3') | ~m1_pre_topc(B_239, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1423, c_1691])).
% 4.11/1.70  tff(c_1738, plain, (![B_243]: (~l1_struct_0(B_243) | v2_struct_0(B_243) | ~v1_tex_2(B_243, '#skF_3') | ~m1_pre_topc(B_243, '#skF_3'))), inference(resolution, [status(thm)], [c_1695, c_10])).
% 4.11/1.70  tff(c_1745, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1118, c_1738])).
% 4.11/1.70  tff(c_1751, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1434, c_1745])).
% 4.11/1.70  tff(c_1752, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1223, c_1751])).
% 4.11/1.70  tff(c_1755, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1752])).
% 4.11/1.70  tff(c_1759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1440, c_1755])).
% 4.11/1.70  tff(c_1760, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1379])).
% 4.11/1.70  tff(c_1777, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1760, c_10])).
% 4.11/1.70  tff(c_1781, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_1777])).
% 4.11/1.70  tff(c_1784, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1781])).
% 4.11/1.70  tff(c_1788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1784])).
% 4.11/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.70  
% 4.11/1.70  Inference rules
% 4.11/1.70  ----------------------
% 4.11/1.70  #Ref     : 0
% 4.11/1.70  #Sup     : 316
% 4.11/1.70  #Fact    : 0
% 4.11/1.70  #Define  : 0
% 4.11/1.70  #Split   : 15
% 4.11/1.70  #Chain   : 0
% 4.11/1.70  #Close   : 0
% 4.11/1.70  
% 4.11/1.70  Ordering : KBO
% 4.11/1.70  
% 4.11/1.70  Simplification rules
% 4.11/1.70  ----------------------
% 4.11/1.70  #Subsume      : 70
% 4.11/1.70  #Demod        : 268
% 4.11/1.70  #Tautology    : 50
% 4.11/1.70  #SimpNegUnit  : 73
% 4.11/1.70  #BackRed      : 27
% 4.11/1.70  
% 4.11/1.70  #Partial instantiations: 0
% 4.11/1.70  #Strategies tried      : 1
% 4.11/1.70  
% 4.11/1.70  Timing (in seconds)
% 4.11/1.70  ----------------------
% 4.11/1.71  Preprocessing        : 0.33
% 4.11/1.71  Parsing              : 0.18
% 4.11/1.71  CNF conversion       : 0.02
% 4.11/1.71  Main loop            : 0.55
% 4.11/1.71  Inferencing          : 0.20
% 4.11/1.71  Reduction            : 0.17
% 4.11/1.71  Demodulation         : 0.12
% 4.11/1.71  BG Simplification    : 0.03
% 4.11/1.71  Subsumption          : 0.10
% 4.11/1.71  Abstraction          : 0.03
% 4.11/1.71  MUC search           : 0.00
% 4.11/1.71  Cooper               : 0.00
% 4.11/1.71  Total                : 0.95
% 4.11/1.71  Index Insertion      : 0.00
% 4.11/1.71  Index Deletion       : 0.00
% 4.11/1.71  Index Matching       : 0.00
% 4.11/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------

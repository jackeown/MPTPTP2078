%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:03 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 197 expanded)
%              Number of leaves         :   33 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  229 ( 529 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) )
           => ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc13_tex_2)).

tff(f_166,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_114,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_337,plain,(
    ! [A_90,B_91] :
      ( m1_pre_topc(k1_tex_2(A_90,B_91),A_90)
      | ~ m1_subset_1(B_91,u1_struct_0(A_90))
      | ~ l1_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_339,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_337])).

tff(c_342,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_339])).

tff(c_343,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_342])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( l1_pre_topc(B_8)
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_346,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_343,c_8])).

tff(c_349,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_346])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_283,plain,(
    ! [A_80,B_81] :
      ( ~ v2_struct_0(k1_tex_2(A_80,B_81))
      | ~ m1_subset_1(B_81,u1_struct_0(A_80))
      | ~ l1_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_286,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_283])).

tff(c_289,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_286])).

tff(c_290,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_289])).

tff(c_68,plain,(
    ! [A_49,B_50] :
      ( ~ v2_struct_0(k1_tex_2(A_49,B_50))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_71,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_74,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_71])).

tff(c_75,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_74])).

tff(c_107,plain,(
    ! [A_61,B_62] :
      ( m1_pre_topc(k1_tex_2(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_109,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_107])).

tff(c_112,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_109])).

tff(c_113,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_112])).

tff(c_87,plain,(
    ! [A_55,B_56] :
      ( v7_struct_0(k1_tex_2(A_55,B_56))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l1_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_90,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_93,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_90])).

tff(c_94,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_93])).

tff(c_217,plain,(
    ! [B_73,A_74] :
      ( ~ v7_struct_0(B_73)
      | v1_tex_2(B_73,A_74)
      | v2_struct_0(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74)
      | v7_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_56,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_67,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_86,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_50])).

tff(c_220,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_217,c_86])).

tff(c_223,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_113,c_94,c_220])).

tff(c_224,plain,(
    v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_75,c_223])).

tff(c_249,plain,(
    ! [A_78,B_79] :
      ( ~ v7_struct_0(A_78)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_78),B_79),u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_struct_0(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_262,plain,
    ( ~ v7_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_249])).

tff(c_272,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_224,c_262])).

tff(c_273,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_272])).

tff(c_276,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_273])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_276])).

tff(c_281,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_293,plain,(
    ! [A_82,B_83] :
      ( v1_subset_1(k6_domain_1(A_82,B_83),A_82)
      | ~ m1_subset_1(B_83,A_82)
      | v1_zfmisc_1(A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_282,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_296,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_293,c_282])).

tff(c_299,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_296])).

tff(c_300,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_303,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_300,c_10])).

tff(c_306,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_303])).

tff(c_309,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_306])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_309])).

tff(c_315,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_314,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_12,plain,(
    ! [B_12,A_10] :
      ( m1_subset_1(u1_struct_0(B_12),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_376,plain,(
    ! [B_106,A_107] :
      ( v1_subset_1(u1_struct_0(B_106),u1_struct_0(A_107))
      | ~ m1_subset_1(u1_struct_0(B_106),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ v1_tex_2(B_106,A_107)
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_380,plain,(
    ! [B_12,A_10] :
      ( v1_subset_1(u1_struct_0(B_12),u1_struct_0(A_10))
      | ~ v1_tex_2(B_12,A_10)
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_376])).

tff(c_332,plain,(
    ! [B_88,A_89] :
      ( ~ v1_subset_1(B_88,A_89)
      | v1_xboole_0(B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89))
      | ~ v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_387,plain,(
    ! [B_112,A_113] :
      ( ~ v1_subset_1(u1_struct_0(B_112),u1_struct_0(A_113))
      | v1_xboole_0(u1_struct_0(B_112))
      | ~ v1_zfmisc_1(u1_struct_0(A_113))
      | v1_xboole_0(u1_struct_0(A_113))
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_12,c_332])).

tff(c_392,plain,(
    ! [B_114,A_115] :
      ( v1_xboole_0(u1_struct_0(B_114))
      | ~ v1_zfmisc_1(u1_struct_0(A_115))
      | v1_xboole_0(u1_struct_0(A_115))
      | ~ v1_tex_2(B_114,A_115)
      | ~ m1_pre_topc(B_114,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_380,c_387])).

tff(c_394,plain,(
    ! [B_114] :
      ( v1_xboole_0(u1_struct_0(B_114))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ v1_tex_2(B_114,'#skF_2')
      | ~ m1_pre_topc(B_114,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_314,c_392])).

tff(c_400,plain,(
    ! [B_114] :
      ( v1_xboole_0(u1_struct_0(B_114))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ v1_tex_2(B_114,'#skF_2')
      | ~ m1_pre_topc(B_114,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_394])).

tff(c_403,plain,(
    ! [B_116] :
      ( v1_xboole_0(u1_struct_0(B_116))
      | ~ v1_tex_2(B_116,'#skF_2')
      | ~ m1_pre_topc(B_116,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_400])).

tff(c_416,plain,(
    ! [B_117] :
      ( ~ l1_struct_0(B_117)
      | v2_struct_0(B_117)
      | ~ v1_tex_2(B_117,'#skF_2')
      | ~ m1_pre_topc(B_117,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_403,c_10])).

tff(c_427,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_281,c_416])).

tff(c_437,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_427])).

tff(c_438,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_437])).

tff(c_441,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_438])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.36  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.60/1.36  
% 2.60/1.36  %Foreground sorts:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Background operators:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Foreground operators:
% 2.60/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.36  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.60/1.36  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.60/1.36  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.60/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.60/1.36  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.60/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.36  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.60/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.36  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.36  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.60/1.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.60/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.60/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.60/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.36  
% 2.60/1.38  tff(f_179, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 2.60/1.38  tff(f_128, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.60/1.38  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.60/1.38  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.60/1.38  tff(f_142, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.60/1.38  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v1_tex_2(B, A)) => (~v2_struct_0(B) & ~v7_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc13_tex_2)).
% 2.60/1.38  tff(f_166, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 2.60/1.38  tff(f_153, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 2.60/1.38  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.60/1.38  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.60/1.38  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 2.60/1.38  tff(f_100, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.60/1.38  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.60/1.38  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.60/1.38  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.60/1.38  tff(c_337, plain, (![A_90, B_91]: (m1_pre_topc(k1_tex_2(A_90, B_91), A_90) | ~m1_subset_1(B_91, u1_struct_0(A_90)) | ~l1_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.60/1.38  tff(c_339, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_337])).
% 2.60/1.38  tff(c_342, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_339])).
% 2.60/1.38  tff(c_343, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_342])).
% 2.60/1.38  tff(c_8, plain, (![B_8, A_6]: (l1_pre_topc(B_8) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.60/1.38  tff(c_346, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_343, c_8])).
% 2.60/1.38  tff(c_349, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_346])).
% 2.60/1.38  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.60/1.38  tff(c_283, plain, (![A_80, B_81]: (~v2_struct_0(k1_tex_2(A_80, B_81)) | ~m1_subset_1(B_81, u1_struct_0(A_80)) | ~l1_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.60/1.38  tff(c_286, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_283])).
% 2.60/1.38  tff(c_289, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_286])).
% 2.60/1.38  tff(c_290, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_289])).
% 2.60/1.38  tff(c_68, plain, (![A_49, B_50]: (~v2_struct_0(k1_tex_2(A_49, B_50)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.60/1.38  tff(c_71, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_68])).
% 2.60/1.38  tff(c_74, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_71])).
% 2.60/1.38  tff(c_75, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_74])).
% 2.60/1.38  tff(c_107, plain, (![A_61, B_62]: (m1_pre_topc(k1_tex_2(A_61, B_62), A_61) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.60/1.38  tff(c_109, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_107])).
% 2.60/1.38  tff(c_112, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_109])).
% 2.60/1.38  tff(c_113, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_112])).
% 2.60/1.38  tff(c_87, plain, (![A_55, B_56]: (v7_struct_0(k1_tex_2(A_55, B_56)) | ~m1_subset_1(B_56, u1_struct_0(A_55)) | ~l1_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.60/1.38  tff(c_90, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_87])).
% 2.60/1.38  tff(c_93, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_90])).
% 2.60/1.38  tff(c_94, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_93])).
% 2.60/1.38  tff(c_217, plain, (![B_73, A_74]: (~v7_struct_0(B_73) | v1_tex_2(B_73, A_74) | v2_struct_0(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74) | v7_struct_0(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.60/1.38  tff(c_56, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.60/1.38  tff(c_67, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.60/1.38  tff(c_50, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.60/1.38  tff(c_86, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_50])).
% 2.60/1.38  tff(c_220, plain, (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_217, c_86])).
% 2.60/1.38  tff(c_223, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_113, c_94, c_220])).
% 2.60/1.38  tff(c_224, plain, (v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_75, c_223])).
% 2.60/1.38  tff(c_249, plain, (![A_78, B_79]: (~v7_struct_0(A_78) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_78), B_79), u1_struct_0(A_78)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_struct_0(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.60/1.38  tff(c_262, plain, (~v7_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_67, c_249])).
% 2.60/1.38  tff(c_272, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_224, c_262])).
% 2.60/1.38  tff(c_273, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_272])).
% 2.60/1.38  tff(c_276, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_273])).
% 2.60/1.38  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_276])).
% 2.60/1.38  tff(c_281, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 2.60/1.38  tff(c_293, plain, (![A_82, B_83]: (v1_subset_1(k6_domain_1(A_82, B_83), A_82) | ~m1_subset_1(B_83, A_82) | v1_zfmisc_1(A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.60/1.38  tff(c_282, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 2.60/1.38  tff(c_296, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_293, c_282])).
% 2.60/1.38  tff(c_299, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_296])).
% 2.60/1.38  tff(c_300, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_299])).
% 2.60/1.38  tff(c_10, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.38  tff(c_303, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_300, c_10])).
% 2.60/1.38  tff(c_306, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_303])).
% 2.60/1.38  tff(c_309, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_306])).
% 2.60/1.38  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_309])).
% 2.60/1.38  tff(c_315, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_299])).
% 2.60/1.38  tff(c_314, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_299])).
% 2.60/1.38  tff(c_12, plain, (![B_12, A_10]: (m1_subset_1(u1_struct_0(B_12), k1_zfmisc_1(u1_struct_0(A_10))) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.60/1.38  tff(c_376, plain, (![B_106, A_107]: (v1_subset_1(u1_struct_0(B_106), u1_struct_0(A_107)) | ~m1_subset_1(u1_struct_0(B_106), k1_zfmisc_1(u1_struct_0(A_107))) | ~v1_tex_2(B_106, A_107) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.60/1.38  tff(c_380, plain, (![B_12, A_10]: (v1_subset_1(u1_struct_0(B_12), u1_struct_0(A_10)) | ~v1_tex_2(B_12, A_10) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10))), inference(resolution, [status(thm)], [c_12, c_376])).
% 2.60/1.38  tff(c_332, plain, (![B_88, A_89]: (~v1_subset_1(B_88, A_89) | v1_xboole_0(B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)) | ~v1_zfmisc_1(A_89) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.60/1.38  tff(c_387, plain, (![B_112, A_113]: (~v1_subset_1(u1_struct_0(B_112), u1_struct_0(A_113)) | v1_xboole_0(u1_struct_0(B_112)) | ~v1_zfmisc_1(u1_struct_0(A_113)) | v1_xboole_0(u1_struct_0(A_113)) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_12, c_332])).
% 2.60/1.38  tff(c_392, plain, (![B_114, A_115]: (v1_xboole_0(u1_struct_0(B_114)) | ~v1_zfmisc_1(u1_struct_0(A_115)) | v1_xboole_0(u1_struct_0(A_115)) | ~v1_tex_2(B_114, A_115) | ~m1_pre_topc(B_114, A_115) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_380, c_387])).
% 2.60/1.38  tff(c_394, plain, (![B_114]: (v1_xboole_0(u1_struct_0(B_114)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v1_tex_2(B_114, '#skF_2') | ~m1_pre_topc(B_114, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_314, c_392])).
% 2.60/1.38  tff(c_400, plain, (![B_114]: (v1_xboole_0(u1_struct_0(B_114)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v1_tex_2(B_114, '#skF_2') | ~m1_pre_topc(B_114, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_394])).
% 2.60/1.38  tff(c_403, plain, (![B_116]: (v1_xboole_0(u1_struct_0(B_116)) | ~v1_tex_2(B_116, '#skF_2') | ~m1_pre_topc(B_116, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_315, c_400])).
% 2.60/1.38  tff(c_416, plain, (![B_117]: (~l1_struct_0(B_117) | v2_struct_0(B_117) | ~v1_tex_2(B_117, '#skF_2') | ~m1_pre_topc(B_117, '#skF_2'))), inference(resolution, [status(thm)], [c_403, c_10])).
% 2.60/1.38  tff(c_427, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_281, c_416])).
% 2.60/1.38  tff(c_437, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_427])).
% 2.60/1.38  tff(c_438, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_290, c_437])).
% 2.60/1.38  tff(c_441, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_438])).
% 2.60/1.38  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_349, c_441])).
% 2.60/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  
% 2.60/1.38  Inference rules
% 2.60/1.38  ----------------------
% 2.60/1.38  #Ref     : 0
% 2.60/1.38  #Sup     : 62
% 2.60/1.38  #Fact    : 0
% 2.60/1.38  #Define  : 0
% 2.60/1.38  #Split   : 4
% 2.60/1.38  #Chain   : 0
% 2.60/1.38  #Close   : 0
% 2.60/1.38  
% 2.60/1.38  Ordering : KBO
% 2.60/1.38  
% 2.60/1.38  Simplification rules
% 2.60/1.38  ----------------------
% 2.60/1.38  #Subsume      : 10
% 2.60/1.38  #Demod        : 48
% 2.60/1.38  #Tautology    : 6
% 2.60/1.38  #SimpNegUnit  : 24
% 2.60/1.38  #BackRed      : 0
% 2.60/1.38  
% 2.60/1.38  #Partial instantiations: 0
% 2.60/1.38  #Strategies tried      : 1
% 2.60/1.38  
% 2.60/1.38  Timing (in seconds)
% 2.60/1.38  ----------------------
% 2.60/1.38  Preprocessing        : 0.34
% 2.60/1.38  Parsing              : 0.18
% 2.60/1.38  CNF conversion       : 0.02
% 2.60/1.38  Main loop            : 0.27
% 2.60/1.38  Inferencing          : 0.10
% 2.60/1.38  Reduction            : 0.08
% 2.60/1.38  Demodulation         : 0.06
% 2.60/1.38  BG Simplification    : 0.02
% 2.60/1.39  Subsumption          : 0.05
% 2.60/1.39  Abstraction          : 0.01
% 2.60/1.39  MUC search           : 0.00
% 2.60/1.39  Cooper               : 0.00
% 2.60/1.39  Total                : 0.66
% 2.60/1.39  Index Insertion      : 0.00
% 2.60/1.39  Index Deletion       : 0.00
% 2.60/1.39  Index Matching       : 0.00
% 2.60/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:05 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 348 expanded)
%              Number of leaves         :   35 ( 125 expanded)
%              Depth                    :   14
%              Number of atoms          :  283 ( 948 expanded)
%              Number of equality atoms :   15 (  36 expanded)
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

tff(f_177,negated_conjecture,(
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

tff(f_153,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_97,axiom,(
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

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ~ ( u1_struct_0(B) = u1_struct_0(A)
              & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_54,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_67,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_95,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_60])).

tff(c_44,plain,(
    ! [A_36,B_38] :
      ( ~ v1_zfmisc_1(A_36)
      | ~ v1_subset_1(k6_domain_1(A_36,B_38),A_36)
      | ~ m1_subset_1(B_38,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_98,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_95,c_44])).

tff(c_101,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_98])).

tff(c_102,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_149,plain,(
    ! [A_73,B_74] :
      ( m1_pre_topc(k1_tex_2(A_73,B_74),A_73)
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_151,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_149])).

tff(c_154,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_151])).

tff(c_155,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_154])).

tff(c_272,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1('#skF_1'(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | v1_tex_2(B_84,A_83)
      | ~ m1_pre_topc(B_84,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ! [B_28,A_27] :
      ( v1_subset_1(B_28,A_27)
      | B_28 = A_27
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_496,plain,(
    ! [A_117,B_118] :
      ( v1_subset_1('#skF_1'(A_117,B_118),u1_struct_0(A_117))
      | u1_struct_0(A_117) = '#skF_1'(A_117,B_118)
      | v1_tex_2(B_118,A_117)
      | ~ m1_pre_topc(B_118,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_272,c_26])).

tff(c_20,plain,(
    ! [A_17,B_23] :
      ( ~ v1_subset_1('#skF_1'(A_17,B_23),u1_struct_0(A_17))
      | v1_tex_2(B_23,A_17)
      | ~ m1_pre_topc(B_23,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_514,plain,(
    ! [A_119,B_120] :
      ( u1_struct_0(A_119) = '#skF_1'(A_119,B_120)
      | v1_tex_2(B_120,A_119)
      | ~ m1_pre_topc(B_120,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_496,c_20])).

tff(c_530,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_514,c_67])).

tff(c_539,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_155,c_530])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( l1_pre_topc(B_8)
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_158,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_155,c_8])).

tff(c_161,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_158])).

tff(c_86,plain,(
    ! [A_59,B_60] :
      ( ~ v2_struct_0(k1_tex_2(A_59,B_60))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_89,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_86])).

tff(c_92,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_89])).

tff(c_93,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_92])).

tff(c_138,plain,(
    ! [B_71,A_72] :
      ( u1_struct_0(B_71) = '#skF_1'(A_72,B_71)
      | v1_tex_2(B_71,A_72)
      | ~ m1_pre_topc(B_71,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_144,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_138,c_67])).

tff(c_148,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_144])).

tff(c_183,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_148])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_225,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_10])).

tff(c_256,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_225])).

tff(c_260,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_263,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_263])).

tff(c_269,plain,(
    l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_120,plain,(
    ! [A_65,B_66] :
      ( v7_struct_0(k1_tex_2(A_65,B_66))
      | ~ m1_subset_1(B_66,u1_struct_0(A_65))
      | ~ l1_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_123,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_120])).

tff(c_126,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_123])).

tff(c_127,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_126])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_zfmisc_1(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | ~ v7_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_228,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_12])).

tff(c_258,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_228])).

tff(c_271,plain,(
    v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_258])).

tff(c_552,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_271])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_552])).

tff(c_557,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_561,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_557,c_10])).

tff(c_564,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_561])).

tff(c_567,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_564])).

tff(c_571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_567])).

tff(c_573,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_592,plain,(
    ! [B_130,A_131] :
      ( ~ v1_tex_2(B_130,A_131)
      | u1_struct_0(B_130) != u1_struct_0(A_131)
      | ~ m1_pre_topc(B_130,A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_595,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) != u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_573,c_592])).

tff(c_598,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) != u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_595])).

tff(c_599,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_598])).

tff(c_663,plain,(
    ! [A_144,B_145] :
      ( m1_pre_topc(k1_tex_2(A_144,B_145),A_144)
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l1_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_665,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_663])).

tff(c_668,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_665])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_599,c_668])).

tff(c_672,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_598])).

tff(c_675,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_672,c_8])).

tff(c_678,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_675])).

tff(c_732,plain,(
    ! [A_154,B_155] :
      ( ~ v2_struct_0(k1_tex_2(A_154,B_155))
      | ~ m1_subset_1(B_155,u1_struct_0(A_154))
      | ~ l1_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_735,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_732])).

tff(c_738,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_735])).

tff(c_739,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_738])).

tff(c_689,plain,(
    ! [A_148,B_149] :
      ( v1_subset_1(k6_domain_1(A_148,B_149),A_148)
      | ~ m1_subset_1(B_149,A_148)
      | v1_zfmisc_1(A_148)
      | v1_xboole_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_572,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_695,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_689,c_572])).

tff(c_699,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_695])).

tff(c_700,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_699])).

tff(c_703,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_700,c_10])).

tff(c_706,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_703])).

tff(c_717,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_706])).

tff(c_721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_717])).

tff(c_723,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_699])).

tff(c_722,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_699])).

tff(c_14,plain,(
    ! [B_13,A_11] :
      ( m1_subset_1(u1_struct_0(B_13),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_791,plain,(
    ! [B_174,A_175] :
      ( v1_subset_1(u1_struct_0(B_174),u1_struct_0(A_175))
      | ~ m1_subset_1(u1_struct_0(B_174),k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ v1_tex_2(B_174,A_175)
      | ~ m1_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_795,plain,(
    ! [B_13,A_11] :
      ( v1_subset_1(u1_struct_0(B_13),u1_struct_0(A_11))
      | ~ v1_tex_2(B_13,A_11)
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_791])).

tff(c_752,plain,(
    ! [B_160,A_161] :
      ( ~ v1_subset_1(B_160,A_161)
      | v1_xboole_0(B_160)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_161))
      | ~ v1_zfmisc_1(A_161)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_836,plain,(
    ! [B_188,A_189] :
      ( ~ v1_subset_1(u1_struct_0(B_188),u1_struct_0(A_189))
      | v1_xboole_0(u1_struct_0(B_188))
      | ~ v1_zfmisc_1(u1_struct_0(A_189))
      | v1_xboole_0(u1_struct_0(A_189))
      | ~ m1_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189) ) ),
    inference(resolution,[status(thm)],[c_14,c_752])).

tff(c_845,plain,(
    ! [B_190,A_191] :
      ( v1_xboole_0(u1_struct_0(B_190))
      | ~ v1_zfmisc_1(u1_struct_0(A_191))
      | v1_xboole_0(u1_struct_0(A_191))
      | ~ v1_tex_2(B_190,A_191)
      | ~ m1_pre_topc(B_190,A_191)
      | ~ l1_pre_topc(A_191) ) ),
    inference(resolution,[status(thm)],[c_795,c_836])).

tff(c_847,plain,(
    ! [B_190] :
      ( v1_xboole_0(u1_struct_0(B_190))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ v1_tex_2(B_190,'#skF_2')
      | ~ m1_pre_topc(B_190,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_722,c_845])).

tff(c_855,plain,(
    ! [B_190] :
      ( v1_xboole_0(u1_struct_0(B_190))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ v1_tex_2(B_190,'#skF_2')
      | ~ m1_pre_topc(B_190,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_847])).

tff(c_859,plain,(
    ! [B_192] :
      ( v1_xboole_0(u1_struct_0(B_192))
      | ~ v1_tex_2(B_192,'#skF_2')
      | ~ m1_pre_topc(B_192,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_723,c_855])).

tff(c_904,plain,(
    ! [B_196] :
      ( ~ l1_struct_0(B_196)
      | v2_struct_0(B_196)
      | ~ v1_tex_2(B_196,'#skF_2')
      | ~ m1_pre_topc(B_196,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_859,c_10])).

tff(c_915,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_573,c_904])).

tff(c_924,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_915])).

tff(c_925,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_739,c_924])).

tff(c_928,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_925])).

tff(c_932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_928])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.51  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.51  
% 3.23/1.51  %Foreground sorts:
% 3.23/1.51  
% 3.23/1.51  
% 3.23/1.51  %Background operators:
% 3.23/1.51  
% 3.23/1.51  
% 3.23/1.51  %Foreground operators:
% 3.23/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.23/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.51  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.23/1.51  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.23/1.51  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.23/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.23/1.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.23/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.51  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.23/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.23/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.51  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.23/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.51  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.23/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.23/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.51  
% 3.23/1.53  tff(f_177, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 3.23/1.53  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.23/1.53  tff(f_153, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.23/1.53  tff(f_118, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.23/1.53  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 3.23/1.53  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.23/1.53  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.23/1.53  tff(f_132, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.23/1.53  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.23/1.53  tff(f_62, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.23/1.53  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 3.23/1.53  tff(f_164, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 3.23/1.53  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.23/1.53  tff(f_83, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.23/1.53  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.23/1.53  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.23/1.53  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.53  tff(c_48, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.23/1.53  tff(c_54, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.23/1.53  tff(c_67, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 3.23/1.53  tff(c_60, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.23/1.53  tff(c_95, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_67, c_60])).
% 3.23/1.53  tff(c_44, plain, (![A_36, B_38]: (~v1_zfmisc_1(A_36) | ~v1_subset_1(k6_domain_1(A_36, B_38), A_36) | ~m1_subset_1(B_38, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.53  tff(c_98, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_95, c_44])).
% 3.23/1.53  tff(c_101, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_98])).
% 3.23/1.53  tff(c_102, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_101])).
% 3.23/1.53  tff(c_149, plain, (![A_73, B_74]: (m1_pre_topc(k1_tex_2(A_73, B_74), A_73) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.23/1.53  tff(c_151, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_149])).
% 3.23/1.53  tff(c_154, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_151])).
% 3.23/1.53  tff(c_155, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_154])).
% 3.23/1.53  tff(c_272, plain, (![A_83, B_84]: (m1_subset_1('#skF_1'(A_83, B_84), k1_zfmisc_1(u1_struct_0(A_83))) | v1_tex_2(B_84, A_83) | ~m1_pre_topc(B_84, A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.53  tff(c_26, plain, (![B_28, A_27]: (v1_subset_1(B_28, A_27) | B_28=A_27 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.23/1.53  tff(c_496, plain, (![A_117, B_118]: (v1_subset_1('#skF_1'(A_117, B_118), u1_struct_0(A_117)) | u1_struct_0(A_117)='#skF_1'(A_117, B_118) | v1_tex_2(B_118, A_117) | ~m1_pre_topc(B_118, A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_272, c_26])).
% 3.23/1.53  tff(c_20, plain, (![A_17, B_23]: (~v1_subset_1('#skF_1'(A_17, B_23), u1_struct_0(A_17)) | v1_tex_2(B_23, A_17) | ~m1_pre_topc(B_23, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.53  tff(c_514, plain, (![A_119, B_120]: (u1_struct_0(A_119)='#skF_1'(A_119, B_120) | v1_tex_2(B_120, A_119) | ~m1_pre_topc(B_120, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_496, c_20])).
% 3.23/1.53  tff(c_530, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_514, c_67])).
% 3.23/1.53  tff(c_539, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_155, c_530])).
% 3.23/1.53  tff(c_8, plain, (![B_8, A_6]: (l1_pre_topc(B_8) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.53  tff(c_158, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_155, c_8])).
% 3.23/1.53  tff(c_161, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_158])).
% 3.23/1.53  tff(c_86, plain, (![A_59, B_60]: (~v2_struct_0(k1_tex_2(A_59, B_60)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.23/1.53  tff(c_89, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_86])).
% 3.23/1.53  tff(c_92, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_89])).
% 3.23/1.53  tff(c_93, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_92])).
% 3.23/1.53  tff(c_138, plain, (![B_71, A_72]: (u1_struct_0(B_71)='#skF_1'(A_72, B_71) | v1_tex_2(B_71, A_72) | ~m1_pre_topc(B_71, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.53  tff(c_144, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_138, c_67])).
% 3.23/1.53  tff(c_148, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_144])).
% 3.23/1.53  tff(c_183, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_148])).
% 3.23/1.53  tff(c_10, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.23/1.53  tff(c_225, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_10])).
% 3.23/1.53  tff(c_256, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_93, c_225])).
% 3.23/1.53  tff(c_260, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_256])).
% 3.23/1.53  tff(c_263, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_260])).
% 3.23/1.53  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_263])).
% 3.23/1.53  tff(c_269, plain, (l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_256])).
% 3.23/1.53  tff(c_120, plain, (![A_65, B_66]: (v7_struct_0(k1_tex_2(A_65, B_66)) | ~m1_subset_1(B_66, u1_struct_0(A_65)) | ~l1_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.23/1.53  tff(c_123, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_120])).
% 3.23/1.53  tff(c_126, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_123])).
% 3.23/1.53  tff(c_127, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_126])).
% 3.23/1.53  tff(c_12, plain, (![A_10]: (v1_zfmisc_1(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | ~v7_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.23/1.53  tff(c_228, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_12])).
% 3.23/1.53  tff(c_258, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_228])).
% 3.23/1.53  tff(c_271, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_258])).
% 3.23/1.53  tff(c_552, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_271])).
% 3.23/1.53  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_552])).
% 3.23/1.53  tff(c_557, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_101])).
% 3.23/1.53  tff(c_561, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_557, c_10])).
% 3.23/1.53  tff(c_564, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_561])).
% 3.23/1.53  tff(c_567, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_564])).
% 3.23/1.53  tff(c_571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_567])).
% 3.23/1.53  tff(c_573, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 3.23/1.53  tff(c_592, plain, (![B_130, A_131]: (~v1_tex_2(B_130, A_131) | u1_struct_0(B_130)!=u1_struct_0(A_131) | ~m1_pre_topc(B_130, A_131) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.23/1.53  tff(c_595, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_573, c_592])).
% 3.23/1.53  tff(c_598, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_595])).
% 3.23/1.53  tff(c_599, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_598])).
% 3.23/1.53  tff(c_663, plain, (![A_144, B_145]: (m1_pre_topc(k1_tex_2(A_144, B_145), A_144) | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l1_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.23/1.53  tff(c_665, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_663])).
% 3.23/1.53  tff(c_668, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_665])).
% 3.23/1.53  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_599, c_668])).
% 3.23/1.53  tff(c_672, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_598])).
% 3.23/1.53  tff(c_675, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_672, c_8])).
% 3.23/1.53  tff(c_678, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_675])).
% 3.23/1.53  tff(c_732, plain, (![A_154, B_155]: (~v2_struct_0(k1_tex_2(A_154, B_155)) | ~m1_subset_1(B_155, u1_struct_0(A_154)) | ~l1_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.23/1.53  tff(c_735, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_732])).
% 3.23/1.53  tff(c_738, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_735])).
% 3.23/1.53  tff(c_739, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_738])).
% 3.23/1.53  tff(c_689, plain, (![A_148, B_149]: (v1_subset_1(k6_domain_1(A_148, B_149), A_148) | ~m1_subset_1(B_149, A_148) | v1_zfmisc_1(A_148) | v1_xboole_0(A_148))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.23/1.53  tff(c_572, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 3.23/1.53  tff(c_695, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_689, c_572])).
% 3.23/1.53  tff(c_699, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_695])).
% 3.23/1.53  tff(c_700, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_699])).
% 3.23/1.53  tff(c_703, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_700, c_10])).
% 3.23/1.53  tff(c_706, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_703])).
% 3.23/1.53  tff(c_717, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_706])).
% 3.23/1.53  tff(c_721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_717])).
% 3.23/1.53  tff(c_723, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_699])).
% 3.23/1.53  tff(c_722, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_699])).
% 3.23/1.53  tff(c_14, plain, (![B_13, A_11]: (m1_subset_1(u1_struct_0(B_13), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.23/1.53  tff(c_791, plain, (![B_174, A_175]: (v1_subset_1(u1_struct_0(B_174), u1_struct_0(A_175)) | ~m1_subset_1(u1_struct_0(B_174), k1_zfmisc_1(u1_struct_0(A_175))) | ~v1_tex_2(B_174, A_175) | ~m1_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.53  tff(c_795, plain, (![B_13, A_11]: (v1_subset_1(u1_struct_0(B_13), u1_struct_0(A_11)) | ~v1_tex_2(B_13, A_11) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_14, c_791])).
% 3.23/1.53  tff(c_752, plain, (![B_160, A_161]: (~v1_subset_1(B_160, A_161) | v1_xboole_0(B_160) | ~m1_subset_1(B_160, k1_zfmisc_1(A_161)) | ~v1_zfmisc_1(A_161) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.53  tff(c_836, plain, (![B_188, A_189]: (~v1_subset_1(u1_struct_0(B_188), u1_struct_0(A_189)) | v1_xboole_0(u1_struct_0(B_188)) | ~v1_zfmisc_1(u1_struct_0(A_189)) | v1_xboole_0(u1_struct_0(A_189)) | ~m1_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189))), inference(resolution, [status(thm)], [c_14, c_752])).
% 3.23/1.53  tff(c_845, plain, (![B_190, A_191]: (v1_xboole_0(u1_struct_0(B_190)) | ~v1_zfmisc_1(u1_struct_0(A_191)) | v1_xboole_0(u1_struct_0(A_191)) | ~v1_tex_2(B_190, A_191) | ~m1_pre_topc(B_190, A_191) | ~l1_pre_topc(A_191))), inference(resolution, [status(thm)], [c_795, c_836])).
% 3.23/1.53  tff(c_847, plain, (![B_190]: (v1_xboole_0(u1_struct_0(B_190)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v1_tex_2(B_190, '#skF_2') | ~m1_pre_topc(B_190, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_722, c_845])).
% 3.23/1.53  tff(c_855, plain, (![B_190]: (v1_xboole_0(u1_struct_0(B_190)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v1_tex_2(B_190, '#skF_2') | ~m1_pre_topc(B_190, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_847])).
% 3.23/1.53  tff(c_859, plain, (![B_192]: (v1_xboole_0(u1_struct_0(B_192)) | ~v1_tex_2(B_192, '#skF_2') | ~m1_pre_topc(B_192, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_723, c_855])).
% 3.23/1.53  tff(c_904, plain, (![B_196]: (~l1_struct_0(B_196) | v2_struct_0(B_196) | ~v1_tex_2(B_196, '#skF_2') | ~m1_pre_topc(B_196, '#skF_2'))), inference(resolution, [status(thm)], [c_859, c_10])).
% 3.23/1.53  tff(c_915, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_573, c_904])).
% 3.23/1.53  tff(c_924, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_672, c_915])).
% 3.23/1.53  tff(c_925, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_739, c_924])).
% 3.23/1.53  tff(c_928, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_925])).
% 3.23/1.53  tff(c_932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_678, c_928])).
% 3.23/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.53  
% 3.23/1.53  Inference rules
% 3.23/1.53  ----------------------
% 3.23/1.53  #Ref     : 0
% 3.23/1.53  #Sup     : 151
% 3.23/1.53  #Fact    : 0
% 3.23/1.53  #Define  : 0
% 3.23/1.53  #Split   : 9
% 3.23/1.53  #Chain   : 0
% 3.23/1.53  #Close   : 0
% 3.23/1.53  
% 3.23/1.53  Ordering : KBO
% 3.23/1.53  
% 3.23/1.53  Simplification rules
% 3.23/1.53  ----------------------
% 3.23/1.53  #Subsume      : 28
% 3.23/1.53  #Demod        : 108
% 3.23/1.53  #Tautology    : 13
% 3.23/1.53  #SimpNegUnit  : 36
% 3.23/1.53  #BackRed      : 15
% 3.23/1.53  
% 3.23/1.53  #Partial instantiations: 0
% 3.23/1.53  #Strategies tried      : 1
% 3.23/1.53  
% 3.23/1.53  Timing (in seconds)
% 3.23/1.53  ----------------------
% 3.23/1.53  Preprocessing        : 0.34
% 3.23/1.53  Parsing              : 0.18
% 3.23/1.53  CNF conversion       : 0.02
% 3.23/1.53  Main loop            : 0.41
% 3.23/1.53  Inferencing          : 0.15
% 3.23/1.53  Reduction            : 0.12
% 3.23/1.53  Demodulation         : 0.08
% 3.23/1.53  BG Simplification    : 0.02
% 3.23/1.53  Subsumption          : 0.08
% 3.23/1.53  Abstraction          : 0.02
% 3.23/1.53  MUC search           : 0.00
% 3.23/1.53  Cooper               : 0.00
% 3.23/1.53  Total                : 0.79
% 3.23/1.53  Index Insertion      : 0.00
% 3.23/1.53  Index Deletion       : 0.00
% 3.23/1.53  Index Matching       : 0.00
% 3.23/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

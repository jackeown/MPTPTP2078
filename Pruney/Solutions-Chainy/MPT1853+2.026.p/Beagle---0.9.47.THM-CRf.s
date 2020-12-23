%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:03 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 331 expanded)
%              Number of leaves         :   29 ( 124 expanded)
%              Depth                    :   11
%              Number of atoms          :  204 ( 980 expanded)
%              Number of equality atoms :    7 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_83,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_62,axiom,(
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

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_399,plain,(
    ! [A_81,B_82] :
      ( ~ v2_struct_0(k1_tex_2(A_81,B_82))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_402,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_399])).

tff(c_405,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_402])).

tff(c_406,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_405])).

tff(c_415,plain,(
    ! [A_85,B_86] :
      ( m1_pre_topc(k1_tex_2(A_85,B_86),A_85)
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l1_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_417,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_415])).

tff(c_420,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_417])).

tff(c_421,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_420])).

tff(c_42,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_64,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_89,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48])).

tff(c_90,plain,(
    ! [A_46,B_47] :
      ( m1_pre_topc(k1_tex_2(A_46,B_47),A_46)
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_92,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_95,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_92])).

tff(c_96,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_95])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_99,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_96,c_4])).

tff(c_102,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_99])).

tff(c_81,plain,(
    ! [A_44,B_45] :
      ( ~ v2_struct_0(k1_tex_2(A_44,B_45))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_84,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_87,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_84])).

tff(c_88,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_87])).

tff(c_53,plain,(
    ! [B_37,A_38] :
      ( m1_subset_1(u1_struct_0(B_37),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( v1_subset_1(B_12,A_11)
      | B_12 = A_11
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_61,plain,(
    ! [B_37,A_38] :
      ( v1_subset_1(u1_struct_0(B_37),u1_struct_0(A_38))
      | u1_struct_0(B_37) = u1_struct_0(A_38)
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_53,c_12])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( m1_subset_1(u1_struct_0(B_7),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    ! [B_58,A_59] :
      ( v1_tex_2(B_58,A_59)
      | ~ v1_subset_1(u1_struct_0(B_58),u1_struct_0(A_59))
      | ~ m1_subset_1(u1_struct_0(B_58),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_144,plain,(
    ! [B_60,A_61] :
      ( v1_tex_2(B_60,A_61)
      | ~ v1_subset_1(u1_struct_0(B_60),u1_struct_0(A_61))
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_139])).

tff(c_149,plain,(
    ! [B_62,A_63] :
      ( v1_tex_2(B_62,A_63)
      | u1_struct_0(B_62) = u1_struct_0(A_63)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_61,c_144])).

tff(c_155,plain,
    ( u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_149,c_64])).

tff(c_159,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_96,c_155])).

tff(c_73,plain,(
    ! [A_42,B_43] :
      ( v7_struct_0(k1_tex_2(A_42,B_43))
      | ~ m1_subset_1(B_43,u1_struct_0(A_42))
      | ~ l1_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_76,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_79,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_76])).

tff(c_80,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_79])).

tff(c_32,plain,(
    ! [A_24,B_26] :
      ( ~ v7_struct_0(A_24)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_24),B_26),u1_struct_0(A_24))
      | ~ m1_subset_1(B_26,u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_178,plain,(
    ! [B_26] :
      ( ~ v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),B_26),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_26,u1_struct_0(k1_tex_2('#skF_1','#skF_2')))
      | ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_32])).

tff(c_220,plain,(
    ! [B_26] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),B_26),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_26,u1_struct_0('#skF_1'))
      | ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_80,c_178])).

tff(c_221,plain,(
    ! [B_26] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),B_26),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_26,u1_struct_0('#skF_1'))
      | ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_220])).

tff(c_332,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_335,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_332])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_335])).

tff(c_371,plain,(
    ! [B_78] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),B_78),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_378,plain,(
    ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_89,c_371])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_378])).

tff(c_388,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_428,plain,(
    ! [B_87,A_88] :
      ( ~ v1_tex_2(B_87,A_88)
      | v2_struct_0(B_87)
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v7_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_431,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_388,c_428])).

tff(c_434,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_421,c_431])).

tff(c_435,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_406,c_434])).

tff(c_444,plain,(
    ! [A_93,B_94] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(A_93),B_94),u1_struct_0(A_93))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_struct_0(A_93)
      | v7_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_387,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_450,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_444,c_387])).

tff(c_454,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_450])).

tff(c_455,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_435,c_454])).

tff(c_458,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_455])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.40  
% 2.62/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.40  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.62/1.40  
% 2.62/1.40  %Foreground sorts:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Background operators:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Foreground operators:
% 2.62/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.40  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.62/1.40  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.62/1.40  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.62/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.62/1.40  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.62/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.40  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.62/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.40  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.62/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.62/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.40  
% 2.62/1.42  tff(f_150, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 2.62/1.42  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.62/1.42  tff(f_97, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.62/1.42  tff(f_83, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.62/1.42  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.62/1.42  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.62/1.42  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.62/1.42  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 2.62/1.42  tff(f_124, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 2.62/1.42  tff(f_62, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.62/1.42  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tex_2)).
% 2.62/1.42  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.62/1.42  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.42  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.62/1.42  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.62/1.42  tff(c_399, plain, (![A_81, B_82]: (~v2_struct_0(k1_tex_2(A_81, B_82)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.62/1.42  tff(c_402, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_399])).
% 2.62/1.42  tff(c_405, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_402])).
% 2.62/1.42  tff(c_406, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_405])).
% 2.62/1.42  tff(c_415, plain, (![A_85, B_86]: (m1_pre_topc(k1_tex_2(A_85, B_86), A_85) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l1_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.42  tff(c_417, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_415])).
% 2.62/1.42  tff(c_420, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_417])).
% 2.62/1.42  tff(c_421, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_420])).
% 2.62/1.42  tff(c_42, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.62/1.42  tff(c_64, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 2.62/1.42  tff(c_48, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.62/1.42  tff(c_89, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_48])).
% 2.62/1.42  tff(c_90, plain, (![A_46, B_47]: (m1_pre_topc(k1_tex_2(A_46, B_47), A_46) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.42  tff(c_92, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_90])).
% 2.62/1.42  tff(c_95, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_92])).
% 2.62/1.42  tff(c_96, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_95])).
% 2.62/1.42  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.62/1.42  tff(c_99, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_96, c_4])).
% 2.62/1.42  tff(c_102, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_99])).
% 2.62/1.42  tff(c_81, plain, (![A_44, B_45]: (~v2_struct_0(k1_tex_2(A_44, B_45)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.62/1.42  tff(c_84, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_81])).
% 2.62/1.42  tff(c_87, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_84])).
% 2.62/1.42  tff(c_88, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_87])).
% 2.62/1.42  tff(c_53, plain, (![B_37, A_38]: (m1_subset_1(u1_struct_0(B_37), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.42  tff(c_12, plain, (![B_12, A_11]: (v1_subset_1(B_12, A_11) | B_12=A_11 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.62/1.42  tff(c_61, plain, (![B_37, A_38]: (v1_subset_1(u1_struct_0(B_37), u1_struct_0(A_38)) | u1_struct_0(B_37)=u1_struct_0(A_38) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_53, c_12])).
% 2.62/1.42  tff(c_6, plain, (![B_7, A_5]: (m1_subset_1(u1_struct_0(B_7), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.42  tff(c_139, plain, (![B_58, A_59]: (v1_tex_2(B_58, A_59) | ~v1_subset_1(u1_struct_0(B_58), u1_struct_0(A_59)) | ~m1_subset_1(u1_struct_0(B_58), k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.62/1.42  tff(c_144, plain, (![B_60, A_61]: (v1_tex_2(B_60, A_61) | ~v1_subset_1(u1_struct_0(B_60), u1_struct_0(A_61)) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_6, c_139])).
% 2.62/1.42  tff(c_149, plain, (![B_62, A_63]: (v1_tex_2(B_62, A_63) | u1_struct_0(B_62)=u1_struct_0(A_63) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_61, c_144])).
% 2.62/1.42  tff(c_155, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_149, c_64])).
% 2.62/1.42  tff(c_159, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_96, c_155])).
% 2.62/1.42  tff(c_73, plain, (![A_42, B_43]: (v7_struct_0(k1_tex_2(A_42, B_43)) | ~m1_subset_1(B_43, u1_struct_0(A_42)) | ~l1_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.62/1.42  tff(c_76, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_73])).
% 2.62/1.42  tff(c_79, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_76])).
% 2.62/1.42  tff(c_80, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_79])).
% 2.62/1.42  tff(c_32, plain, (![A_24, B_26]: (~v7_struct_0(A_24) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_24), B_26), u1_struct_0(A_24)) | ~m1_subset_1(B_26, u1_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.62/1.42  tff(c_178, plain, (![B_26]: (~v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), B_26), u1_struct_0('#skF_1')) | ~m1_subset_1(B_26, u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))) | ~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_159, c_32])).
% 2.62/1.42  tff(c_220, plain, (![B_26]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), B_26), u1_struct_0('#skF_1')) | ~m1_subset_1(B_26, u1_struct_0('#skF_1')) | ~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_80, c_178])).
% 2.62/1.42  tff(c_221, plain, (![B_26]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), B_26), u1_struct_0('#skF_1')) | ~m1_subset_1(B_26, u1_struct_0('#skF_1')) | ~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_88, c_220])).
% 2.62/1.42  tff(c_332, plain, (~l1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_221])).
% 2.62/1.42  tff(c_335, plain, (~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2, c_332])).
% 2.62/1.42  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_335])).
% 2.62/1.42  tff(c_371, plain, (![B_78]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), B_78), u1_struct_0('#skF_1')) | ~m1_subset_1(B_78, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_221])).
% 2.62/1.42  tff(c_378, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_89, c_371])).
% 2.62/1.42  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_378])).
% 2.62/1.42  tff(c_388, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 2.62/1.42  tff(c_428, plain, (![B_87, A_88]: (~v1_tex_2(B_87, A_88) | v2_struct_0(B_87) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88) | ~v7_struct_0(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.62/1.42  tff(c_431, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_388, c_428])).
% 2.62/1.42  tff(c_434, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_421, c_431])).
% 2.62/1.42  tff(c_435, plain, (~v7_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_406, c_434])).
% 2.62/1.42  tff(c_444, plain, (![A_93, B_94]: (v1_subset_1(k6_domain_1(u1_struct_0(A_93), B_94), u1_struct_0(A_93)) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_struct_0(A_93) | v7_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.62/1.42  tff(c_387, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_42])).
% 2.62/1.42  tff(c_450, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_444, c_387])).
% 2.62/1.42  tff(c_454, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_450])).
% 2.62/1.42  tff(c_455, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_435, c_454])).
% 2.62/1.42  tff(c_458, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_455])).
% 2.62/1.42  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_458])).
% 2.62/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.42  
% 2.62/1.42  Inference rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Ref     : 0
% 2.62/1.42  #Sup     : 67
% 2.62/1.42  #Fact    : 0
% 2.62/1.42  #Define  : 0
% 2.62/1.42  #Split   : 6
% 2.62/1.42  #Chain   : 0
% 2.62/1.42  #Close   : 0
% 2.62/1.42  
% 2.62/1.42  Ordering : KBO
% 2.62/1.42  
% 2.62/1.42  Simplification rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Subsume      : 7
% 2.62/1.42  #Demod        : 63
% 2.62/1.42  #Tautology    : 16
% 2.62/1.42  #SimpNegUnit  : 24
% 2.62/1.42  #BackRed      : 0
% 2.62/1.42  
% 2.62/1.42  #Partial instantiations: 0
% 2.62/1.42  #Strategies tried      : 1
% 2.62/1.42  
% 2.62/1.42  Timing (in seconds)
% 2.62/1.42  ----------------------
% 2.62/1.42  Preprocessing        : 0.32
% 2.62/1.42  Parsing              : 0.18
% 2.62/1.42  CNF conversion       : 0.02
% 2.62/1.42  Main loop            : 0.29
% 2.62/1.42  Inferencing          : 0.11
% 2.62/1.42  Reduction            : 0.08
% 2.62/1.42  Demodulation         : 0.05
% 2.62/1.42  BG Simplification    : 0.02
% 2.62/1.43  Subsumption          : 0.05
% 2.62/1.43  Abstraction          : 0.01
% 2.62/1.43  MUC search           : 0.00
% 2.62/1.43  Cooper               : 0.00
% 2.62/1.43  Total                : 0.65
% 2.62/1.43  Index Insertion      : 0.00
% 2.62/1.43  Index Deletion       : 0.00
% 2.62/1.43  Index Matching       : 0.00
% 2.62/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

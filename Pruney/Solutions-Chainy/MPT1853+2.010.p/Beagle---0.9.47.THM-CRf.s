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
% DateTime   : Thu Dec  3 10:29:01 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 349 expanded)
%              Number of leaves         :   36 ( 127 expanded)
%              Depth                    :   13
%              Number of atoms          :  276 ( 946 expanded)
%              Number of equality atoms :   18 (  39 expanded)
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

tff(f_165,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_33,axiom,(
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
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_104,axiom,(
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

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_80,axiom,(
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

tff(f_90,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_595,plain,(
    ! [A_115,B_116] :
      ( ~ v2_struct_0(k1_tex_2(A_115,B_116))
      | ~ m1_subset_1(B_116,u1_struct_0(A_115))
      | ~ l1_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_602,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_595])).

tff(c_606,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_602])).

tff(c_607,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_606])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_610,plain,(
    ! [A_119,B_120] :
      ( m1_pre_topc(k1_tex_2(A_119,B_120),A_119)
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_615,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_610])).

tff(c_619,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_615])).

tff(c_620,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_619])).

tff(c_62,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_77,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_305,plain,(
    ! [A_77,B_78] :
      ( ~ v7_struct_0(A_77)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_77),B_78),u1_struct_0(A_77))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_322,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_305])).

tff(c_332,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_322])).

tff(c_333,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_332])).

tff(c_334,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_337,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_334])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_337])).

tff(c_342,plain,(
    ~ v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_343,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_165,plain,(
    ! [A_61,B_62] :
      ( m1_pre_topc(k1_tex_2(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_170,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_165])).

tff(c_174,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_170])).

tff(c_175,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_174])).

tff(c_208,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1('#skF_2'(A_70,B_71),k1_zfmisc_1(u1_struct_0(A_70)))
      | v1_tex_2(B_71,A_70)
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    ! [B_28,A_27] :
      ( v1_subset_1(B_28,A_27)
      | B_28 = A_27
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_466,plain,(
    ! [A_96,B_97] :
      ( v1_subset_1('#skF_2'(A_96,B_97),u1_struct_0(A_96))
      | u1_struct_0(A_96) = '#skF_2'(A_96,B_97)
      | v1_tex_2(B_97,A_96)
      | ~ m1_pre_topc(B_97,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_208,c_32])).

tff(c_26,plain,(
    ! [A_17,B_23] :
      ( ~ v1_subset_1('#skF_2'(A_17,B_23),u1_struct_0(A_17))
      | v1_tex_2(B_23,A_17)
      | ~ m1_pre_topc(B_23,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_476,plain,(
    ! [A_98,B_99] :
      ( u1_struct_0(A_98) = '#skF_2'(A_98,B_99)
      | v1_tex_2(B_99,A_98)
      | ~ m1_pre_topc(B_99,A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_466,c_26])).

tff(c_56,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_130,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_56])).

tff(c_482,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_476,c_130])).

tff(c_486,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_175,c_482])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( l1_pre_topc(B_5)
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_178,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_6])).

tff(c_181,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_178])).

tff(c_131,plain,(
    ! [A_55,B_56] :
      ( v7_struct_0(k1_tex_2(A_55,B_56))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l1_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_138,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_131])).

tff(c_142,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_138])).

tff(c_143,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_142])).

tff(c_158,plain,(
    ! [B_59,A_60] :
      ( u1_struct_0(B_59) = '#skF_2'(A_60,B_59)
      | v1_tex_2(B_59,A_60)
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_161,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_130])).

tff(c_164,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_161])).

tff(c_222,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_164])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_zfmisc_1(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | ~ v7_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_246,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_10])).

tff(c_270,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_246])).

tff(c_273,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_282,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_273])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_282])).

tff(c_287,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_494,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_287])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_521,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_494,c_8])).

tff(c_524,plain,(
    v7_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_521])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_524])).

tff(c_527,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_627,plain,(
    ! [B_121,A_122] :
      ( ~ v1_tex_2(B_121,A_122)
      | v2_struct_0(B_121)
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v7_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_633,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_527,c_627])).

tff(c_637,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_620,c_633])).

tff(c_638,plain,(
    ~ v7_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_607,c_637])).

tff(c_556,plain,(
    ! [A_109,B_110] :
      ( v1_zfmisc_1(A_109)
      | k6_domain_1(A_109,B_110) != A_109
      | ~ m1_subset_1(B_110,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_568,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_556])).

tff(c_608,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_568])).

tff(c_548,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k6_domain_1(A_107,B_108),k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_108,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_640,plain,(
    ! [A_125,B_126] :
      ( v1_subset_1(k6_domain_1(A_125,B_126),A_125)
      | k6_domain_1(A_125,B_126) = A_125
      | ~ m1_subset_1(B_126,A_125)
      | v1_xboole_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_548,c_32])).

tff(c_528,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_643,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_640,c_528])).

tff(c_649,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_643])).

tff(c_650,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_608,c_649])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [A_42] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_42))
      | ~ l1_struct_0(A_42)
      | v7_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    ! [A_42] :
      ( ~ l1_struct_0(A_42)
      | v7_struct_0(A_42)
      | ~ v1_xboole_0(u1_struct_0(A_42)) ) ),
    inference(resolution,[status(thm)],[c_2,c_67])).

tff(c_653,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_650,c_71])).

tff(c_656,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_638,c_653])).

tff(c_659,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_656])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_659])).

tff(c_664,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_666,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_671,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_666,c_8])).

tff(c_672,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_671])).

tff(c_675,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_672])).

tff(c_679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_675])).

tff(c_680,plain,(
    v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_671])).

tff(c_699,plain,(
    ! [A_129,B_130] :
      ( m1_pre_topc(k1_tex_2(A_129,B_130),A_129)
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_704,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_699])).

tff(c_708,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_704])).

tff(c_709,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_708])).

tff(c_717,plain,(
    ! [B_133,A_134] :
      ( ~ v1_tex_2(B_133,A_134)
      | v2_struct_0(B_133)
      | ~ m1_pre_topc(B_133,A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v7_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_723,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_527,c_717])).

tff(c_727,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_52,c_709,c_723])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_607,c_727])).

tff(c_730,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_731,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_741,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_731])).

tff(c_746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.51  
% 3.15/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.51  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.15/1.51  
% 3.15/1.51  %Foreground sorts:
% 3.15/1.51  
% 3.15/1.51  
% 3.15/1.51  %Background operators:
% 3.15/1.51  
% 3.15/1.51  
% 3.15/1.51  %Foreground operators:
% 3.15/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.15/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.51  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.15/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.15/1.51  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.15/1.51  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.15/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.15/1.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.15/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.51  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.15/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.15/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.51  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.15/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.51  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.15/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.15/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.15/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.51  
% 3.39/1.54  tff(f_165, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 3.39/1.54  tff(f_139, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.39/1.54  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.39/1.54  tff(f_125, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.39/1.54  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 3.39/1.54  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 3.39/1.54  tff(f_111, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.39/1.54  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.39/1.54  tff(f_54, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.39/1.54  tff(f_48, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.39/1.54  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 3.39/1.54  tff(f_90, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.39/1.54  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.39/1.54  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 3.39/1.54  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.39/1.54  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.39/1.54  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.39/1.54  tff(c_595, plain, (![A_115, B_116]: (~v2_struct_0(k1_tex_2(A_115, B_116)) | ~m1_subset_1(B_116, u1_struct_0(A_115)) | ~l1_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.39/1.54  tff(c_602, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_595])).
% 3.39/1.54  tff(c_606, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_602])).
% 3.39/1.54  tff(c_607, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_606])).
% 3.39/1.54  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.54  tff(c_610, plain, (![A_119, B_120]: (m1_pre_topc(k1_tex_2(A_119, B_120), A_119) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.39/1.54  tff(c_615, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_610])).
% 3.39/1.54  tff(c_619, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_615])).
% 3.39/1.54  tff(c_620, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_619])).
% 3.39/1.54  tff(c_62, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.39/1.54  tff(c_77, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.39/1.54  tff(c_305, plain, (![A_77, B_78]: (~v7_struct_0(A_77) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_77), B_78), u1_struct_0(A_77)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.39/1.54  tff(c_322, plain, (~v7_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_77, c_305])).
% 3.39/1.54  tff(c_332, plain, (~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_322])).
% 3.39/1.54  tff(c_333, plain, (~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_332])).
% 3.39/1.54  tff(c_334, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_333])).
% 3.39/1.54  tff(c_337, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_334])).
% 3.39/1.54  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_337])).
% 3.39/1.54  tff(c_342, plain, (~v7_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_333])).
% 3.39/1.54  tff(c_343, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_333])).
% 3.39/1.54  tff(c_165, plain, (![A_61, B_62]: (m1_pre_topc(k1_tex_2(A_61, B_62), A_61) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.39/1.54  tff(c_170, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_165])).
% 3.39/1.54  tff(c_174, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_170])).
% 3.39/1.54  tff(c_175, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_174])).
% 3.39/1.54  tff(c_208, plain, (![A_70, B_71]: (m1_subset_1('#skF_2'(A_70, B_71), k1_zfmisc_1(u1_struct_0(A_70))) | v1_tex_2(B_71, A_70) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.39/1.54  tff(c_32, plain, (![B_28, A_27]: (v1_subset_1(B_28, A_27) | B_28=A_27 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.39/1.54  tff(c_466, plain, (![A_96, B_97]: (v1_subset_1('#skF_2'(A_96, B_97), u1_struct_0(A_96)) | u1_struct_0(A_96)='#skF_2'(A_96, B_97) | v1_tex_2(B_97, A_96) | ~m1_pre_topc(B_97, A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_208, c_32])).
% 3.39/1.54  tff(c_26, plain, (![A_17, B_23]: (~v1_subset_1('#skF_2'(A_17, B_23), u1_struct_0(A_17)) | v1_tex_2(B_23, A_17) | ~m1_pre_topc(B_23, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.39/1.54  tff(c_476, plain, (![A_98, B_99]: (u1_struct_0(A_98)='#skF_2'(A_98, B_99) | v1_tex_2(B_99, A_98) | ~m1_pre_topc(B_99, A_98) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_466, c_26])).
% 3.39/1.54  tff(c_56, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.39/1.54  tff(c_130, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_56])).
% 3.39/1.54  tff(c_482, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_476, c_130])).
% 3.39/1.54  tff(c_486, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_175, c_482])).
% 3.39/1.54  tff(c_6, plain, (![B_5, A_3]: (l1_pre_topc(B_5) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.39/1.54  tff(c_178, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_175, c_6])).
% 3.39/1.54  tff(c_181, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_178])).
% 3.39/1.54  tff(c_131, plain, (![A_55, B_56]: (v7_struct_0(k1_tex_2(A_55, B_56)) | ~m1_subset_1(B_56, u1_struct_0(A_55)) | ~l1_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.39/1.54  tff(c_138, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_131])).
% 3.39/1.54  tff(c_142, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_138])).
% 3.39/1.54  tff(c_143, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_142])).
% 3.39/1.54  tff(c_158, plain, (![B_59, A_60]: (u1_struct_0(B_59)='#skF_2'(A_60, B_59) | v1_tex_2(B_59, A_60) | ~m1_pre_topc(B_59, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.39/1.54  tff(c_161, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_158, c_130])).
% 3.39/1.54  tff(c_164, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_161])).
% 3.39/1.54  tff(c_222, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_164])).
% 3.39/1.54  tff(c_10, plain, (![A_7]: (v1_zfmisc_1(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | ~v7_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.54  tff(c_246, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_10])).
% 3.39/1.54  tff(c_270, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_246])).
% 3.39/1.54  tff(c_273, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_270])).
% 3.39/1.54  tff(c_282, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_273])).
% 3.39/1.54  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_282])).
% 3.39/1.54  tff(c_287, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_270])).
% 3.39/1.54  tff(c_494, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_287])).
% 3.39/1.54  tff(c_8, plain, (![A_6]: (~v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.39/1.54  tff(c_521, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_494, c_8])).
% 3.39/1.54  tff(c_524, plain, (v7_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_521])).
% 3.39/1.54  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_524])).
% 3.39/1.54  tff(c_527, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 3.39/1.54  tff(c_627, plain, (![B_121, A_122]: (~v1_tex_2(B_121, A_122) | v2_struct_0(B_121) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122) | ~v7_struct_0(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.54  tff(c_633, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_527, c_627])).
% 3.39/1.54  tff(c_637, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_620, c_633])).
% 3.39/1.54  tff(c_638, plain, (~v7_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_607, c_637])).
% 3.39/1.54  tff(c_556, plain, (![A_109, B_110]: (v1_zfmisc_1(A_109) | k6_domain_1(A_109, B_110)!=A_109 | ~m1_subset_1(B_110, A_109) | v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.39/1.54  tff(c_568, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_556])).
% 3.39/1.54  tff(c_608, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_568])).
% 3.39/1.54  tff(c_548, plain, (![A_107, B_108]: (m1_subset_1(k6_domain_1(A_107, B_108), k1_zfmisc_1(A_107)) | ~m1_subset_1(B_108, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.54  tff(c_640, plain, (![A_125, B_126]: (v1_subset_1(k6_domain_1(A_125, B_126), A_125) | k6_domain_1(A_125, B_126)=A_125 | ~m1_subset_1(B_126, A_125) | v1_xboole_0(A_125))), inference(resolution, [status(thm)], [c_548, c_32])).
% 3.39/1.54  tff(c_528, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 3.39/1.54  tff(c_643, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_640, c_528])).
% 3.39/1.54  tff(c_649, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_643])).
% 3.39/1.54  tff(c_650, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_608, c_649])).
% 3.39/1.54  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.54  tff(c_67, plain, (![A_42]: (~v1_zfmisc_1(u1_struct_0(A_42)) | ~l1_struct_0(A_42) | v7_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.39/1.54  tff(c_71, plain, (![A_42]: (~l1_struct_0(A_42) | v7_struct_0(A_42) | ~v1_xboole_0(u1_struct_0(A_42)))), inference(resolution, [status(thm)], [c_2, c_67])).
% 3.39/1.54  tff(c_653, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_650, c_71])).
% 3.39/1.54  tff(c_656, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_638, c_653])).
% 3.39/1.54  tff(c_659, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_656])).
% 3.39/1.54  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_659])).
% 3.39/1.54  tff(c_664, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_568])).
% 3.39/1.54  tff(c_666, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_664])).
% 3.39/1.54  tff(c_671, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_666, c_8])).
% 3.39/1.54  tff(c_672, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_671])).
% 3.39/1.54  tff(c_675, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_672])).
% 3.39/1.54  tff(c_679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_675])).
% 3.39/1.54  tff(c_680, plain, (v7_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_671])).
% 3.39/1.54  tff(c_699, plain, (![A_129, B_130]: (m1_pre_topc(k1_tex_2(A_129, B_130), A_129) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l1_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.39/1.54  tff(c_704, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_699])).
% 3.39/1.54  tff(c_708, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_704])).
% 3.39/1.54  tff(c_709, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_708])).
% 3.39/1.54  tff(c_717, plain, (![B_133, A_134]: (~v1_tex_2(B_133, A_134) | v2_struct_0(B_133) | ~m1_pre_topc(B_133, A_134) | ~l1_pre_topc(A_134) | ~v7_struct_0(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.54  tff(c_723, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_527, c_717])).
% 3.39/1.54  tff(c_727, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_680, c_52, c_709, c_723])).
% 3.39/1.54  tff(c_729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_607, c_727])).
% 3.39/1.54  tff(c_730, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_664])).
% 3.39/1.54  tff(c_731, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_664])).
% 3.39/1.54  tff(c_741, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2, c_731])).
% 3.39/1.54  tff(c_746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_730, c_741])).
% 3.39/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.54  
% 3.39/1.54  Inference rules
% 3.39/1.54  ----------------------
% 3.39/1.54  #Ref     : 0
% 3.39/1.54  #Sup     : 114
% 3.39/1.54  #Fact    : 0
% 3.39/1.54  #Define  : 0
% 3.39/1.54  #Split   : 9
% 3.39/1.54  #Chain   : 0
% 3.39/1.54  #Close   : 0
% 3.39/1.54  
% 3.39/1.54  Ordering : KBO
% 3.39/1.54  
% 3.39/1.54  Simplification rules
% 3.39/1.54  ----------------------
% 3.39/1.54  #Subsume      : 10
% 3.39/1.54  #Demod        : 114
% 3.39/1.54  #Tautology    : 30
% 3.39/1.54  #SimpNegUnit  : 31
% 3.39/1.54  #BackRed      : 10
% 3.39/1.54  
% 3.39/1.54  #Partial instantiations: 0
% 3.39/1.54  #Strategies tried      : 1
% 3.39/1.54  
% 3.39/1.54  Timing (in seconds)
% 3.39/1.54  ----------------------
% 3.39/1.54  Preprocessing        : 0.36
% 3.39/1.54  Parsing              : 0.19
% 3.39/1.54  CNF conversion       : 0.03
% 3.39/1.54  Main loop            : 0.35
% 3.39/1.54  Inferencing          : 0.13
% 3.39/1.54  Reduction            : 0.11
% 3.39/1.54  Demodulation         : 0.07
% 3.39/1.54  BG Simplification    : 0.02
% 3.39/1.54  Subsumption          : 0.06
% 3.39/1.54  Abstraction          : 0.02
% 3.39/1.54  MUC search           : 0.00
% 3.39/1.54  Cooper               : 0.00
% 3.39/1.54  Total                : 0.76
% 3.39/1.54  Index Insertion      : 0.00
% 3.39/1.54  Index Deletion       : 0.00
% 3.39/1.54  Index Matching       : 0.00
% 3.39/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

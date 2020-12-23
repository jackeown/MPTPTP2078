%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:02 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 338 expanded)
%              Number of leaves         :   36 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  256 ( 898 expanded)
%              Number of equality atoms :   17 (  38 expanded)
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

tff(f_167,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_29,axiom,(
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
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_94,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_154,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_763,plain,(
    ! [A_134,B_135] :
      ( ~ v2_struct_0(k1_tex_2(A_134,B_135))
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_770,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_763])).

tff(c_774,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_770])).

tff(c_775,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_774])).

tff(c_601,plain,(
    ! [A_109,B_110] :
      ( v1_zfmisc_1(A_109)
      | k6_domain_1(A_109,B_110) != A_109
      | ~ m1_subset_1(B_110,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_613,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_601])).

tff(c_631,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_593,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k6_domain_1(A_107,B_108),k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_108,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [B_28,A_27] :
      ( v1_subset_1(B_28,A_27)
      | B_28 = A_27
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_718,plain,(
    ! [A_132,B_133] :
      ( v1_subset_1(k6_domain_1(A_132,B_133),A_132)
      | k6_domain_1(A_132,B_133) = A_132
      | ~ m1_subset_1(B_133,A_132)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_593,c_32])).

tff(c_62,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_73,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_124,plain,(
    ! [A_54,B_55] :
      ( ~ v1_zfmisc_1(A_54)
      | ~ v1_subset_1(k6_domain_1(A_54,B_55),A_54)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_130,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_73,c_124])).

tff(c_133,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_130])).

tff(c_136,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_170,plain,(
    ! [A_60,B_61] :
      ( m1_pre_topc(k1_tex_2(A_60,B_61),A_60)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_175,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_170])).

tff(c_179,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_175])).

tff(c_180,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_179])).

tff(c_343,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1('#skF_2'(A_80,B_81),k1_zfmisc_1(u1_struct_0(A_80)))
      | v1_tex_2(B_81,A_80)
      | ~ m1_pre_topc(B_81,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_497,plain,(
    ! [A_97,B_98] :
      ( v1_subset_1('#skF_2'(A_97,B_98),u1_struct_0(A_97))
      | u1_struct_0(A_97) = '#skF_2'(A_97,B_98)
      | v1_tex_2(B_98,A_97)
      | ~ m1_pre_topc(B_98,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_343,c_32])).

tff(c_26,plain,(
    ! [A_17,B_23] :
      ( ~ v1_subset_1('#skF_2'(A_17,B_23),u1_struct_0(A_17))
      | v1_tex_2(B_23,A_17)
      | ~ m1_pre_topc(B_23,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_517,plain,(
    ! [A_99,B_100] :
      ( u1_struct_0(A_99) = '#skF_2'(A_99,B_100)
      | v1_tex_2(B_100,A_99)
      | ~ m1_pre_topc(B_100,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_497,c_26])).

tff(c_56,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_135,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56])).

tff(c_523,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_517,c_135])).

tff(c_527,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_180,c_523])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_183,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_186,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_183])).

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

tff(c_187,plain,(
    ! [B_62,A_63] :
      ( u1_struct_0(B_62) = '#skF_2'(A_63,B_62)
      | v1_tex_2(B_62,A_63)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_190,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_135])).

tff(c_193,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_180,c_190])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_211,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_6])).

tff(c_230,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_211])).

tff(c_239,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_242,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_239])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_242])).

tff(c_248,plain,(
    l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_155,plain,(
    ! [A_58,B_59] :
      ( v7_struct_0(k1_tex_2(A_58,B_59))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_162,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_155])).

tff(c_166,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_162])).

tff(c_167,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_166])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_zfmisc_1(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | ~ v7_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_214,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_10])).

tff(c_232,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_214])).

tff(c_256,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_232])).

tff(c_539,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_256])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_539])).

tff(c_545,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_562,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_545,c_6])).

tff(c_565,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_562])).

tff(c_568,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_565])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_568])).

tff(c_573,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_576,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_56])).

tff(c_724,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_718,c_576])).

tff(c_731,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_724])).

tff(c_732,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_731])).

tff(c_735,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_732,c_6])).

tff(c_738,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_735])).

tff(c_741,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_738])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_741])).

tff(c_746,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_748,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_746])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_752,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_748,c_8])).

tff(c_753,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_756,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_753])).

tff(c_760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_756])).

tff(c_761,plain,(
    v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_830,plain,(
    ! [A_138,B_139] :
      ( m1_pre_topc(k1_tex_2(A_138,B_139),A_138)
      | ~ m1_subset_1(B_139,u1_struct_0(A_138))
      | ~ l1_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_835,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_830])).

tff(c_839,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_835])).

tff(c_840,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_839])).

tff(c_850,plain,(
    ! [B_144,A_145] :
      ( ~ v1_tex_2(B_144,A_145)
      | v2_struct_0(B_144)
      | ~ m1_pre_topc(B_144,A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v7_struct_0(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_856,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_573,c_850])).

tff(c_860,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_52,c_840,c_856])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_775,c_860])).

tff(c_863,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_746])).

tff(c_867,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_863,c_6])).

tff(c_870,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_867])).

tff(c_886,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_870])).

tff(c_890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.44  
% 2.99/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.44  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.99/1.44  
% 2.99/1.44  %Foreground sorts:
% 2.99/1.44  
% 2.99/1.44  
% 2.99/1.44  %Background operators:
% 2.99/1.44  
% 2.99/1.44  
% 2.99/1.44  %Foreground operators:
% 2.99/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.99/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.44  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.99/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.99/1.44  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.99/1.44  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.99/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.99/1.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.99/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.44  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.99/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.99/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.44  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.99/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.44  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.99/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.99/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.99/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.44  
% 2.99/1.46  tff(f_167, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.99/1.46  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.99/1.46  tff(f_143, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.99/1.46  tff(f_94, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.99/1.46  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.99/1.46  tff(f_115, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.99/1.46  tff(f_154, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.99/1.46  tff(f_129, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.99/1.46  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.99/1.46  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.99/1.46  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.99/1.46  tff(f_58, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.99/1.46  tff(f_52, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.99/1.46  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.99/1.46  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.99/1.46  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.46  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.99/1.46  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.99/1.46  tff(c_763, plain, (![A_134, B_135]: (~v2_struct_0(k1_tex_2(A_134, B_135)) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.99/1.46  tff(c_770, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_763])).
% 2.99/1.46  tff(c_774, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_770])).
% 2.99/1.46  tff(c_775, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_774])).
% 2.99/1.46  tff(c_601, plain, (![A_109, B_110]: (v1_zfmisc_1(A_109) | k6_domain_1(A_109, B_110)!=A_109 | ~m1_subset_1(B_110, A_109) | v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.99/1.46  tff(c_613, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_601])).
% 2.99/1.46  tff(c_631, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_613])).
% 2.99/1.46  tff(c_593, plain, (![A_107, B_108]: (m1_subset_1(k6_domain_1(A_107, B_108), k1_zfmisc_1(A_107)) | ~m1_subset_1(B_108, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.99/1.46  tff(c_32, plain, (![B_28, A_27]: (v1_subset_1(B_28, A_27) | B_28=A_27 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.99/1.46  tff(c_718, plain, (![A_132, B_133]: (v1_subset_1(k6_domain_1(A_132, B_133), A_132) | k6_domain_1(A_132, B_133)=A_132 | ~m1_subset_1(B_133, A_132) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_593, c_32])).
% 2.99/1.46  tff(c_62, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.99/1.46  tff(c_73, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 2.99/1.46  tff(c_124, plain, (![A_54, B_55]: (~v1_zfmisc_1(A_54) | ~v1_subset_1(k6_domain_1(A_54, B_55), A_54) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.99/1.46  tff(c_130, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_73, c_124])).
% 2.99/1.46  tff(c_133, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_130])).
% 2.99/1.46  tff(c_136, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_133])).
% 2.99/1.46  tff(c_170, plain, (![A_60, B_61]: (m1_pre_topc(k1_tex_2(A_60, B_61), A_60) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.99/1.46  tff(c_175, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_170])).
% 2.99/1.46  tff(c_179, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_175])).
% 2.99/1.46  tff(c_180, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_179])).
% 2.99/1.46  tff(c_343, plain, (![A_80, B_81]: (m1_subset_1('#skF_2'(A_80, B_81), k1_zfmisc_1(u1_struct_0(A_80))) | v1_tex_2(B_81, A_80) | ~m1_pre_topc(B_81, A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.99/1.46  tff(c_497, plain, (![A_97, B_98]: (v1_subset_1('#skF_2'(A_97, B_98), u1_struct_0(A_97)) | u1_struct_0(A_97)='#skF_2'(A_97, B_98) | v1_tex_2(B_98, A_97) | ~m1_pre_topc(B_98, A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_343, c_32])).
% 2.99/1.46  tff(c_26, plain, (![A_17, B_23]: (~v1_subset_1('#skF_2'(A_17, B_23), u1_struct_0(A_17)) | v1_tex_2(B_23, A_17) | ~m1_pre_topc(B_23, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.99/1.46  tff(c_517, plain, (![A_99, B_100]: (u1_struct_0(A_99)='#skF_2'(A_99, B_100) | v1_tex_2(B_100, A_99) | ~m1_pre_topc(B_100, A_99) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_497, c_26])).
% 2.99/1.46  tff(c_56, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.99/1.46  tff(c_135, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56])).
% 2.99/1.46  tff(c_523, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_517, c_135])).
% 2.99/1.46  tff(c_527, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_180, c_523])).
% 2.99/1.46  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.99/1.46  tff(c_183, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_180, c_4])).
% 2.99/1.46  tff(c_186, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_183])).
% 2.99/1.46  tff(c_111, plain, (![A_52, B_53]: (~v2_struct_0(k1_tex_2(A_52, B_53)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.99/1.46  tff(c_118, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_111])).
% 2.99/1.46  tff(c_122, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_118])).
% 2.99/1.46  tff(c_123, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_122])).
% 2.99/1.46  tff(c_187, plain, (![B_62, A_63]: (u1_struct_0(B_62)='#skF_2'(A_63, B_62) | v1_tex_2(B_62, A_63) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.99/1.46  tff(c_190, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_187, c_135])).
% 2.99/1.46  tff(c_193, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_180, c_190])).
% 2.99/1.46  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.99/1.46  tff(c_211, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_6])).
% 2.99/1.46  tff(c_230, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_123, c_211])).
% 2.99/1.46  tff(c_239, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_230])).
% 2.99/1.46  tff(c_242, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_239])).
% 2.99/1.46  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_242])).
% 2.99/1.46  tff(c_248, plain, (l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_230])).
% 2.99/1.46  tff(c_155, plain, (![A_58, B_59]: (v7_struct_0(k1_tex_2(A_58, B_59)) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l1_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.99/1.46  tff(c_162, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_155])).
% 2.99/1.46  tff(c_166, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_162])).
% 2.99/1.46  tff(c_167, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_166])).
% 2.99/1.46  tff(c_10, plain, (![A_7]: (v1_zfmisc_1(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | ~v7_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.46  tff(c_214, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_10])).
% 2.99/1.46  tff(c_232, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_214])).
% 2.99/1.46  tff(c_256, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_232])).
% 2.99/1.46  tff(c_539, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_527, c_256])).
% 2.99/1.46  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_539])).
% 2.99/1.46  tff(c_545, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_133])).
% 2.99/1.46  tff(c_562, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_545, c_6])).
% 2.99/1.46  tff(c_565, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_562])).
% 2.99/1.46  tff(c_568, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_565])).
% 2.99/1.46  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_568])).
% 2.99/1.46  tff(c_573, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 2.99/1.46  tff(c_576, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_56])).
% 2.99/1.46  tff(c_724, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_718, c_576])).
% 2.99/1.46  tff(c_731, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_724])).
% 2.99/1.46  tff(c_732, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_631, c_731])).
% 2.99/1.46  tff(c_735, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_732, c_6])).
% 2.99/1.46  tff(c_738, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_735])).
% 2.99/1.46  tff(c_741, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_738])).
% 2.99/1.46  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_741])).
% 2.99/1.46  tff(c_746, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_613])).
% 2.99/1.46  tff(c_748, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_746])).
% 2.99/1.46  tff(c_8, plain, (![A_6]: (~v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.99/1.46  tff(c_752, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_748, c_8])).
% 2.99/1.46  tff(c_753, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_752])).
% 2.99/1.46  tff(c_756, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_753])).
% 2.99/1.46  tff(c_760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_756])).
% 2.99/1.46  tff(c_761, plain, (v7_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_752])).
% 2.99/1.46  tff(c_830, plain, (![A_138, B_139]: (m1_pre_topc(k1_tex_2(A_138, B_139), A_138) | ~m1_subset_1(B_139, u1_struct_0(A_138)) | ~l1_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.99/1.46  tff(c_835, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_830])).
% 2.99/1.46  tff(c_839, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_835])).
% 2.99/1.46  tff(c_840, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_839])).
% 2.99/1.46  tff(c_850, plain, (![B_144, A_145]: (~v1_tex_2(B_144, A_145) | v2_struct_0(B_144) | ~m1_pre_topc(B_144, A_145) | ~l1_pre_topc(A_145) | ~v7_struct_0(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.46  tff(c_856, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_573, c_850])).
% 2.99/1.46  tff(c_860, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_761, c_52, c_840, c_856])).
% 2.99/1.46  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_775, c_860])).
% 2.99/1.46  tff(c_863, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_746])).
% 2.99/1.46  tff(c_867, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_863, c_6])).
% 2.99/1.46  tff(c_870, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_867])).
% 2.99/1.46  tff(c_886, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_870])).
% 2.99/1.46  tff(c_890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_886])).
% 2.99/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.46  
% 2.99/1.46  Inference rules
% 2.99/1.46  ----------------------
% 2.99/1.46  #Ref     : 0
% 2.99/1.46  #Sup     : 142
% 2.99/1.46  #Fact    : 0
% 2.99/1.46  #Define  : 0
% 2.99/1.46  #Split   : 10
% 2.99/1.46  #Chain   : 0
% 2.99/1.46  #Close   : 0
% 2.99/1.46  
% 2.99/1.46  Ordering : KBO
% 2.99/1.46  
% 2.99/1.46  Simplification rules
% 2.99/1.46  ----------------------
% 2.99/1.46  #Subsume      : 16
% 2.99/1.46  #Demod        : 121
% 2.99/1.46  #Tautology    : 27
% 2.99/1.46  #SimpNegUnit  : 42
% 2.99/1.46  #BackRed      : 16
% 2.99/1.46  
% 2.99/1.46  #Partial instantiations: 0
% 2.99/1.46  #Strategies tried      : 1
% 2.99/1.46  
% 2.99/1.46  Timing (in seconds)
% 2.99/1.46  ----------------------
% 2.99/1.46  Preprocessing        : 0.33
% 2.99/1.46  Parsing              : 0.17
% 2.99/1.46  CNF conversion       : 0.02
% 2.99/1.46  Main loop            : 0.37
% 2.99/1.46  Inferencing          : 0.14
% 2.99/1.46  Reduction            : 0.11
% 2.99/1.46  Demodulation         : 0.08
% 2.99/1.46  BG Simplification    : 0.02
% 2.99/1.46  Subsumption          : 0.06
% 2.99/1.46  Abstraction          : 0.02
% 2.99/1.46  MUC search           : 0.00
% 2.99/1.46  Cooper               : 0.00
% 2.99/1.46  Total                : 0.74
% 2.99/1.46  Index Insertion      : 0.00
% 2.99/1.46  Index Deletion       : 0.00
% 2.99/1.46  Index Matching       : 0.00
% 2.99/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:00 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 214 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  200 ( 548 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

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

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_147,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_136,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc13_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_74,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_240,plain,(
    ! [A_57,B_58] :
      ( m1_pre_topc(k1_tex_2(A_57,B_58),A_57)
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_242,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_240])).

tff(c_245,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_242])).

tff(c_246,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_245])).

tff(c_163,plain,(
    ! [A_45,B_46] :
      ( ~ v2_struct_0(k1_tex_2(A_45,B_46))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_166,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_169,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_166])).

tff(c_170,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_169])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    ! [A_51,B_52] :
      ( v1_subset_1(k6_domain_1(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,A_51)
      | v1_zfmisc_1(A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10,plain,(
    ! [A_5] :
      ( v1_zfmisc_1(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | ~ v7_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_63,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_91,plain,(
    ! [A_37,B_38] :
      ( ~ v1_zfmisc_1(A_37)
      | ~ v1_subset_1(k6_domain_1(A_37,B_38),A_37)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_97,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_63,c_91])).

tff(c_101,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_97])).

tff(c_102,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_109,plain,
    ( ~ l1_struct_0('#skF_1')
    | ~ v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_102])).

tff(c_111,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_83,plain,(
    ! [A_35,B_36] :
      ( ~ v2_struct_0(k1_tex_2(A_35,B_36))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l1_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_86,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_89,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_86])).

tff(c_90,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_89])).

tff(c_112,plain,(
    ! [A_39,B_40] :
      ( m1_pre_topc(k1_tex_2(A_39,B_40),A_39)
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_114,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_117,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_114])).

tff(c_118,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_117])).

tff(c_66,plain,(
    ! [A_29,B_30] :
      ( v7_struct_0(k1_tex_2(A_29,B_30))
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_69,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_72,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_69])).

tff(c_73,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_72])).

tff(c_120,plain,(
    ! [B_43,A_44] :
      ( ~ v7_struct_0(B_43)
      | v1_tex_2(B_43,A_44)
      | v2_struct_0(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44)
      | v7_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_65,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42])).

tff(c_126,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_65])).

tff(c_130,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_118,c_73,c_126])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_111,c_90,c_130])).

tff(c_133,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_137,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_137])).

tff(c_142,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_6,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_142,c_6])).

tff(c_153,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_149])).

tff(c_156,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_156])).

tff(c_162,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_192,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_189,c_162])).

tff(c_195,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_192])).

tff(c_196,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_202,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_196,c_6])).

tff(c_206,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_202])).

tff(c_214,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_206])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_214])).

tff(c_219,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v7_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_224,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_219,c_8])).

tff(c_225,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_228,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_225])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_228])).

tff(c_233,plain,(
    v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_161,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_247,plain,(
    ! [B_59,A_60] :
      ( ~ v1_tex_2(B_59,A_60)
      | v2_struct_0(B_59)
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v7_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_250,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_161,c_247])).

tff(c_253,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_38,c_250])).

tff(c_254,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_170,c_253])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.27  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 2.14/1.27  
% 2.14/1.27  %Foreground sorts:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Background operators:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Foreground operators:
% 2.14/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.27  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.14/1.27  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.14/1.27  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.14/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.14/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.14/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.27  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.14/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.27  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.27  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.14/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.14/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.27  
% 2.14/1.29  tff(f_160, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.14/1.29  tff(f_111, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.14/1.29  tff(f_125, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.14/1.29  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.14/1.29  tff(f_147, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 2.14/1.29  tff(f_55, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.14/1.29  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.14/1.29  tff(f_97, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v1_tex_2(B, A)) => (~v2_struct_0(B) & ~v7_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc13_tex_2)).
% 2.14/1.29  tff(f_41, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.14/1.29  tff(f_49, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.14/1.29  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.14/1.29  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.14/1.29  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.14/1.29  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.14/1.29  tff(c_240, plain, (![A_57, B_58]: (m1_pre_topc(k1_tex_2(A_57, B_58), A_57) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~l1_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.14/1.29  tff(c_242, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_240])).
% 2.14/1.29  tff(c_245, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_242])).
% 2.14/1.29  tff(c_246, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_245])).
% 2.14/1.29  tff(c_163, plain, (![A_45, B_46]: (~v2_struct_0(k1_tex_2(A_45, B_46)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.14/1.29  tff(c_166, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_163])).
% 2.14/1.29  tff(c_169, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_166])).
% 2.14/1.29  tff(c_170, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_169])).
% 2.14/1.29  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.29  tff(c_189, plain, (![A_51, B_52]: (v1_subset_1(k6_domain_1(A_51, B_52), A_51) | ~m1_subset_1(B_52, A_51) | v1_zfmisc_1(A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.14/1.29  tff(c_10, plain, (![A_5]: (v1_zfmisc_1(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | ~v7_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.14/1.29  tff(c_48, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.14/1.29  tff(c_63, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.14/1.29  tff(c_91, plain, (![A_37, B_38]: (~v1_zfmisc_1(A_37) | ~v1_subset_1(k6_domain_1(A_37, B_38), A_37) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.14/1.29  tff(c_97, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_63, c_91])).
% 2.14/1.29  tff(c_101, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_97])).
% 2.14/1.29  tff(c_102, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_101])).
% 2.14/1.29  tff(c_109, plain, (~l1_struct_0('#skF_1') | ~v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_102])).
% 2.14/1.29  tff(c_111, plain, (~v7_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_109])).
% 2.14/1.29  tff(c_83, plain, (![A_35, B_36]: (~v2_struct_0(k1_tex_2(A_35, B_36)) | ~m1_subset_1(B_36, u1_struct_0(A_35)) | ~l1_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.14/1.29  tff(c_86, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_83])).
% 2.14/1.29  tff(c_89, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_86])).
% 2.14/1.29  tff(c_90, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_89])).
% 2.14/1.29  tff(c_112, plain, (![A_39, B_40]: (m1_pre_topc(k1_tex_2(A_39, B_40), A_39) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.14/1.29  tff(c_114, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_112])).
% 2.14/1.29  tff(c_117, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_114])).
% 2.14/1.29  tff(c_118, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_117])).
% 2.14/1.29  tff(c_66, plain, (![A_29, B_30]: (v7_struct_0(k1_tex_2(A_29, B_30)) | ~m1_subset_1(B_30, u1_struct_0(A_29)) | ~l1_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.14/1.29  tff(c_69, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_66])).
% 2.14/1.29  tff(c_72, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_69])).
% 2.14/1.29  tff(c_73, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_72])).
% 2.14/1.29  tff(c_120, plain, (![B_43, A_44]: (~v7_struct_0(B_43) | v1_tex_2(B_43, A_44) | v2_struct_0(B_43) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44) | v7_struct_0(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.14/1.29  tff(c_42, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.14/1.29  tff(c_65, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42])).
% 2.14/1.29  tff(c_126, plain, (~v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_120, c_65])).
% 2.14/1.29  tff(c_130, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_118, c_73, c_126])).
% 2.14/1.29  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_111, c_90, c_130])).
% 2.14/1.29  tff(c_133, plain, (~l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_109])).
% 2.14/1.29  tff(c_137, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.14/1.29  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_137])).
% 2.14/1.29  tff(c_142, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_101])).
% 2.14/1.29  tff(c_6, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.29  tff(c_149, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_142, c_6])).
% 2.14/1.29  tff(c_153, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_149])).
% 2.14/1.29  tff(c_156, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_153])).
% 2.14/1.29  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_156])).
% 2.14/1.29  tff(c_162, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 2.14/1.29  tff(c_192, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_189, c_162])).
% 2.14/1.29  tff(c_195, plain, (v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_192])).
% 2.14/1.29  tff(c_196, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_195])).
% 2.14/1.29  tff(c_202, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_196, c_6])).
% 2.14/1.29  tff(c_206, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_202])).
% 2.14/1.29  tff(c_214, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_206])).
% 2.14/1.29  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_214])).
% 2.14/1.29  tff(c_219, plain, (v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_195])).
% 2.14/1.29  tff(c_8, plain, (![A_4]: (~v1_zfmisc_1(u1_struct_0(A_4)) | ~l1_struct_0(A_4) | v7_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.29  tff(c_224, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_219, c_8])).
% 2.14/1.29  tff(c_225, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_224])).
% 2.14/1.29  tff(c_228, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_225])).
% 2.14/1.29  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_228])).
% 2.14/1.29  tff(c_233, plain, (v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_224])).
% 2.14/1.29  tff(c_161, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 2.14/1.29  tff(c_247, plain, (![B_59, A_60]: (~v1_tex_2(B_59, A_60) | v2_struct_0(B_59) | ~m1_pre_topc(B_59, A_60) | ~l1_pre_topc(A_60) | ~v7_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.29  tff(c_250, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_161, c_247])).
% 2.14/1.29  tff(c_253, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_38, c_250])).
% 2.14/1.29  tff(c_254, plain, (~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_170, c_253])).
% 2.14/1.29  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_246, c_254])).
% 2.14/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  Inference rules
% 2.14/1.29  ----------------------
% 2.14/1.29  #Ref     : 0
% 2.14/1.29  #Sup     : 29
% 2.14/1.29  #Fact    : 0
% 2.14/1.29  #Define  : 0
% 2.14/1.29  #Split   : 5
% 2.14/1.29  #Chain   : 0
% 2.14/1.29  #Close   : 0
% 2.14/1.29  
% 2.14/1.29  Ordering : KBO
% 2.14/1.29  
% 2.14/1.29  Simplification rules
% 2.14/1.29  ----------------------
% 2.14/1.29  #Subsume      : 3
% 2.14/1.29  #Demod        : 22
% 2.14/1.29  #Tautology    : 9
% 2.14/1.29  #SimpNegUnit  : 12
% 2.14/1.29  #BackRed      : 0
% 2.14/1.29  
% 2.14/1.29  #Partial instantiations: 0
% 2.14/1.29  #Strategies tried      : 1
% 2.14/1.29  
% 2.14/1.29  Timing (in seconds)
% 2.14/1.29  ----------------------
% 2.14/1.30  Preprocessing        : 0.30
% 2.14/1.30  Parsing              : 0.17
% 2.14/1.30  CNF conversion       : 0.02
% 2.14/1.30  Main loop            : 0.20
% 2.14/1.30  Inferencing          : 0.08
% 2.14/1.30  Reduction            : 0.05
% 2.14/1.30  Demodulation         : 0.04
% 2.14/1.30  BG Simplification    : 0.01
% 2.14/1.30  Subsumption          : 0.03
% 2.14/1.30  Abstraction          : 0.01
% 2.14/1.30  MUC search           : 0.00
% 2.14/1.30  Cooper               : 0.00
% 2.14/1.30  Total                : 0.53
% 2.14/1.30  Index Insertion      : 0.00
% 2.14/1.30  Index Deletion       : 0.00
% 2.14/1.30  Index Matching       : 0.00
% 2.14/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

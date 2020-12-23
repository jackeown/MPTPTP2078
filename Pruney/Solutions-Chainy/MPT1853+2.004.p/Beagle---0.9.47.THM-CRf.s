%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:00 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 231 expanded)
%              Number of leaves         :   29 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  226 ( 617 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_148,negated_conjecture,(
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
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_83,axiom,(
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

tff(f_135,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_60,axiom,(
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

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_241,plain,(
    ! [A_57,B_58] :
      ( ~ v2_struct_0(k1_tex_2(A_57,B_58))
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_244,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_241])).

tff(c_247,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_244])).

tff(c_248,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_247])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    ! [A_45,B_46] :
      ( ~ v2_struct_0(k1_tex_2(A_45,B_46))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_178,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_175])).

tff(c_181,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_178])).

tff(c_182,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_181])).

tff(c_28,plain,(
    ! [A_14,B_16] :
      ( v1_subset_1(k6_domain_1(A_14,B_16),A_14)
      | ~ m1_subset_1(B_16,A_14)
      | v1_zfmisc_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_64,plain,(
    ! [A_29,B_30] :
      ( ~ v2_struct_0(k1_tex_2(A_29,B_30))
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_67,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_70,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_67])).

tff(c_71,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_70])).

tff(c_80,plain,(
    ! [A_33,B_34] :
      ( m1_pre_topc(k1_tex_2(A_33,B_34),A_33)
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_82,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_80])).

tff(c_85,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_82])).

tff(c_86,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_85])).

tff(c_72,plain,(
    ! [A_31,B_32] :
      ( v7_struct_0(k1_tex_2(A_31,B_32))
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_75,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_78,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_75])).

tff(c_79,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_78])).

tff(c_88,plain,(
    ! [B_37,A_38] :
      ( ~ v7_struct_0(B_37)
      | v1_tex_2(B_37,A_38)
      | v2_struct_0(B_37)
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38)
      | v7_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_55,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_94,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_55])).

tff(c_98,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_86,c_79,c_94])).

tff(c_99,plain,(
    v7_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_71,c_98])).

tff(c_44,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_100,plain,(
    ! [A_39,B_40] :
      ( ~ v7_struct_0(A_39)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_39),B_40),u1_struct_0(A_39))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_103,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_100])).

tff(c_110,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_99,c_103])).

tff(c_111,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_110])).

tff(c_115,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_115])).

tff(c_120,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_54])).

tff(c_135,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_138,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_135])).

tff(c_141,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_138])).

tff(c_142,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_23] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v7_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [A_23] :
      ( ~ l1_struct_0(A_23)
      | v7_struct_0(A_23)
      | ~ v1_xboole_0(u1_struct_0(A_23)) ) ),
    inference(resolution,[status(thm)],[c_2,c_47])).

tff(c_146,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_142,c_51])).

tff(c_147,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_158,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_147])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_158])).

tff(c_163,plain,(
    v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_191,plain,(
    ! [A_49,B_50] :
      ( m1_pre_topc(k1_tex_2(A_49,B_50),A_49)
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_193,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_191])).

tff(c_196,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_193])).

tff(c_197,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_196])).

tff(c_134,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_198,plain,(
    ! [B_51,A_52] :
      ( ~ v1_tex_2(B_51,A_52)
      | v2_struct_0(B_51)
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v7_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_201,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_134,c_198])).

tff(c_204,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_34,c_197,c_201])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_182,c_204])).

tff(c_207,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_6,plain,(
    ! [A_3] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v7_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_214,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_207,c_6])).

tff(c_215,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_218,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_215])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218])).

tff(c_223,plain,(
    v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_249,plain,(
    ! [A_59,B_60] :
      ( m1_pre_topc(k1_tex_2(A_59,B_60),A_59)
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_251,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_249])).

tff(c_254,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_251])).

tff(c_255,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_254])).

tff(c_256,plain,(
    ! [B_61,A_62] :
      ( ~ v1_tex_2(B_61,A_62)
      | v2_struct_0(B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v7_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_259,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_134,c_256])).

tff(c_262,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_34,c_255,c_259])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_248,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.22  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 1.99/1.22  
% 1.99/1.22  %Foreground sorts:
% 1.99/1.22  
% 1.99/1.22  
% 1.99/1.22  %Background operators:
% 1.99/1.22  
% 1.99/1.22  
% 1.99/1.22  %Foreground operators:
% 1.99/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.22  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.99/1.22  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 1.99/1.22  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.99/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.99/1.22  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.99/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.22  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.99/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.22  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.22  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.99/1.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.99/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.22  
% 2.26/1.24  tff(f_148, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.26/1.24  tff(f_111, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.26/1.24  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.26/1.24  tff(f_122, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 2.26/1.24  tff(f_97, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.26/1.24  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v1_tex_2(B, A)) => (~v2_struct_0(B) & ~v7_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc13_tex_2)).
% 2.26/1.24  tff(f_135, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.26/1.24  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.26/1.24  tff(f_41, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.26/1.24  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.26/1.24  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.26/1.24  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.26/1.24  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.26/1.24  tff(c_241, plain, (![A_57, B_58]: (~v2_struct_0(k1_tex_2(A_57, B_58)) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~l1_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.26/1.24  tff(c_244, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_241])).
% 2.26/1.24  tff(c_247, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_244])).
% 2.26/1.24  tff(c_248, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_247])).
% 2.26/1.24  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.24  tff(c_175, plain, (![A_45, B_46]: (~v2_struct_0(k1_tex_2(A_45, B_46)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.26/1.24  tff(c_178, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_175])).
% 2.26/1.24  tff(c_181, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_178])).
% 2.26/1.24  tff(c_182, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_181])).
% 2.26/1.24  tff(c_28, plain, (![A_14, B_16]: (v1_subset_1(k6_domain_1(A_14, B_16), A_14) | ~m1_subset_1(B_16, A_14) | v1_zfmisc_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.26/1.24  tff(c_64, plain, (![A_29, B_30]: (~v2_struct_0(k1_tex_2(A_29, B_30)) | ~m1_subset_1(B_30, u1_struct_0(A_29)) | ~l1_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.26/1.24  tff(c_67, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_64])).
% 2.26/1.24  tff(c_70, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_67])).
% 2.26/1.24  tff(c_71, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_70])).
% 2.26/1.24  tff(c_80, plain, (![A_33, B_34]: (m1_pre_topc(k1_tex_2(A_33, B_34), A_33) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.24  tff(c_82, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_80])).
% 2.26/1.24  tff(c_85, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_82])).
% 2.26/1.24  tff(c_86, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_85])).
% 2.26/1.24  tff(c_72, plain, (![A_31, B_32]: (v7_struct_0(k1_tex_2(A_31, B_32)) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.26/1.24  tff(c_75, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_72])).
% 2.26/1.24  tff(c_78, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_75])).
% 2.26/1.24  tff(c_79, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_78])).
% 2.26/1.24  tff(c_88, plain, (![B_37, A_38]: (~v7_struct_0(B_37) | v1_tex_2(B_37, A_38) | v2_struct_0(B_37) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38) | v7_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.26/1.24  tff(c_38, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.26/1.24  tff(c_55, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 2.26/1.24  tff(c_94, plain, (~v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_55])).
% 2.26/1.24  tff(c_98, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_86, c_79, c_94])).
% 2.26/1.24  tff(c_99, plain, (v7_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_71, c_98])).
% 2.26/1.24  tff(c_44, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.26/1.24  tff(c_54, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.26/1.24  tff(c_100, plain, (![A_39, B_40]: (~v7_struct_0(A_39) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_39), B_40), u1_struct_0(A_39)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.24  tff(c_103, plain, (~v7_struct_0('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_100])).
% 2.26/1.24  tff(c_110, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_99, c_103])).
% 2.26/1.24  tff(c_111, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_110])).
% 2.26/1.24  tff(c_115, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_111])).
% 2.26/1.24  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_115])).
% 2.26/1.24  tff(c_120, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_38])).
% 2.26/1.24  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_54])).
% 2.26/1.24  tff(c_135, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_44])).
% 2.26/1.24  tff(c_138, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_135])).
% 2.26/1.24  tff(c_141, plain, (v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_138])).
% 2.26/1.24  tff(c_142, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_141])).
% 2.26/1.24  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.24  tff(c_47, plain, (![A_23]: (~v1_zfmisc_1(u1_struct_0(A_23)) | ~l1_struct_0(A_23) | v7_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.24  tff(c_51, plain, (![A_23]: (~l1_struct_0(A_23) | v7_struct_0(A_23) | ~v1_xboole_0(u1_struct_0(A_23)))), inference(resolution, [status(thm)], [c_2, c_47])).
% 2.26/1.24  tff(c_146, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_142, c_51])).
% 2.26/1.24  tff(c_147, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_146])).
% 2.26/1.24  tff(c_158, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_147])).
% 2.26/1.24  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_158])).
% 2.26/1.24  tff(c_163, plain, (v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_146])).
% 2.26/1.24  tff(c_191, plain, (![A_49, B_50]: (m1_pre_topc(k1_tex_2(A_49, B_50), A_49) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.24  tff(c_193, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_191])).
% 2.26/1.24  tff(c_196, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_193])).
% 2.26/1.24  tff(c_197, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_196])).
% 2.26/1.24  tff(c_134, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 2.26/1.24  tff(c_198, plain, (![B_51, A_52]: (~v1_tex_2(B_51, A_52) | v2_struct_0(B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52) | ~v7_struct_0(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.26/1.24  tff(c_201, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_134, c_198])).
% 2.26/1.24  tff(c_204, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_34, c_197, c_201])).
% 2.26/1.24  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_182, c_204])).
% 2.26/1.24  tff(c_207, plain, (v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_141])).
% 2.26/1.24  tff(c_6, plain, (![A_3]: (~v1_zfmisc_1(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v7_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.24  tff(c_214, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_207, c_6])).
% 2.26/1.24  tff(c_215, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_214])).
% 2.26/1.24  tff(c_218, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_215])).
% 2.26/1.24  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_218])).
% 2.26/1.24  tff(c_223, plain, (v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_214])).
% 2.26/1.24  tff(c_249, plain, (![A_59, B_60]: (m1_pre_topc(k1_tex_2(A_59, B_60), A_59) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.24  tff(c_251, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_249])).
% 2.26/1.24  tff(c_254, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_251])).
% 2.26/1.24  tff(c_255, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_254])).
% 2.26/1.24  tff(c_256, plain, (![B_61, A_62]: (~v1_tex_2(B_61, A_62) | v2_struct_0(B_61) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62) | ~v7_struct_0(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.26/1.24  tff(c_259, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_134, c_256])).
% 2.26/1.24  tff(c_262, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_34, c_255, c_259])).
% 2.26/1.24  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_248, c_262])).
% 2.26/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.24  
% 2.26/1.24  Inference rules
% 2.26/1.24  ----------------------
% 2.26/1.24  #Ref     : 0
% 2.26/1.24  #Sup     : 28
% 2.26/1.24  #Fact    : 0
% 2.26/1.24  #Define  : 0
% 2.26/1.24  #Split   : 6
% 2.26/1.24  #Chain   : 0
% 2.26/1.24  #Close   : 0
% 2.26/1.24  
% 2.26/1.24  Ordering : KBO
% 2.26/1.24  
% 2.26/1.24  Simplification rules
% 2.26/1.24  ----------------------
% 2.26/1.24  #Subsume      : 4
% 2.26/1.24  #Demod        : 31
% 2.26/1.24  #Tautology    : 5
% 2.26/1.24  #SimpNegUnit  : 18
% 2.26/1.24  #BackRed      : 0
% 2.26/1.24  
% 2.26/1.24  #Partial instantiations: 0
% 2.26/1.24  #Strategies tried      : 1
% 2.26/1.24  
% 2.26/1.24  Timing (in seconds)
% 2.26/1.24  ----------------------
% 2.26/1.25  Preprocessing        : 0.29
% 2.26/1.25  Parsing              : 0.16
% 2.26/1.25  CNF conversion       : 0.02
% 2.26/1.25  Main loop            : 0.19
% 2.26/1.25  Inferencing          : 0.08
% 2.26/1.25  Reduction            : 0.05
% 2.26/1.25  Demodulation         : 0.04
% 2.26/1.25  BG Simplification    : 0.01
% 2.26/1.25  Subsumption          : 0.03
% 2.26/1.25  Abstraction          : 0.01
% 2.26/1.25  MUC search           : 0.00
% 2.26/1.25  Cooper               : 0.00
% 2.26/1.25  Total                : 0.53
% 2.26/1.25  Index Insertion      : 0.00
% 2.26/1.25  Index Deletion       : 0.00
% 2.26/1.25  Index Matching       : 0.00
% 2.26/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

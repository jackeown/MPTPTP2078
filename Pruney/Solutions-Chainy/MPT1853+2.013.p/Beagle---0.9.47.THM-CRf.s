%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:01 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 769 expanded)
%              Number of leaves         :   33 ( 266 expanded)
%              Depth                    :   14
%              Number of atoms          :  293 (2323 expanded)
%              Number of equality atoms :    7 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_109,axiom,(
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

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_147,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_48,axiom,(
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

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_422,plain,(
    ! [A_87,B_88] :
      ( ~ v2_struct_0(k1_tex_2(A_87,B_88))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_425,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_422])).

tff(c_428,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_425])).

tff(c_429,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_428])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_431,plain,(
    ! [A_90,B_91] :
      ( v1_subset_1(k6_domain_1(A_90,B_91),A_90)
      | ~ m1_subset_1(B_91,A_90)
      | v1_zfmisc_1(A_90)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_63,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_76,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_52])).

tff(c_123,plain,(
    ! [A_59,B_60] :
      ( ~ v7_struct_0(A_59)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_59),B_60),u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_130,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_123])).

tff(c_134,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_130])).

tff(c_135,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_134])).

tff(c_136,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_139,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_139])).

tff(c_144,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_145,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_102,plain,(
    ! [A_53,B_54] :
      ( m1_pre_topc(k1_tex_2(A_53,B_54),A_53)
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ l1_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_104,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_102])).

tff(c_107,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_104])).

tff(c_108,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_107])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( l1_pre_topc(B_5)
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_108,c_6])).

tff(c_114,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_111])).

tff(c_93,plain,(
    ! [A_49,B_50] :
      ( ~ v2_struct_0(k1_tex_2(A_49,B_50))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_96,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_99,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_96])).

tff(c_100,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_99])).

tff(c_65,plain,(
    ! [B_42,A_43] :
      ( m1_subset_1(u1_struct_0(B_42),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_42,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( v1_subset_1(B_14,A_13)
      | B_14 = A_13
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_73,plain,(
    ! [B_42,A_43] :
      ( v1_subset_1(u1_struct_0(B_42),u1_struct_0(A_43))
      | u1_struct_0(B_42) = u1_struct_0(A_43)
      | ~ m1_pre_topc(B_42,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_65,c_16])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( m1_subset_1(u1_struct_0(B_9),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_165,plain,(
    ! [B_67,A_68] :
      ( v1_tex_2(B_67,A_68)
      | ~ v1_subset_1(u1_struct_0(B_67),u1_struct_0(A_68))
      | ~ m1_subset_1(u1_struct_0(B_67),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_171,plain,(
    ! [B_70,A_71] :
      ( v1_tex_2(B_70,A_71)
      | ~ v1_subset_1(u1_struct_0(B_70),u1_struct_0(A_71))
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_180,plain,(
    ! [B_72,A_73] :
      ( v1_tex_2(B_72,A_73)
      | u1_struct_0(B_72) = u1_struct_0(A_73)
      | ~ m1_pre_topc(B_72,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_73,c_171])).

tff(c_190,plain,
    ( u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_180,c_63])).

tff(c_196,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_108,c_190])).

tff(c_77,plain,(
    ! [A_45,B_46] :
      ( v7_struct_0(k1_tex_2(A_45,B_46))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_80,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_83,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_80])).

tff(c_84,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_83])).

tff(c_36,plain,(
    ! [A_26,B_28] :
      ( v1_subset_1(k6_domain_1(A_26,B_28),A_26)
      | ~ m1_subset_1(B_28,A_26)
      | v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_131,plain,(
    ! [A_59,B_28] :
      ( ~ v7_struct_0(A_59)
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59)
      | ~ m1_subset_1(B_28,u1_struct_0(A_59))
      | v1_zfmisc_1(u1_struct_0(A_59))
      | v1_xboole_0(u1_struct_0(A_59)) ) ),
    inference(resolution,[status(thm)],[c_36,c_123])).

tff(c_212,plain,(
    ! [B_28] :
      ( ~ v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_1'))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')))
      | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_131])).

tff(c_261,plain,(
    ! [B_28] :
      ( ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_1'))
      | v1_zfmisc_1(u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_196,c_84,c_212])).

tff(c_262,plain,(
    ! [B_28] :
      ( ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_1'))
      | v1_zfmisc_1(u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_261])).

tff(c_365,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_368,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_365])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_368])).

tff(c_373,plain,(
    ! [B_28] :
      ( ~ m1_subset_1(B_28,u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_zfmisc_1(u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_381,plain,(
    ! [B_28] : ~ m1_subset_1(B_28,u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_40])).

tff(c_384,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_385,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_35] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_35))
      | ~ l1_struct_0(A_35)
      | v7_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59,plain,(
    ! [A_35] :
      ( ~ l1_struct_0(A_35)
      | v7_struct_0(A_35)
      | ~ v1_xboole_0(u1_struct_0(A_35)) ) ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_388,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_385,c_59])).

tff(c_391,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_388])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_391])).

tff(c_394,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_398,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_394,c_8])).

tff(c_401,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_398])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_401])).

tff(c_404,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_406,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_406])).

tff(c_409,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_434,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_431,c_409])).

tff(c_437,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_434])).

tff(c_438,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_437])).

tff(c_442,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_438,c_59])).

tff(c_451,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_442])).

tff(c_454,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_451])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_454])).

tff(c_459,plain,(
    v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_469,plain,(
    ! [A_96,B_97] :
      ( m1_pre_topc(k1_tex_2(A_96,B_97),A_96)
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_471,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_469])).

tff(c_474,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_471])).

tff(c_475,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_474])).

tff(c_405,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_482,plain,(
    ! [B_98,A_99] :
      ( ~ v1_tex_2(B_98,A_99)
      | v2_struct_0(B_98)
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99)
      | ~ v7_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_485,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_405,c_482])).

tff(c_488,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_42,c_475,c_485])).

tff(c_490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_429,c_488])).

tff(c_491,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_496,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_491,c_8])).

tff(c_497,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_500,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_497])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_500])).

tff(c_505,plain,(
    v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_523,plain,(
    ! [A_104,B_105] :
      ( m1_pre_topc(k1_tex_2(A_104,B_105),A_104)
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_525,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_523])).

tff(c_528,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_525])).

tff(c_529,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_528])).

tff(c_536,plain,(
    ! [B_106,A_107] :
      ( ~ v1_tex_2(B_106,A_107)
      | v2_struct_0(B_106)
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v7_struct_0(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_539,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_405,c_536])).

tff(c_542,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_42,c_529,c_539])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_429,c_542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:50:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.39  
% 2.87/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.40  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.87/1.40  
% 2.87/1.40  %Foreground sorts:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Background operators:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Foreground operators:
% 2.87/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.40  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.87/1.40  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.87/1.40  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.87/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.87/1.40  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.87/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.40  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.87/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.40  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.40  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.87/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.87/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.40  
% 2.87/1.42  tff(f_160, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.87/1.42  tff(f_109, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.87/1.42  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.87/1.42  tff(f_134, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 2.87/1.42  tff(f_147, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.87/1.42  tff(f_95, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.87/1.42  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.87/1.42  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.87/1.42  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.87/1.42  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tex_2)).
% 2.87/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.87/1.42  tff(f_48, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.87/1.42  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.87/1.42  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.87/1.42  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.87/1.42  tff(c_40, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.87/1.42  tff(c_422, plain, (![A_87, B_88]: (~v2_struct_0(k1_tex_2(A_87, B_88)) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.42  tff(c_425, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_422])).
% 2.87/1.42  tff(c_428, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_425])).
% 2.87/1.42  tff(c_429, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_428])).
% 2.87/1.42  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.42  tff(c_431, plain, (![A_90, B_91]: (v1_subset_1(k6_domain_1(A_90, B_91), A_90) | ~m1_subset_1(B_91, A_90) | v1_zfmisc_1(A_90) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.87/1.42  tff(c_46, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.87/1.42  tff(c_63, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 2.87/1.42  tff(c_52, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.87/1.42  tff(c_76, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_63, c_52])).
% 2.87/1.42  tff(c_123, plain, (![A_59, B_60]: (~v7_struct_0(A_59) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_59), B_60), u1_struct_0(A_59)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.87/1.42  tff(c_130, plain, (~v7_struct_0('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_123])).
% 2.87/1.42  tff(c_134, plain, (~v7_struct_0('#skF_1') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_130])).
% 2.87/1.42  tff(c_135, plain, (~v7_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_134])).
% 2.87/1.42  tff(c_136, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_135])).
% 2.87/1.42  tff(c_139, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_136])).
% 2.87/1.42  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_139])).
% 2.87/1.42  tff(c_144, plain, (~v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_135])).
% 2.87/1.42  tff(c_145, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_135])).
% 2.87/1.42  tff(c_102, plain, (![A_53, B_54]: (m1_pre_topc(k1_tex_2(A_53, B_54), A_53) | ~m1_subset_1(B_54, u1_struct_0(A_53)) | ~l1_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.42  tff(c_104, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_102])).
% 2.87/1.42  tff(c_107, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_104])).
% 2.87/1.42  tff(c_108, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_107])).
% 2.87/1.42  tff(c_6, plain, (![B_5, A_3]: (l1_pre_topc(B_5) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.42  tff(c_111, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_108, c_6])).
% 2.87/1.42  tff(c_114, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_111])).
% 2.87/1.42  tff(c_93, plain, (![A_49, B_50]: (~v2_struct_0(k1_tex_2(A_49, B_50)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.42  tff(c_96, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_93])).
% 2.87/1.42  tff(c_99, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_96])).
% 2.87/1.42  tff(c_100, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_99])).
% 2.87/1.42  tff(c_65, plain, (![B_42, A_43]: (m1_subset_1(u1_struct_0(B_42), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.87/1.42  tff(c_16, plain, (![B_14, A_13]: (v1_subset_1(B_14, A_13) | B_14=A_13 | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.87/1.42  tff(c_73, plain, (![B_42, A_43]: (v1_subset_1(u1_struct_0(B_42), u1_struct_0(A_43)) | u1_struct_0(B_42)=u1_struct_0(A_43) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_65, c_16])).
% 2.87/1.42  tff(c_10, plain, (![B_9, A_7]: (m1_subset_1(u1_struct_0(B_9), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.87/1.42  tff(c_165, plain, (![B_67, A_68]: (v1_tex_2(B_67, A_68) | ~v1_subset_1(u1_struct_0(B_67), u1_struct_0(A_68)) | ~m1_subset_1(u1_struct_0(B_67), k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.87/1.42  tff(c_171, plain, (![B_70, A_71]: (v1_tex_2(B_70, A_71) | ~v1_subset_1(u1_struct_0(B_70), u1_struct_0(A_71)) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_10, c_165])).
% 2.87/1.42  tff(c_180, plain, (![B_72, A_73]: (v1_tex_2(B_72, A_73) | u1_struct_0(B_72)=u1_struct_0(A_73) | ~m1_pre_topc(B_72, A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_73, c_171])).
% 2.87/1.42  tff(c_190, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_180, c_63])).
% 2.87/1.42  tff(c_196, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_108, c_190])).
% 2.87/1.42  tff(c_77, plain, (![A_45, B_46]: (v7_struct_0(k1_tex_2(A_45, B_46)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.42  tff(c_80, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_77])).
% 2.87/1.42  tff(c_83, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_80])).
% 2.87/1.42  tff(c_84, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_83])).
% 2.87/1.42  tff(c_36, plain, (![A_26, B_28]: (v1_subset_1(k6_domain_1(A_26, B_28), A_26) | ~m1_subset_1(B_28, A_26) | v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.87/1.42  tff(c_131, plain, (![A_59, B_28]: (~v7_struct_0(A_59) | ~l1_struct_0(A_59) | v2_struct_0(A_59) | ~m1_subset_1(B_28, u1_struct_0(A_59)) | v1_zfmisc_1(u1_struct_0(A_59)) | v1_xboole_0(u1_struct_0(A_59)))), inference(resolution, [status(thm)], [c_36, c_123])).
% 2.87/1.42  tff(c_212, plain, (![B_28]: (~v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1(B_28, u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_196, c_131])).
% 2.87/1.42  tff(c_261, plain, (![B_28]: (~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1(B_28, u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_196, c_84, c_212])).
% 2.87/1.42  tff(c_262, plain, (![B_28]: (~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1(B_28, u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_100, c_261])).
% 2.87/1.42  tff(c_365, plain, (~l1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_262])).
% 2.87/1.42  tff(c_368, plain, (~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4, c_365])).
% 2.87/1.42  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_368])).
% 2.87/1.42  tff(c_373, plain, (![B_28]: (~m1_subset_1(B_28, u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_262])).
% 2.87/1.42  tff(c_381, plain, (![B_28]: (~m1_subset_1(B_28, u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_373])).
% 2.87/1.42  tff(c_383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_40])).
% 2.87/1.42  tff(c_384, plain, (v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_373])).
% 2.87/1.42  tff(c_385, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_384])).
% 2.87/1.42  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.42  tff(c_55, plain, (![A_35]: (~v1_zfmisc_1(u1_struct_0(A_35)) | ~l1_struct_0(A_35) | v7_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.87/1.42  tff(c_59, plain, (![A_35]: (~l1_struct_0(A_35) | v7_struct_0(A_35) | ~v1_xboole_0(u1_struct_0(A_35)))), inference(resolution, [status(thm)], [c_2, c_55])).
% 2.87/1.42  tff(c_388, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_385, c_59])).
% 2.87/1.42  tff(c_391, plain, (v7_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_388])).
% 2.87/1.42  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_391])).
% 2.87/1.42  tff(c_394, plain, (v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_384])).
% 2.87/1.42  tff(c_8, plain, (![A_6]: (~v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.87/1.42  tff(c_398, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_394, c_8])).
% 2.87/1.42  tff(c_401, plain, (v7_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_398])).
% 2.87/1.42  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_401])).
% 2.87/1.42  tff(c_404, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_46])).
% 2.87/1.42  tff(c_406, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.87/1.42  tff(c_407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_404, c_406])).
% 2.87/1.42  tff(c_409, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_52])).
% 2.87/1.42  tff(c_434, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_431, c_409])).
% 2.87/1.42  tff(c_437, plain, (v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_434])).
% 2.87/1.42  tff(c_438, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_437])).
% 2.87/1.42  tff(c_442, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_438, c_59])).
% 2.87/1.42  tff(c_451, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_442])).
% 2.87/1.42  tff(c_454, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_451])).
% 2.87/1.42  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_454])).
% 2.87/1.42  tff(c_459, plain, (v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_442])).
% 2.87/1.42  tff(c_469, plain, (![A_96, B_97]: (m1_pre_topc(k1_tex_2(A_96, B_97), A_96) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.42  tff(c_471, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_469])).
% 2.87/1.42  tff(c_474, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_471])).
% 2.87/1.42  tff(c_475, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_474])).
% 2.87/1.42  tff(c_405, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 2.87/1.42  tff(c_482, plain, (![B_98, A_99]: (~v1_tex_2(B_98, A_99) | v2_struct_0(B_98) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99) | ~v7_struct_0(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.42  tff(c_485, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_405, c_482])).
% 2.87/1.42  tff(c_488, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_42, c_475, c_485])).
% 2.87/1.42  tff(c_490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_429, c_488])).
% 2.87/1.42  tff(c_491, plain, (v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_437])).
% 2.87/1.42  tff(c_496, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_491, c_8])).
% 2.87/1.42  tff(c_497, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_496])).
% 2.87/1.42  tff(c_500, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_497])).
% 2.87/1.42  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_500])).
% 2.87/1.42  tff(c_505, plain, (v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_496])).
% 2.87/1.42  tff(c_523, plain, (![A_104, B_105]: (m1_pre_topc(k1_tex_2(A_104, B_105), A_104) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.42  tff(c_525, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_523])).
% 2.87/1.42  tff(c_528, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_525])).
% 2.87/1.42  tff(c_529, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_528])).
% 2.87/1.42  tff(c_536, plain, (![B_106, A_107]: (~v1_tex_2(B_106, A_107) | v2_struct_0(B_106) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107) | ~v7_struct_0(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.42  tff(c_539, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_405, c_536])).
% 2.87/1.42  tff(c_542, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_505, c_42, c_529, c_539])).
% 2.87/1.42  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_429, c_542])).
% 2.87/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.42  
% 2.87/1.42  Inference rules
% 2.87/1.42  ----------------------
% 2.87/1.42  #Ref     : 0
% 2.87/1.42  #Sup     : 74
% 2.87/1.42  #Fact    : 0
% 2.87/1.42  #Define  : 0
% 2.87/1.42  #Split   : 13
% 2.87/1.42  #Chain   : 0
% 2.87/1.42  #Close   : 0
% 2.87/1.42  
% 2.87/1.42  Ordering : KBO
% 2.87/1.42  
% 2.87/1.42  Simplification rules
% 2.87/1.42  ----------------------
% 2.87/1.42  #Subsume      : 14
% 2.87/1.42  #Demod        : 70
% 2.87/1.42  #Tautology    : 13
% 2.87/1.42  #SimpNegUnit  : 29
% 2.87/1.42  #BackRed      : 1
% 2.87/1.42  
% 2.87/1.42  #Partial instantiations: 0
% 2.87/1.42  #Strategies tried      : 1
% 2.87/1.42  
% 2.87/1.42  Timing (in seconds)
% 2.87/1.42  ----------------------
% 2.87/1.42  Preprocessing        : 0.31
% 2.87/1.42  Parsing              : 0.17
% 2.87/1.42  CNF conversion       : 0.02
% 2.87/1.42  Main loop            : 0.33
% 2.87/1.42  Inferencing          : 0.13
% 2.87/1.42  Reduction            : 0.10
% 2.87/1.42  Demodulation         : 0.06
% 2.87/1.42  BG Simplification    : 0.02
% 2.87/1.42  Subsumption          : 0.06
% 2.87/1.42  Abstraction          : 0.01
% 2.87/1.42  MUC search           : 0.00
% 2.87/1.42  Cooper               : 0.00
% 2.87/1.42  Total                : 0.69
% 2.87/1.42  Index Insertion      : 0.00
% 2.87/1.42  Index Deletion       : 0.00
% 2.87/1.42  Index Matching       : 0.00
% 2.87/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

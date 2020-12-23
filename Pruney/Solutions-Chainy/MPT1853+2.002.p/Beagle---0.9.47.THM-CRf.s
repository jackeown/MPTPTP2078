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
% DateTime   : Thu Dec  3 10:29:00 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 234 expanded)
%              Number of leaves         :   34 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  258 ( 622 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_33,axiom,(
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

tff(f_129,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_98,axiom,(
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

tff(f_156,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_75,axiom,(
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

tff(f_108,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_56,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_378,plain,(
    ! [A_86,B_87] :
      ( ~ v2_struct_0(k1_tex_2(A_86,B_87))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_385,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_378])).

tff(c_389,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_385])).

tff(c_390,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_389])).

tff(c_288,plain,(
    ! [A_73,B_74] :
      ( ~ v2_struct_0(k1_tex_2(A_73,B_74))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_295,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_288])).

tff(c_299,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_295])).

tff(c_300,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_299])).

tff(c_301,plain,(
    ! [A_75,B_76] :
      ( m1_pre_topc(k1_tex_2(A_75,B_76),A_75)
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_306,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_301])).

tff(c_310,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_306])).

tff(c_311,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_310])).

tff(c_118,plain,(
    ! [A_43,B_44] :
      ( ~ v2_struct_0(k1_tex_2(A_43,B_44))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_125,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_118])).

tff(c_129,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_125])).

tff(c_130,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_129])).

tff(c_147,plain,(
    ! [A_47,B_48] :
      ( m1_pre_topc(k1_tex_2(A_47,B_48),A_47)
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_152,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_147])).

tff(c_156,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_152])).

tff(c_157,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_156])).

tff(c_133,plain,(
    ! [A_45,B_46] :
      ( v7_struct_0(k1_tex_2(A_45,B_46))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_140,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_133])).

tff(c_144,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_140])).

tff(c_145,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_144])).

tff(c_163,plain,(
    ! [B_53,A_54] :
      ( ~ v7_struct_0(B_53)
      | v1_tex_2(B_53,A_54)
      | v2_struct_0(B_53)
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54)
      | v7_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_67,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_132,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_50])).

tff(c_169,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_163,c_132])).

tff(c_173,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_157,c_145,c_169])).

tff(c_174,plain,(
    v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_130,c_173])).

tff(c_196,plain,(
    ! [A_59,B_60] :
      ( ~ v7_struct_0(A_59)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_59),B_60),u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_207,plain,
    ( ~ v7_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_196])).

tff(c_211,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_174,c_207])).

tff(c_212,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_211])).

tff(c_215,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_212])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_215])).

tff(c_220,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_312,plain,(
    ! [B_77,A_78] :
      ( ~ v1_tex_2(B_77,A_78)
      | v2_struct_0(B_77)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v7_struct_0(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_315,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_220,c_312])).

tff(c_318,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_311,c_315])).

tff(c_319,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_300,c_318])).

tff(c_248,plain,(
    ! [A_67,B_68] :
      ( v1_zfmisc_1(A_67)
      | k6_domain_1(A_67,B_68) != A_67
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_260,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') != u1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_248])).

tff(c_287,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_240,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k6_domain_1(A_65,B_66),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( v1_subset_1(B_18,A_17)
      | B_18 = A_17
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_345,plain,(
    ! [A_84,B_85] :
      ( v1_subset_1(k6_domain_1(A_84,B_85),A_84)
      | k6_domain_1(A_84,B_85) = A_84
      | ~ m1_subset_1(B_85,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_240,c_26])).

tff(c_221,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_348,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_345,c_221])).

tff(c_354,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_348])).

tff(c_355,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_354])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_29] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v7_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_29] :
      ( ~ l1_struct_0(A_29)
      | v7_struct_0(A_29)
      | ~ v1_xboole_0(u1_struct_0(A_29)) ) ),
    inference(resolution,[status(thm)],[c_2,c_59])).

tff(c_358,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_355,c_63])).

tff(c_364,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_358])).

tff(c_370,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_364])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_370])).

tff(c_375,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_377,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v7_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_394,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_377,c_8])).

tff(c_395,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_408,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_395])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_408])).

tff(c_413,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_425,plain,(
    ! [A_88,B_89] :
      ( m1_pre_topc(k1_tex_2(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_430,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_425])).

tff(c_434,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_430])).

tff(c_435,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_434])).

tff(c_468,plain,(
    ! [B_90,A_91] :
      ( ~ v1_tex_2(B_90,A_91)
      | v2_struct_0(B_90)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v7_struct_0(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_471,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_220,c_468])).

tff(c_474,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_46,c_435,c_471])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_390,c_474])).

tff(c_477,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_6,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_484,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_477,c_6])).

tff(c_488,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_484])).

tff(c_491,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_488])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:13:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.31  
% 2.27/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.31  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.27/1.31  
% 2.27/1.31  %Foreground sorts:
% 2.27/1.31  
% 2.27/1.31  
% 2.27/1.31  %Background operators:
% 2.27/1.31  
% 2.27/1.31  
% 2.27/1.31  %Foreground operators:
% 2.27/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.31  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.27/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.31  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.27/1.31  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.27/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.27/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.31  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.27/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.31  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.31  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.27/1.31  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.27/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.31  
% 2.70/1.33  tff(f_169, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.70/1.33  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.70/1.33  tff(f_143, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.70/1.33  tff(f_129, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.70/1.33  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v1_tex_2(B, A)) => (~v2_struct_0(B) & ~v7_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc13_tex_2)).
% 2.70/1.33  tff(f_156, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.70/1.33  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.70/1.33  tff(f_108, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.70/1.33  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.70/1.33  tff(f_115, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.70/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.70/1.33  tff(f_49, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.70/1.33  tff(f_41, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.70/1.33  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.70/1.33  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.33  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.70/1.33  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.70/1.33  tff(c_378, plain, (![A_86, B_87]: (~v2_struct_0(k1_tex_2(A_86, B_87)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.70/1.33  tff(c_385, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_378])).
% 2.70/1.33  tff(c_389, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_385])).
% 2.70/1.33  tff(c_390, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_389])).
% 2.70/1.33  tff(c_288, plain, (![A_73, B_74]: (~v2_struct_0(k1_tex_2(A_73, B_74)) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.70/1.33  tff(c_295, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_288])).
% 2.70/1.33  tff(c_299, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_295])).
% 2.70/1.33  tff(c_300, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_299])).
% 2.70/1.33  tff(c_301, plain, (![A_75, B_76]: (m1_pre_topc(k1_tex_2(A_75, B_76), A_75) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.70/1.33  tff(c_306, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_301])).
% 2.70/1.33  tff(c_310, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_306])).
% 2.70/1.33  tff(c_311, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_310])).
% 2.70/1.33  tff(c_118, plain, (![A_43, B_44]: (~v2_struct_0(k1_tex_2(A_43, B_44)) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.70/1.33  tff(c_125, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_118])).
% 2.70/1.33  tff(c_129, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_125])).
% 2.70/1.33  tff(c_130, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_129])).
% 2.70/1.33  tff(c_147, plain, (![A_47, B_48]: (m1_pre_topc(k1_tex_2(A_47, B_48), A_47) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.70/1.33  tff(c_152, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_147])).
% 2.70/1.33  tff(c_156, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_152])).
% 2.70/1.33  tff(c_157, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_156])).
% 2.70/1.33  tff(c_133, plain, (![A_45, B_46]: (v7_struct_0(k1_tex_2(A_45, B_46)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.70/1.33  tff(c_140, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_133])).
% 2.70/1.33  tff(c_144, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_140])).
% 2.70/1.33  tff(c_145, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_144])).
% 2.70/1.33  tff(c_163, plain, (![B_53, A_54]: (~v7_struct_0(B_53) | v1_tex_2(B_53, A_54) | v2_struct_0(B_53) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54) | v7_struct_0(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.70/1.33  tff(c_56, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.70/1.33  tff(c_67, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.70/1.33  tff(c_50, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.70/1.33  tff(c_132, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_50])).
% 2.70/1.33  tff(c_169, plain, (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_163, c_132])).
% 2.70/1.33  tff(c_173, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_157, c_145, c_169])).
% 2.70/1.33  tff(c_174, plain, (v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_130, c_173])).
% 2.70/1.33  tff(c_196, plain, (![A_59, B_60]: (~v7_struct_0(A_59) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_59), B_60), u1_struct_0(A_59)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.70/1.33  tff(c_207, plain, (~v7_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_67, c_196])).
% 2.70/1.33  tff(c_211, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_174, c_207])).
% 2.70/1.33  tff(c_212, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_211])).
% 2.70/1.33  tff(c_215, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_212])).
% 2.70/1.33  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_215])).
% 2.70/1.33  tff(c_220, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 2.70/1.33  tff(c_312, plain, (![B_77, A_78]: (~v1_tex_2(B_77, A_78) | v2_struct_0(B_77) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(A_78) | ~v7_struct_0(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.70/1.33  tff(c_315, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_220, c_312])).
% 2.70/1.33  tff(c_318, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_311, c_315])).
% 2.70/1.33  tff(c_319, plain, (~v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_300, c_318])).
% 2.70/1.33  tff(c_248, plain, (![A_67, B_68]: (v1_zfmisc_1(A_67) | k6_domain_1(A_67, B_68)!=A_67 | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.70/1.33  tff(c_260, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')!=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_248])).
% 2.70/1.33  tff(c_287, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')!=u1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_260])).
% 2.70/1.33  tff(c_240, plain, (![A_65, B_66]: (m1_subset_1(k6_domain_1(A_65, B_66), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.33  tff(c_26, plain, (![B_18, A_17]: (v1_subset_1(B_18, A_17) | B_18=A_17 | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.70/1.33  tff(c_345, plain, (![A_84, B_85]: (v1_subset_1(k6_domain_1(A_84, B_85), A_84) | k6_domain_1(A_84, B_85)=A_84 | ~m1_subset_1(B_85, A_84) | v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_240, c_26])).
% 2.70/1.33  tff(c_221, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 2.70/1.33  tff(c_348, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_345, c_221])).
% 2.70/1.33  tff(c_354, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_348])).
% 2.70/1.33  tff(c_355, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_287, c_354])).
% 2.70/1.33  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.33  tff(c_59, plain, (![A_29]: (~v1_zfmisc_1(u1_struct_0(A_29)) | ~l1_struct_0(A_29) | v7_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.33  tff(c_63, plain, (![A_29]: (~l1_struct_0(A_29) | v7_struct_0(A_29) | ~v1_xboole_0(u1_struct_0(A_29)))), inference(resolution, [status(thm)], [c_2, c_59])).
% 2.70/1.33  tff(c_358, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_355, c_63])).
% 2.70/1.33  tff(c_364, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_319, c_358])).
% 2.70/1.33  tff(c_370, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_364])).
% 2.70/1.33  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_370])).
% 2.70/1.33  tff(c_375, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_260])).
% 2.70/1.33  tff(c_377, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_375])).
% 2.70/1.33  tff(c_8, plain, (![A_4]: (~v1_zfmisc_1(u1_struct_0(A_4)) | ~l1_struct_0(A_4) | v7_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.33  tff(c_394, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_377, c_8])).
% 2.70/1.33  tff(c_395, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_394])).
% 2.70/1.33  tff(c_408, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_395])).
% 2.70/1.33  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_408])).
% 2.70/1.33  tff(c_413, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_394])).
% 2.70/1.33  tff(c_425, plain, (![A_88, B_89]: (m1_pre_topc(k1_tex_2(A_88, B_89), A_88) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.70/1.33  tff(c_430, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_425])).
% 2.70/1.33  tff(c_434, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_430])).
% 2.70/1.33  tff(c_435, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_434])).
% 2.70/1.33  tff(c_468, plain, (![B_90, A_91]: (~v1_tex_2(B_90, A_91) | v2_struct_0(B_90) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91) | ~v7_struct_0(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.70/1.33  tff(c_471, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_220, c_468])).
% 2.70/1.33  tff(c_474, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_46, c_435, c_471])).
% 2.70/1.33  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_390, c_474])).
% 2.70/1.33  tff(c_477, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_375])).
% 2.70/1.33  tff(c_6, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.33  tff(c_484, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_477, c_6])).
% 2.70/1.33  tff(c_488, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_484])).
% 2.70/1.33  tff(c_491, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_488])).
% 2.70/1.33  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_491])).
% 2.70/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.33  
% 2.70/1.33  Inference rules
% 2.70/1.33  ----------------------
% 2.70/1.33  #Ref     : 0
% 2.70/1.33  #Sup     : 76
% 2.70/1.33  #Fact    : 0
% 2.70/1.33  #Define  : 0
% 2.70/1.33  #Split   : 6
% 2.70/1.33  #Chain   : 0
% 2.70/1.33  #Close   : 0
% 2.70/1.33  
% 2.70/1.33  Ordering : KBO
% 2.70/1.33  
% 2.70/1.33  Simplification rules
% 2.70/1.33  ----------------------
% 2.70/1.33  #Subsume      : 9
% 2.70/1.33  #Demod        : 34
% 2.70/1.33  #Tautology    : 20
% 2.70/1.33  #SimpNegUnit  : 20
% 2.70/1.33  #BackRed      : 2
% 2.70/1.33  
% 2.70/1.33  #Partial instantiations: 0
% 2.70/1.33  #Strategies tried      : 1
% 2.70/1.33  
% 2.70/1.33  Timing (in seconds)
% 2.70/1.33  ----------------------
% 2.70/1.34  Preprocessing        : 0.30
% 2.70/1.34  Parsing              : 0.17
% 2.70/1.34  CNF conversion       : 0.02
% 2.70/1.34  Main loop            : 0.27
% 2.70/1.34  Inferencing          : 0.11
% 2.70/1.34  Reduction            : 0.07
% 2.70/1.34  Demodulation         : 0.05
% 2.70/1.34  BG Simplification    : 0.02
% 2.70/1.34  Subsumption          : 0.04
% 2.70/1.34  Abstraction          : 0.01
% 2.70/1.34  MUC search           : 0.00
% 2.70/1.34  Cooper               : 0.00
% 2.70/1.34  Total                : 0.61
% 2.70/1.34  Index Insertion      : 0.00
% 2.70/1.34  Index Deletion       : 0.00
% 2.70/1.34  Index Matching       : 0.00
% 2.70/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

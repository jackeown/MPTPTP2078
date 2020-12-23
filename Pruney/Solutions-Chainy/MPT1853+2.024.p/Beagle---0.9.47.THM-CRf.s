%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:03 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 388 expanded)
%              Number of leaves         :   29 ( 142 expanded)
%              Depth                    :   13
%              Number of atoms          :  210 (1136 expanded)
%              Number of equality atoms :   11 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_69,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_55,axiom,(
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

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_349,plain,(
    ! [A_78,B_79] :
      ( m1_pre_topc(k1_tex_2(A_78,B_79),A_78)
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_351,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_349])).

tff(c_354,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_351])).

tff(c_355,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_354])).

tff(c_330,plain,(
    ! [A_72,B_73] :
      ( ~ v2_struct_0(k1_tex_2(A_72,B_73))
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_333,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_330])).

tff(c_336,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_333])).

tff(c_337,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_336])).

tff(c_50,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_63,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_89,plain,(
    ! [A_45,B_46] :
      ( m1_pre_topc(k1_tex_2(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_91,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_94,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_91])).

tff(c_95,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_94])).

tff(c_144,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1('#skF_1'(A_53,B_54),k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_tex_2(B_54,A_53)
      | ~ m1_pre_topc(B_54,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( v1_subset_1(B_19,A_18)
      | B_19 = A_18
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_252,plain,(
    ! [A_67,B_68] :
      ( v1_subset_1('#skF_1'(A_67,B_68),u1_struct_0(A_67))
      | u1_struct_0(A_67) = '#skF_1'(A_67,B_68)
      | v1_tex_2(B_68,A_67)
      | ~ m1_pre_topc(B_68,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_144,c_18])).

tff(c_12,plain,(
    ! [A_8,B_14] :
      ( ~ v1_subset_1('#skF_1'(A_8,B_14),u1_struct_0(A_8))
      | v1_tex_2(B_14,A_8)
      | ~ m1_pre_topc(B_14,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_277,plain,(
    ! [A_69,B_70] :
      ( u1_struct_0(A_69) = '#skF_1'(A_69,B_70)
      | v1_tex_2(B_70,A_69)
      | ~ m1_pre_topc(B_70,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_252,c_12])).

tff(c_44,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_81,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_44])).

tff(c_283,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_277,c_81])).

tff(c_287,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_95,c_283])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_101,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( ~ v2_struct_0(k1_tex_2(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_67,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_70,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_67])).

tff(c_71,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_70])).

tff(c_82,plain,(
    ! [B_43,A_44] :
      ( u1_struct_0(B_43) = '#skF_1'(A_44,B_43)
      | v1_tex_2(B_43,A_44)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_85,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_81])).

tff(c_88,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_85])).

tff(c_109,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_88])).

tff(c_72,plain,(
    ! [A_41,B_42] :
      ( v7_struct_0(k1_tex_2(A_41,B_42))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_75,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_72])).

tff(c_78,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_75])).

tff(c_79,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_78])).

tff(c_208,plain,(
    ! [A_63,B_64] :
      ( ~ v7_struct_0(A_63)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_63),B_64),u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_214,plain,(
    ! [B_64] :
      ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ v1_subset_1(k6_domain_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),B_64),u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_64,u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_208])).

tff(c_223,plain,(
    ! [B_64] :
      ( ~ v1_subset_1(k6_domain_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),B_64),'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_64,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_109,c_79,c_214])).

tff(c_224,plain,(
    ! [B_64] :
      ( ~ v1_subset_1(k6_domain_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),B_64),'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_64,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_223])).

tff(c_267,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_270,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_267])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_270])).

tff(c_275,plain,(
    ! [B_64] :
      ( ~ v1_subset_1(k6_domain_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),B_64),'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_64,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_312,plain,(
    ! [B_71] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),B_71),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_287,c_287,c_275])).

tff(c_319,plain,(
    ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_63,c_312])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_319])).

tff(c_328,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_356,plain,(
    ! [B_80,A_81] :
      ( ~ v1_tex_2(B_80,A_81)
      | v2_struct_0(B_80)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81)
      | ~ v7_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_362,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_328,c_356])).

tff(c_366,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_362])).

tff(c_367,plain,
    ( ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_337,c_366])).

tff(c_375,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_367])).

tff(c_390,plain,(
    ! [A_88,B_89] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(A_88),B_89),u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_struct_0(A_88)
      | v7_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_329,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_393,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_390,c_329])).

tff(c_396,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_393])).

tff(c_397,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_375,c_396])).

tff(c_400,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_397])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.33  
% 2.61/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.33  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.33  
% 2.61/1.33  %Foreground sorts:
% 2.61/1.33  
% 2.61/1.33  
% 2.61/1.33  %Background operators:
% 2.61/1.33  
% 2.61/1.33  
% 2.61/1.33  %Foreground operators:
% 2.61/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.61/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.61/1.33  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.61/1.33  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.61/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.61/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.61/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.33  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.61/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.61/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.33  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.61/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.61/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.33  
% 2.61/1.35  tff(f_143, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.61/1.35  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.61/1.35  tff(f_90, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.61/1.35  tff(f_104, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.61/1.35  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.61/1.35  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.61/1.35  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.61/1.35  tff(f_117, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.61/1.35  tff(f_55, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.61/1.35  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 2.61/1.35  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.61/1.35  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.35  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.61/1.35  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.61/1.35  tff(c_349, plain, (![A_78, B_79]: (m1_pre_topc(k1_tex_2(A_78, B_79), A_78) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.61/1.35  tff(c_351, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_349])).
% 2.61/1.35  tff(c_354, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_351])).
% 2.61/1.35  tff(c_355, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_354])).
% 2.61/1.35  tff(c_330, plain, (![A_72, B_73]: (~v2_struct_0(k1_tex_2(A_72, B_73)) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.61/1.35  tff(c_333, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_330])).
% 2.61/1.35  tff(c_336, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_333])).
% 2.61/1.35  tff(c_337, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_336])).
% 2.61/1.35  tff(c_50, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.61/1.35  tff(c_63, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.61/1.35  tff(c_89, plain, (![A_45, B_46]: (m1_pre_topc(k1_tex_2(A_45, B_46), A_45) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.61/1.35  tff(c_91, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_89])).
% 2.61/1.35  tff(c_94, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_91])).
% 2.61/1.35  tff(c_95, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_94])).
% 2.61/1.35  tff(c_144, plain, (![A_53, B_54]: (m1_subset_1('#skF_1'(A_53, B_54), k1_zfmisc_1(u1_struct_0(A_53))) | v1_tex_2(B_54, A_53) | ~m1_pre_topc(B_54, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.35  tff(c_18, plain, (![B_19, A_18]: (v1_subset_1(B_19, A_18) | B_19=A_18 | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.61/1.35  tff(c_252, plain, (![A_67, B_68]: (v1_subset_1('#skF_1'(A_67, B_68), u1_struct_0(A_67)) | u1_struct_0(A_67)='#skF_1'(A_67, B_68) | v1_tex_2(B_68, A_67) | ~m1_pre_topc(B_68, A_67) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_144, c_18])).
% 2.61/1.35  tff(c_12, plain, (![A_8, B_14]: (~v1_subset_1('#skF_1'(A_8, B_14), u1_struct_0(A_8)) | v1_tex_2(B_14, A_8) | ~m1_pre_topc(B_14, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.35  tff(c_277, plain, (![A_69, B_70]: (u1_struct_0(A_69)='#skF_1'(A_69, B_70) | v1_tex_2(B_70, A_69) | ~m1_pre_topc(B_70, A_69) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_252, c_12])).
% 2.61/1.35  tff(c_44, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.61/1.35  tff(c_81, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_44])).
% 2.61/1.35  tff(c_283, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_277, c_81])).
% 2.61/1.35  tff(c_287, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_95, c_283])).
% 2.61/1.35  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.61/1.35  tff(c_98, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_95, c_4])).
% 2.61/1.35  tff(c_101, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98])).
% 2.61/1.35  tff(c_64, plain, (![A_39, B_40]: (~v2_struct_0(k1_tex_2(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.61/1.35  tff(c_67, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_64])).
% 2.61/1.35  tff(c_70, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_67])).
% 2.61/1.35  tff(c_71, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_70])).
% 2.61/1.35  tff(c_82, plain, (![B_43, A_44]: (u1_struct_0(B_43)='#skF_1'(A_44, B_43) | v1_tex_2(B_43, A_44) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.35  tff(c_85, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_82, c_81])).
% 2.61/1.35  tff(c_88, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_85])).
% 2.61/1.35  tff(c_109, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_88])).
% 2.61/1.35  tff(c_72, plain, (![A_41, B_42]: (v7_struct_0(k1_tex_2(A_41, B_42)) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.61/1.35  tff(c_75, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_72])).
% 2.61/1.35  tff(c_78, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_75])).
% 2.61/1.35  tff(c_79, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_78])).
% 2.61/1.35  tff(c_208, plain, (![A_63, B_64]: (~v7_struct_0(A_63) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_63), B_64), u1_struct_0(A_63)) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_struct_0(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.61/1.35  tff(c_214, plain, (![B_64]: (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_subset_1(k6_domain_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), B_64), u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_64, u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_109, c_208])).
% 2.61/1.35  tff(c_223, plain, (![B_64]: (~v1_subset_1(k6_domain_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), B_64), '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_64, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_109, c_79, c_214])).
% 2.61/1.35  tff(c_224, plain, (![B_64]: (~v1_subset_1(k6_domain_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), B_64), '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_64, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_71, c_223])).
% 2.61/1.35  tff(c_267, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_224])).
% 2.61/1.35  tff(c_270, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_267])).
% 2.61/1.35  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_270])).
% 2.61/1.35  tff(c_275, plain, (![B_64]: (~v1_subset_1(k6_domain_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), B_64), '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_64, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))))), inference(splitRight, [status(thm)], [c_224])).
% 2.61/1.35  tff(c_312, plain, (![B_71]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), B_71), u1_struct_0('#skF_2')) | ~m1_subset_1(B_71, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_287, c_287, c_275])).
% 2.61/1.35  tff(c_319, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_63, c_312])).
% 2.61/1.35  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_319])).
% 2.61/1.35  tff(c_328, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 2.61/1.35  tff(c_356, plain, (![B_80, A_81]: (~v1_tex_2(B_80, A_81) | v2_struct_0(B_80) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81) | ~v7_struct_0(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.35  tff(c_362, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_328, c_356])).
% 2.61/1.35  tff(c_366, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_362])).
% 2.61/1.35  tff(c_367, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_337, c_366])).
% 2.61/1.35  tff(c_375, plain, (~v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_367])).
% 2.61/1.35  tff(c_390, plain, (![A_88, B_89]: (v1_subset_1(k6_domain_1(u1_struct_0(A_88), B_89), u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_struct_0(A_88) | v7_struct_0(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.61/1.35  tff(c_329, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 2.61/1.35  tff(c_393, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_390, c_329])).
% 2.61/1.35  tff(c_396, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_393])).
% 2.61/1.35  tff(c_397, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_375, c_396])).
% 2.61/1.35  tff(c_400, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_397])).
% 2.61/1.35  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_400])).
% 2.61/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  Inference rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Ref     : 0
% 2.61/1.35  #Sup     : 54
% 2.61/1.35  #Fact    : 0
% 2.61/1.35  #Define  : 0
% 2.61/1.35  #Split   : 3
% 2.61/1.35  #Chain   : 0
% 2.61/1.35  #Close   : 0
% 2.61/1.35  
% 2.61/1.35  Ordering : KBO
% 2.61/1.35  
% 2.61/1.35  Simplification rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Subsume      : 5
% 2.61/1.35  #Demod        : 74
% 2.61/1.35  #Tautology    : 13
% 2.61/1.35  #SimpNegUnit  : 24
% 2.61/1.35  #BackRed      : 7
% 2.61/1.35  
% 2.61/1.35  #Partial instantiations: 0
% 2.61/1.35  #Strategies tried      : 1
% 2.61/1.35  
% 2.61/1.35  Timing (in seconds)
% 2.61/1.35  ----------------------
% 2.61/1.35  Preprocessing        : 0.31
% 2.61/1.35  Parsing              : 0.16
% 2.61/1.35  CNF conversion       : 0.02
% 2.61/1.35  Main loop            : 0.24
% 2.61/1.35  Inferencing          : 0.09
% 2.61/1.35  Reduction            : 0.08
% 2.61/1.35  Demodulation         : 0.05
% 2.61/1.35  BG Simplification    : 0.02
% 2.61/1.35  Subsumption          : 0.04
% 2.61/1.35  Abstraction          : 0.02
% 2.61/1.35  MUC search           : 0.00
% 2.61/1.35  Cooper               : 0.00
% 2.61/1.35  Total                : 0.59
% 2.61/1.35  Index Insertion      : 0.00
% 2.61/1.35  Index Deletion       : 0.00
% 2.61/1.35  Index Matching       : 0.00
% 2.61/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

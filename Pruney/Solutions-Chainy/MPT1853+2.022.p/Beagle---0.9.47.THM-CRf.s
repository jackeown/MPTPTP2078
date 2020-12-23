%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:03 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 312 expanded)
%              Number of leaves         :   34 ( 116 expanded)
%              Depth                    :   11
%              Number of atoms          :  234 ( 833 expanded)
%              Number of equality atoms :   10 (  20 expanded)
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

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_137,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_91,axiom,(
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

tff(f_98,axiom,(
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

tff(f_77,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_291,plain,(
    ! [A_78,B_79] :
      ( ~ v2_struct_0(k1_tex_2(A_78,B_79))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_294,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_291])).

tff(c_297,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_294])).

tff(c_298,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_297])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_317,plain,(
    ! [A_84,B_85] :
      ( v1_subset_1(k6_domain_1(A_84,B_85),A_84)
      | ~ m1_subset_1(B_85,A_84)
      | v1_zfmisc_1(A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_56,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_67,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_96,plain,(
    ! [A_51,B_52] :
      ( ~ v1_zfmisc_1(A_51)
      | ~ v1_subset_1(k6_domain_1(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_102,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_67,c_96])).

tff(c_106,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_102])).

tff(c_107,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_113,plain,(
    ! [A_53,B_54] :
      ( m1_pre_topc(k1_tex_2(A_53,B_54),A_53)
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ l1_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_115,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_113])).

tff(c_118,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_115])).

tff(c_119,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_118])).

tff(c_207,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1('#skF_1'(A_66,B_67),k1_zfmisc_1(u1_struct_0(A_66)))
      | v1_tex_2(B_67,A_66)
      | ~ m1_pre_topc(B_67,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( v1_subset_1(B_22,A_21)
      | B_22 = A_21
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_242,plain,(
    ! [A_72,B_73] :
      ( v1_subset_1('#skF_1'(A_72,B_73),u1_struct_0(A_72))
      | u1_struct_0(A_72) = '#skF_1'(A_72,B_73)
      | v1_tex_2(B_73,A_72)
      | ~ m1_pre_topc(B_73,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_207,c_24])).

tff(c_18,plain,(
    ! [A_11,B_17] :
      ( ~ v1_subset_1('#skF_1'(A_11,B_17),u1_struct_0(A_11))
      | v1_tex_2(B_17,A_11)
      | ~ m1_pre_topc(B_17,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_252,plain,(
    ! [A_74,B_75] :
      ( u1_struct_0(A_74) = '#skF_1'(A_74,B_75)
      | v1_tex_2(B_75,A_74)
      | ~ m1_pre_topc(B_75,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_242,c_18])).

tff(c_50,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_95,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_50])).

tff(c_258,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_252,c_95])).

tff(c_262,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_119,c_258])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_122,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_119,c_4])).

tff(c_125,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_122])).

tff(c_69,plain,(
    ! [A_43,B_44] :
      ( ~ v2_struct_0(k1_tex_2(A_43,B_44))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_72,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_75,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_72])).

tff(c_76,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_75])).

tff(c_126,plain,(
    ! [B_55,A_56] :
      ( u1_struct_0(B_55) = '#skF_1'(A_56,B_55)
      | v1_tex_2(B_55,A_56)
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_129,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_126,c_95])).

tff(c_132,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_119,c_129])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_147,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_6])).

tff(c_168,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_147])).

tff(c_173,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_176,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_176])).

tff(c_182,plain,(
    l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_85,plain,(
    ! [A_47,B_48] :
      ( v7_struct_0(k1_tex_2(A_47,B_48))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_88,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_85])).

tff(c_91,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_88])).

tff(c_92,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_91])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_zfmisc_1(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | ~ v7_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_153,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_10])).

tff(c_171,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_153])).

tff(c_184,plain,(
    v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_171])).

tff(c_268,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_184])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_268])).

tff(c_273,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_277,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_273,c_6])).

tff(c_280,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_277])).

tff(c_283,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_280])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_283])).

tff(c_289,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_320,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_317,c_289])).

tff(c_323,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_320])).

tff(c_324,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_327,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_324,c_6])).

tff(c_330,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_327])).

tff(c_333,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_330])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_333])).

tff(c_338,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_343,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_338,c_8])).

tff(c_349,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_352,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_349])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_352])).

tff(c_357,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_359,plain,(
    ! [A_88,B_89] :
      ( m1_pre_topc(k1_tex_2(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_361,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_359])).

tff(c_364,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_361])).

tff(c_365,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_364])).

tff(c_288,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_373,plain,(
    ! [B_92,A_93] :
      ( ~ v1_tex_2(B_92,A_93)
      | v2_struct_0(B_92)
      | ~ m1_pre_topc(B_92,A_93)
      | ~ l1_pre_topc(A_93)
      | ~ v7_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_379,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_288,c_373])).

tff(c_383,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_46,c_365,c_379])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_298,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.36  
% 2.43/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.36  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.43/1.36  
% 2.43/1.36  %Foreground sorts:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Background operators:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Foreground operators:
% 2.43/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.36  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.43/1.36  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.43/1.36  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.43/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.43/1.36  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.43/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.36  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.43/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.36  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.36  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.43/1.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.43/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.36  
% 2.73/1.38  tff(f_161, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.73/1.38  tff(f_126, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.73/1.38  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.73/1.38  tff(f_148, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 2.73/1.38  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.73/1.38  tff(f_112, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.73/1.38  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.73/1.38  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.73/1.38  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.73/1.38  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.73/1.38  tff(f_58, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.73/1.38  tff(f_52, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.73/1.38  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.73/1.38  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.73/1.38  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.73/1.38  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.73/1.38  tff(c_291, plain, (![A_78, B_79]: (~v2_struct_0(k1_tex_2(A_78, B_79)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.38  tff(c_294, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_291])).
% 2.73/1.38  tff(c_297, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_294])).
% 2.73/1.38  tff(c_298, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_297])).
% 2.73/1.38  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.38  tff(c_317, plain, (![A_84, B_85]: (v1_subset_1(k6_domain_1(A_84, B_85), A_84) | ~m1_subset_1(B_85, A_84) | v1_zfmisc_1(A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.73/1.38  tff(c_56, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.73/1.38  tff(c_67, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.73/1.38  tff(c_96, plain, (![A_51, B_52]: (~v1_zfmisc_1(A_51) | ~v1_subset_1(k6_domain_1(A_51, B_52), A_51) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.73/1.38  tff(c_102, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_67, c_96])).
% 2.73/1.38  tff(c_106, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_102])).
% 2.73/1.38  tff(c_107, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_106])).
% 2.73/1.38  tff(c_113, plain, (![A_53, B_54]: (m1_pre_topc(k1_tex_2(A_53, B_54), A_53) | ~m1_subset_1(B_54, u1_struct_0(A_53)) | ~l1_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.73/1.38  tff(c_115, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_113])).
% 2.73/1.38  tff(c_118, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_115])).
% 2.73/1.38  tff(c_119, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_118])).
% 2.73/1.38  tff(c_207, plain, (![A_66, B_67]: (m1_subset_1('#skF_1'(A_66, B_67), k1_zfmisc_1(u1_struct_0(A_66))) | v1_tex_2(B_67, A_66) | ~m1_pre_topc(B_67, A_66) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.38  tff(c_24, plain, (![B_22, A_21]: (v1_subset_1(B_22, A_21) | B_22=A_21 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.73/1.38  tff(c_242, plain, (![A_72, B_73]: (v1_subset_1('#skF_1'(A_72, B_73), u1_struct_0(A_72)) | u1_struct_0(A_72)='#skF_1'(A_72, B_73) | v1_tex_2(B_73, A_72) | ~m1_pre_topc(B_73, A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_207, c_24])).
% 2.73/1.38  tff(c_18, plain, (![A_11, B_17]: (~v1_subset_1('#skF_1'(A_11, B_17), u1_struct_0(A_11)) | v1_tex_2(B_17, A_11) | ~m1_pre_topc(B_17, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.38  tff(c_252, plain, (![A_74, B_75]: (u1_struct_0(A_74)='#skF_1'(A_74, B_75) | v1_tex_2(B_75, A_74) | ~m1_pre_topc(B_75, A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_242, c_18])).
% 2.73/1.38  tff(c_50, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.73/1.38  tff(c_95, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_50])).
% 2.73/1.38  tff(c_258, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_252, c_95])).
% 2.73/1.38  tff(c_262, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_119, c_258])).
% 2.73/1.38  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.73/1.38  tff(c_122, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_119, c_4])).
% 2.73/1.38  tff(c_125, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_122])).
% 2.73/1.38  tff(c_69, plain, (![A_43, B_44]: (~v2_struct_0(k1_tex_2(A_43, B_44)) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.38  tff(c_72, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_69])).
% 2.73/1.38  tff(c_75, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_72])).
% 2.73/1.38  tff(c_76, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_75])).
% 2.73/1.38  tff(c_126, plain, (![B_55, A_56]: (u1_struct_0(B_55)='#skF_1'(A_56, B_55) | v1_tex_2(B_55, A_56) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.38  tff(c_129, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_126, c_95])).
% 2.73/1.38  tff(c_132, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_119, c_129])).
% 2.73/1.38  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.73/1.38  tff(c_147, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_6])).
% 2.73/1.38  tff(c_168, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_147])).
% 2.73/1.38  tff(c_173, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_168])).
% 2.73/1.38  tff(c_176, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_173])).
% 2.73/1.38  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_176])).
% 2.73/1.38  tff(c_182, plain, (l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_168])).
% 2.73/1.38  tff(c_85, plain, (![A_47, B_48]: (v7_struct_0(k1_tex_2(A_47, B_48)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.38  tff(c_88, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_85])).
% 2.73/1.38  tff(c_91, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_88])).
% 2.73/1.38  tff(c_92, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_91])).
% 2.73/1.38  tff(c_10, plain, (![A_7]: (v1_zfmisc_1(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | ~v7_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.38  tff(c_153, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_10])).
% 2.73/1.38  tff(c_171, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_153])).
% 2.73/1.38  tff(c_184, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_171])).
% 2.73/1.38  tff(c_268, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_184])).
% 2.73/1.38  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_268])).
% 2.73/1.38  tff(c_273, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_106])).
% 2.73/1.38  tff(c_277, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_273, c_6])).
% 2.73/1.38  tff(c_280, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_277])).
% 2.73/1.38  tff(c_283, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_280])).
% 2.73/1.38  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_283])).
% 2.73/1.38  tff(c_289, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 2.73/1.38  tff(c_320, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_317, c_289])).
% 2.73/1.38  tff(c_323, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_320])).
% 2.73/1.38  tff(c_324, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_323])).
% 2.73/1.38  tff(c_327, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_324, c_6])).
% 2.73/1.38  tff(c_330, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_327])).
% 2.73/1.38  tff(c_333, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_330])).
% 2.73/1.38  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_333])).
% 2.73/1.38  tff(c_338, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_323])).
% 2.73/1.38  tff(c_8, plain, (![A_6]: (~v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.38  tff(c_343, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_338, c_8])).
% 2.73/1.38  tff(c_349, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_343])).
% 2.73/1.38  tff(c_352, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_349])).
% 2.73/1.38  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_352])).
% 2.73/1.38  tff(c_357, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_343])).
% 2.73/1.38  tff(c_359, plain, (![A_88, B_89]: (m1_pre_topc(k1_tex_2(A_88, B_89), A_88) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.73/1.38  tff(c_361, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_359])).
% 2.73/1.38  tff(c_364, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_361])).
% 2.73/1.38  tff(c_365, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_364])).
% 2.73/1.38  tff(c_288, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 2.73/1.38  tff(c_373, plain, (![B_92, A_93]: (~v1_tex_2(B_92, A_93) | v2_struct_0(B_92) | ~m1_pre_topc(B_92, A_93) | ~l1_pre_topc(A_93) | ~v7_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.73/1.38  tff(c_379, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_288, c_373])).
% 2.73/1.38  tff(c_383, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_46, c_365, c_379])).
% 2.73/1.38  tff(c_385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_298, c_383])).
% 2.73/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  Inference rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Ref     : 0
% 2.73/1.38  #Sup     : 48
% 2.73/1.38  #Fact    : 0
% 2.73/1.38  #Define  : 0
% 2.73/1.38  #Split   : 6
% 2.73/1.38  #Chain   : 0
% 2.73/1.38  #Close   : 0
% 2.73/1.38  
% 2.73/1.38  Ordering : KBO
% 2.73/1.38  
% 2.73/1.38  Simplification rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Subsume      : 5
% 2.73/1.38  #Demod        : 52
% 2.73/1.38  #Tautology    : 9
% 2.73/1.38  #SimpNegUnit  : 19
% 2.73/1.38  #BackRed      : 8
% 2.73/1.38  
% 2.73/1.38  #Partial instantiations: 0
% 2.73/1.38  #Strategies tried      : 1
% 2.73/1.38  
% 2.73/1.38  Timing (in seconds)
% 2.73/1.38  ----------------------
% 2.73/1.38  Preprocessing        : 0.33
% 2.73/1.38  Parsing              : 0.17
% 2.73/1.38  CNF conversion       : 0.02
% 2.73/1.38  Main loop            : 0.24
% 2.73/1.38  Inferencing          : 0.09
% 2.73/1.38  Reduction            : 0.07
% 2.73/1.38  Demodulation         : 0.05
% 2.73/1.38  BG Simplification    : 0.02
% 2.73/1.38  Subsumption          : 0.04
% 2.73/1.38  Abstraction          : 0.01
% 2.73/1.38  MUC search           : 0.00
% 2.73/1.38  Cooper               : 0.00
% 2.73/1.38  Total                : 0.61
% 2.73/1.38  Index Insertion      : 0.00
% 2.73/1.38  Index Deletion       : 0.00
% 2.73/1.38  Index Matching       : 0.00
% 2.73/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:51 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 521 expanded)
%              Number of leaves         :   31 ( 201 expanded)
%              Depth                    :   14
%              Number of atoms          :  334 (2132 expanded)
%              Number of equality atoms :   14 (  52 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & v2_pre_topc(B) )
           => ( ~ v2_struct_0(B)
              & v1_tdlat_3(B)
              & v2_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_378,plain,(
    ! [A_80,B_81] :
      ( m1_pre_topc('#skF_1'(A_80,B_81),A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | v1_xboole_0(B_81)
      | ~ l1_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_380,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_378])).

tff(c_383,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_380])).

tff(c_384,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_383])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_422,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_384,c_6])).

tff(c_436,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_422])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_56,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46])).

tff(c_83,plain,(
    ! [A_45,B_46] :
      ( m1_pre_topc('#skF_1'(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | v1_xboole_0(B_46)
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_85,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_83])).

tff(c_88,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_85])).

tff(c_89,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_88])).

tff(c_75,plain,(
    ! [A_43,B_44] :
      ( ~ v2_struct_0('#skF_1'(A_43,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | v1_xboole_0(B_44)
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_78,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_75])).

tff(c_81,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_78])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_81])).

tff(c_101,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_6])).

tff(c_115,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_101])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_112,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_98])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( v1_tdlat_3(B_12)
      | ~ v2_pre_topc(B_12)
      | ~ v7_struct_0(B_12)
      | v2_struct_0(B_12)
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_95,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_14])).

tff(c_108,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_95])).

tff(c_109,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_82,c_108])).

tff(c_117,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_109])).

tff(c_118,plain,(
    ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_119,plain,(
    ! [A_47,B_48] :
      ( u1_struct_0('#skF_1'(A_47,B_48)) = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | v1_xboole_0(B_48)
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_122,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_119])).

tff(c_125,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_122])).

tff(c_126,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_125])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_144,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_8])).

tff(c_161,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_144])).

tff(c_162,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_161])).

tff(c_166,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_166])).

tff(c_171,plain,(
    v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_179,plain,(
    ! [A_49,B_50] :
      ( u1_struct_0('#skF_1'(A_49,B_50)) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | v1_xboole_0(B_50)
      | ~ l1_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_182,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_179])).

tff(c_185,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_182])).

tff(c_186,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_185])).

tff(c_303,plain,(
    ! [B_61,A_62] :
      ( v2_tex_2(u1_struct_0(B_61),A_62)
      | ~ v1_tdlat_3(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc(B_61,A_62)
      | v2_struct_0(B_61)
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_312,plain,(
    ! [A_62] :
      ( v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_62)
      | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_62)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_303])).

tff(c_317,plain,(
    ! [A_62] :
      ( v2_tex_2('#skF_3',A_62)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_62)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_186,c_312])).

tff(c_322,plain,(
    ! [A_63] :
      ( v2_tex_2('#skF_3',A_63)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_63)
      | ~ l1_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_317])).

tff(c_331,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_322])).

tff(c_337,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_89,c_331])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_56,c_337])).

tff(c_340,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_362,plain,(
    ! [A_76,B_77] :
      ( ~ v2_struct_0('#skF_1'(A_76,B_77))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | v1_xboole_0(B_77)
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_365,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_362])).

tff(c_368,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_365])).

tff(c_369,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_368])).

tff(c_419,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_384,c_2])).

tff(c_433,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_419])).

tff(c_416,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_384,c_14])).

tff(c_429,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_416])).

tff(c_430,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_369,c_429])).

tff(c_438,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_430])).

tff(c_439,plain,(
    ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_40,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_445,plain,(
    ! [B_83,A_84] :
      ( ~ v1_tdlat_3(B_83)
      | v7_struct_0(B_83)
      | v2_struct_0(B_83)
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84)
      | ~ v2_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_448,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_384,c_445])).

tff(c_451,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_448])).

tff(c_452,plain,(
    ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_369,c_439,c_451])).

tff(c_370,plain,(
    ! [A_78,B_79] :
      ( u1_struct_0('#skF_1'(A_78,B_79)) = B_79
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | v1_xboole_0(B_79)
      | ~ l1_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_373,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_370])).

tff(c_376,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_373])).

tff(c_377,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_376])).

tff(c_546,plain,(
    ! [B_94,A_95] :
      ( v1_tdlat_3(B_94)
      | ~ v2_tex_2(u1_struct_0(B_94),A_95)
      | ~ m1_subset_1(u1_struct_0(B_94),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_pre_topc(B_94,A_95)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_555,plain,(
    ! [A_95] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_95)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_95)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_546])).

tff(c_559,plain,(
    ! [A_95] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2('#skF_3',A_95)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_95)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_555])).

tff(c_564,plain,(
    ! [A_96] :
      ( ~ v2_tex_2('#skF_3',A_96)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_96)
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_452,c_559])).

tff(c_573,plain,
    ( ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_564])).

tff(c_579,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_384,c_340,c_573])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_579])).

tff(c_583,plain,(
    v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_341,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_402,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_10])).

tff(c_409,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_402])).

tff(c_601,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_409])).

tff(c_604,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_601])).

tff(c_608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.43  
% 2.62/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.43  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.43  
% 2.62/1.43  %Foreground sorts:
% 2.62/1.43  
% 2.62/1.43  
% 2.62/1.43  %Background operators:
% 2.62/1.43  
% 2.62/1.43  
% 2.62/1.43  %Foreground operators:
% 2.62/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.62/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.43  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.62/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.62/1.43  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.62/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.62/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.43  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.62/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.62/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.43  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.62/1.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.62/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.62/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.62/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.43  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.62/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.43  
% 3.00/1.45  tff(f_166, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.00/1.45  tff(f_126, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 3.00/1.45  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.00/1.45  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.00/1.45  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.00/1.45  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & v7_struct_0(B)) & v2_pre_topc(B)) => ((~v2_struct_0(B) & v1_tdlat_3(B)) & v2_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc25_tex_2)).
% 3.00/1.45  tff(f_53, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.00/1.45  tff(f_146, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 3.00/1.45  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 3.00/1.45  tff(f_59, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.00/1.45  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.00/1.45  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.00/1.45  tff(c_36, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.00/1.45  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.00/1.45  tff(c_378, plain, (![A_80, B_81]: (m1_pre_topc('#skF_1'(A_80, B_81), A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | v1_xboole_0(B_81) | ~l1_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.00/1.45  tff(c_380, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_378])).
% 3.00/1.45  tff(c_383, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_380])).
% 3.00/1.45  tff(c_384, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_383])).
% 3.00/1.45  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.45  tff(c_422, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_384, c_6])).
% 3.00/1.45  tff(c_436, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_422])).
% 3.00/1.45  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.45  tff(c_52, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.00/1.45  tff(c_54, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 3.00/1.45  tff(c_46, plain, (~v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.00/1.45  tff(c_56, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46])).
% 3.00/1.45  tff(c_83, plain, (![A_45, B_46]: (m1_pre_topc('#skF_1'(A_45, B_46), A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | v1_xboole_0(B_46) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.00/1.45  tff(c_85, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_83])).
% 3.00/1.45  tff(c_88, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_85])).
% 3.00/1.45  tff(c_89, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_88])).
% 3.00/1.45  tff(c_75, plain, (![A_43, B_44]: (~v2_struct_0('#skF_1'(A_43, B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | v1_xboole_0(B_44) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.00/1.45  tff(c_78, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_75])).
% 3.00/1.45  tff(c_81, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_78])).
% 3.00/1.45  tff(c_82, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_81])).
% 3.00/1.45  tff(c_101, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_89, c_6])).
% 3.00/1.45  tff(c_115, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_101])).
% 3.00/1.45  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.00/1.45  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.45  tff(c_98, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_89, c_2])).
% 3.00/1.45  tff(c_112, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_98])).
% 3.00/1.45  tff(c_14, plain, (![B_12, A_10]: (v1_tdlat_3(B_12) | ~v2_pre_topc(B_12) | ~v7_struct_0(B_12) | v2_struct_0(B_12) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.45  tff(c_95, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_89, c_14])).
% 3.00/1.45  tff(c_108, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_95])).
% 3.00/1.45  tff(c_109, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_82, c_108])).
% 3.00/1.45  tff(c_117, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_109])).
% 3.00/1.45  tff(c_118, plain, (~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_117])).
% 3.00/1.45  tff(c_119, plain, (![A_47, B_48]: (u1_struct_0('#skF_1'(A_47, B_48))=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | v1_xboole_0(B_48) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.00/1.45  tff(c_122, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_119])).
% 3.00/1.45  tff(c_125, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_122])).
% 3.00/1.45  tff(c_126, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_125])).
% 3.00/1.45  tff(c_8, plain, (![A_8]: (~v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.45  tff(c_144, plain, (~v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_8])).
% 3.00/1.45  tff(c_161, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_144])).
% 3.00/1.45  tff(c_162, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_118, c_161])).
% 3.00/1.45  tff(c_166, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_162])).
% 3.00/1.45  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_166])).
% 3.00/1.45  tff(c_171, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_117])).
% 3.00/1.45  tff(c_179, plain, (![A_49, B_50]: (u1_struct_0('#skF_1'(A_49, B_50))=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | v1_xboole_0(B_50) | ~l1_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.00/1.45  tff(c_182, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_179])).
% 3.00/1.45  tff(c_185, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_182])).
% 3.00/1.45  tff(c_186, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_185])).
% 3.00/1.45  tff(c_303, plain, (![B_61, A_62]: (v2_tex_2(u1_struct_0(B_61), A_62) | ~v1_tdlat_3(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc(B_61, A_62) | v2_struct_0(B_61) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.00/1.45  tff(c_312, plain, (![A_62]: (v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_62) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_62) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_186, c_303])).
% 3.00/1.45  tff(c_317, plain, (![A_62]: (v2_tex_2('#skF_3', A_62) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_62) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_186, c_312])).
% 3.00/1.45  tff(c_322, plain, (![A_63]: (v2_tex_2('#skF_3', A_63) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_63) | ~l1_pre_topc(A_63) | v2_struct_0(A_63))), inference(negUnitSimplification, [status(thm)], [c_82, c_317])).
% 3.00/1.45  tff(c_331, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_322])).
% 3.00/1.45  tff(c_337, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_89, c_331])).
% 3.00/1.45  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_56, c_337])).
% 3.00/1.45  tff(c_340, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 3.00/1.45  tff(c_362, plain, (![A_76, B_77]: (~v2_struct_0('#skF_1'(A_76, B_77)) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | v1_xboole_0(B_77) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.00/1.45  tff(c_365, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_362])).
% 3.00/1.45  tff(c_368, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_365])).
% 3.00/1.45  tff(c_369, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_368])).
% 3.00/1.45  tff(c_419, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_384, c_2])).
% 3.00/1.45  tff(c_433, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_419])).
% 3.00/1.45  tff(c_416, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_384, c_14])).
% 3.00/1.45  tff(c_429, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_416])).
% 3.00/1.45  tff(c_430, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_369, c_429])).
% 3.00/1.45  tff(c_438, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_430])).
% 3.00/1.45  tff(c_439, plain, (~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_438])).
% 3.00/1.45  tff(c_40, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.00/1.45  tff(c_445, plain, (![B_83, A_84]: (~v1_tdlat_3(B_83) | v7_struct_0(B_83) | v2_struct_0(B_83) | ~m1_pre_topc(B_83, A_84) | ~l1_pre_topc(A_84) | ~v2_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.00/1.45  tff(c_448, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_384, c_445])).
% 3.00/1.45  tff(c_451, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_448])).
% 3.00/1.45  tff(c_452, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_369, c_439, c_451])).
% 3.00/1.45  tff(c_370, plain, (![A_78, B_79]: (u1_struct_0('#skF_1'(A_78, B_79))=B_79 | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | v1_xboole_0(B_79) | ~l1_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.00/1.45  tff(c_373, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_370])).
% 3.00/1.45  tff(c_376, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_373])).
% 3.00/1.45  tff(c_377, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_376])).
% 3.00/1.45  tff(c_546, plain, (![B_94, A_95]: (v1_tdlat_3(B_94) | ~v2_tex_2(u1_struct_0(B_94), A_95) | ~m1_subset_1(u1_struct_0(B_94), k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_pre_topc(B_94, A_95) | v2_struct_0(B_94) | ~l1_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.00/1.45  tff(c_555, plain, (![A_95]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_95) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_95) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_95) | v2_struct_0(A_95))), inference(superposition, [status(thm), theory('equality')], [c_377, c_546])).
% 3.00/1.45  tff(c_559, plain, (![A_95]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2('#skF_3', A_95) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_95) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_95) | v2_struct_0(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_377, c_555])).
% 3.00/1.45  tff(c_564, plain, (![A_96]: (~v2_tex_2('#skF_3', A_96) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_96) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(negUnitSimplification, [status(thm)], [c_369, c_452, c_559])).
% 3.00/1.45  tff(c_573, plain, (~v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_564])).
% 3.00/1.45  tff(c_579, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_384, c_340, c_573])).
% 3.00/1.45  tff(c_581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_579])).
% 3.00/1.45  tff(c_583, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_438])).
% 3.00/1.45  tff(c_341, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.00/1.45  tff(c_10, plain, (![A_9]: (v1_zfmisc_1(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.00/1.45  tff(c_402, plain, (v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_377, c_10])).
% 3.00/1.45  tff(c_409, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_341, c_402])).
% 3.00/1.45  tff(c_601, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_583, c_409])).
% 3.00/1.45  tff(c_604, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_601])).
% 3.00/1.45  tff(c_608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_436, c_604])).
% 3.00/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.45  
% 3.00/1.45  Inference rules
% 3.00/1.45  ----------------------
% 3.00/1.45  #Ref     : 0
% 3.00/1.45  #Sup     : 94
% 3.00/1.45  #Fact    : 0
% 3.00/1.45  #Define  : 0
% 3.00/1.45  #Split   : 5
% 3.00/1.45  #Chain   : 0
% 3.00/1.45  #Close   : 0
% 3.00/1.45  
% 3.00/1.45  Ordering : KBO
% 3.00/1.45  
% 3.00/1.45  Simplification rules
% 3.00/1.45  ----------------------
% 3.00/1.45  #Subsume      : 6
% 3.00/1.45  #Demod        : 92
% 3.00/1.45  #Tautology    : 24
% 3.00/1.45  #SimpNegUnit  : 47
% 3.00/1.45  #BackRed      : 0
% 3.00/1.45  
% 3.00/1.45  #Partial instantiations: 0
% 3.00/1.45  #Strategies tried      : 1
% 3.00/1.45  
% 3.00/1.45  Timing (in seconds)
% 3.00/1.45  ----------------------
% 3.00/1.46  Preprocessing        : 0.31
% 3.00/1.46  Parsing              : 0.17
% 3.00/1.46  CNF conversion       : 0.02
% 3.00/1.46  Main loop            : 0.32
% 3.00/1.46  Inferencing          : 0.11
% 3.00/1.46  Reduction            : 0.10
% 3.00/1.46  Demodulation         : 0.06
% 3.00/1.46  BG Simplification    : 0.02
% 3.00/1.46  Subsumption          : 0.06
% 3.00/1.46  Abstraction          : 0.01
% 3.00/1.46  MUC search           : 0.00
% 3.00/1.46  Cooper               : 0.00
% 3.00/1.46  Total                : 0.68
% 3.00/1.46  Index Insertion      : 0.00
% 3.00/1.46  Index Deletion       : 0.00
% 3.00/1.46  Index Matching       : 0.00
% 3.00/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:50 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 526 expanded)
%              Number of leaves         :   31 ( 198 expanded)
%              Depth                    :   16
%              Number of atoms          :  353 (2101 expanded)
%              Number of equality atoms :   10 (  80 expanded)
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

tff(f_168,negated_conjecture,(
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

tff(f_128,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) )
       => ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_148,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_107,axiom,(
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

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_468,plain,(
    ! [A_86,B_87] :
      ( m1_pre_topc('#skF_1'(A_86,B_87),A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | v1_xboole_0(B_87)
      | ~ l1_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_470,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_468])).

tff(c_473,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_470])).

tff(c_474,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_473])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_480,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_474,c_6])).

tff(c_486,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_480])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_58,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_60,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50])).

tff(c_246,plain,(
    ! [A_54,B_55] :
      ( m1_pre_topc('#skF_1'(A_54,B_55),A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(B_55)
      | ~ l1_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_250,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_246])).

tff(c_256,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_250])).

tff(c_257,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_256])).

tff(c_78,plain,(
    ! [A_39,B_40] :
      ( ~ v2_struct_0('#skF_1'(A_39,B_40))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | v1_xboole_0(B_40)
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_81,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_84,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_81])).

tff(c_85,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_84])).

tff(c_94,plain,(
    ! [A_43,B_44] :
      ( u1_struct_0('#skF_1'(A_43,B_44)) = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | v1_xboole_0(B_44)
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_97,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_94])).

tff(c_100,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_97])).

tff(c_101,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_100])).

tff(c_32,plain,(
    ! [A_15,B_19] :
      ( ~ v2_struct_0('#skF_1'(A_15,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_15)))
      | v1_xboole_0(B_19)
      | ~ l1_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_111,plain,(
    ! [B_19] :
      ( ~ v2_struct_0('#skF_1'('#skF_1'('#skF_2','#skF_3'),B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1('#skF_3'))
      | v1_xboole_0(B_19)
      | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
      | v2_struct_0('#skF_1'('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_32])).

tff(c_122,plain,(
    ! [B_19] :
      ( ~ v2_struct_0('#skF_1'('#skF_1'('#skF_2','#skF_3'),B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1('#skF_3'))
      | v1_xboole_0(B_19)
      | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_111])).

tff(c_158,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_171,plain,(
    ! [A_47,B_48] :
      ( m1_pre_topc('#skF_1'(A_47,B_48),A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | v1_xboole_0(B_48)
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_175,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_171])).

tff(c_179,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_175])).

tff(c_180,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_179])).

tff(c_190,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_180,c_6])).

tff(c_200,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_190])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_200])).

tff(c_204,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_117,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_125,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_117])).

tff(c_127,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_131,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_127])).

tff(c_132,plain,(
    ! [A_45,B_46] :
      ( m1_pre_topc('#skF_1'(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | v1_xboole_0(B_46)
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_136,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_140,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_136])).

tff(c_141,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_140])).

tff(c_147,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_141,c_6])).

tff(c_153,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_147])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_153])).

tff(c_156,plain,(
    v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_14,plain,(
    ! [A_10] :
      ( v1_tdlat_3(A_10)
      | ~ v2_pre_topc(A_10)
      | ~ v7_struct_0(A_10)
      | v2_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_207,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_156,c_14])).

tff(c_213,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_207])).

tff(c_214,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_213])).

tff(c_219,plain,(
    ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_221,plain,(
    ! [A_52,B_53] :
      ( m1_pre_topc('#skF_1'(A_52,B_53),A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(B_53)
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_225,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_221])).

tff(c_231,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_225])).

tff(c_232,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_231])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_235,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_232,c_2])).

tff(c_241,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_235])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_241])).

tff(c_244,plain,(
    v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_394,plain,(
    ! [B_70,A_71] :
      ( v2_tex_2(u1_struct_0(B_70),A_71)
      | ~ v1_tdlat_3(B_70)
      | ~ m1_subset_1(u1_struct_0(B_70),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_pre_topc(B_70,A_71)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_403,plain,(
    ! [A_71] :
      ( v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_71)
      | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_71)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_394])).

tff(c_408,plain,(
    ! [A_71] :
      ( v2_tex_2('#skF_3',A_71)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_71)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_101,c_403])).

tff(c_413,plain,(
    ! [A_72] :
      ( v2_tex_2('#skF_3',A_72)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_72)
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_408])).

tff(c_422,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_413])).

tff(c_428,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_257,c_422])).

tff(c_430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_60,c_428])).

tff(c_431,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_452,plain,(
    ! [A_82,B_83] :
      ( ~ v2_struct_0('#skF_1'(A_82,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | v1_xboole_0(B_83)
      | ~ l1_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_455,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_452])).

tff(c_458,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_455])).

tff(c_459,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_458])).

tff(c_432,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_487,plain,(
    ! [A_88,B_89] :
      ( u1_struct_0('#skF_1'(A_88,B_89)) = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(B_89)
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_490,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_487])).

tff(c_493,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_490])).

tff(c_494,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_493])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_512,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_10])).

tff(c_527,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_512])).

tff(c_537,plain,(
    ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_527])).

tff(c_44,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_529,plain,(
    ! [B_90,A_91] :
      ( ~ v1_tdlat_3(B_90)
      | v7_struct_0(B_90)
      | v2_struct_0(B_90)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v2_tdlat_3(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_532,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_474,c_529])).

tff(c_535,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_532])).

tff(c_536,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_459,c_535])).

tff(c_538,plain,(
    ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_536])).

tff(c_589,plain,(
    ! [B_98,A_99] :
      ( v1_tdlat_3(B_98)
      | ~ v2_tex_2(u1_struct_0(B_98),A_99)
      | ~ m1_subset_1(u1_struct_0(B_98),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc(B_98,A_99)
      | v2_struct_0(B_98)
      | ~ l1_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_598,plain,(
    ! [A_99] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_99)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_99)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_589])).

tff(c_602,plain,(
    ! [A_99] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2('#skF_3',A_99)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_99)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_598])).

tff(c_607,plain,(
    ! [A_100] :
      ( ~ v2_tex_2('#skF_3',A_100)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_100)
      | ~ l1_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_538,c_602])).

tff(c_616,plain,
    ( ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_607])).

tff(c_622,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_474,c_431,c_616])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_622])).

tff(c_625,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_629,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_625])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.50  
% 2.75/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.50  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.75/1.50  
% 2.75/1.50  %Foreground sorts:
% 2.75/1.50  
% 2.75/1.50  
% 2.75/1.50  %Background operators:
% 2.75/1.50  
% 2.75/1.50  
% 2.75/1.50  %Foreground operators:
% 2.75/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.75/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.50  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.75/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.50  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.75/1.50  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.75/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.50  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.75/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.75/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.50  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.75/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.75/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.75/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.50  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.75/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.50  
% 2.75/1.52  tff(f_168, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.75/1.52  tff(f_128, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 2.75/1.52  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.75/1.52  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.75/1.52  tff(f_53, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.75/1.52  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A)) => (((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tex_1)).
% 2.75/1.52  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.75/1.52  tff(f_148, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.75/1.52  tff(f_59, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.75/1.52  tff(f_107, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 2.75/1.52  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.52  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.52  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.52  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.52  tff(c_468, plain, (![A_86, B_87]: (m1_pre_topc('#skF_1'(A_86, B_87), A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | v1_xboole_0(B_87) | ~l1_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_470, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_468])).
% 2.75/1.52  tff(c_473, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_470])).
% 2.75/1.52  tff(c_474, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_473])).
% 2.75/1.52  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.75/1.52  tff(c_480, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_474, c_6])).
% 2.75/1.52  tff(c_486, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_480])).
% 2.75/1.52  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.75/1.52  tff(c_56, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.52  tff(c_58, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 2.75/1.52  tff(c_50, plain, (~v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.52  tff(c_60, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50])).
% 2.75/1.52  tff(c_246, plain, (![A_54, B_55]: (m1_pre_topc('#skF_1'(A_54, B_55), A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(B_55) | ~l1_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_250, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_246])).
% 2.75/1.52  tff(c_256, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_250])).
% 2.75/1.52  tff(c_257, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_256])).
% 2.75/1.52  tff(c_78, plain, (![A_39, B_40]: (~v2_struct_0('#skF_1'(A_39, B_40)) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | v1_xboole_0(B_40) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_81, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_78])).
% 2.75/1.52  tff(c_84, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_81])).
% 2.75/1.52  tff(c_85, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_84])).
% 2.75/1.52  tff(c_94, plain, (![A_43, B_44]: (u1_struct_0('#skF_1'(A_43, B_44))=B_44 | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | v1_xboole_0(B_44) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_97, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_94])).
% 2.75/1.52  tff(c_100, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_97])).
% 2.75/1.52  tff(c_101, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_100])).
% 2.75/1.52  tff(c_32, plain, (![A_15, B_19]: (~v2_struct_0('#skF_1'(A_15, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_15))) | v1_xboole_0(B_19) | ~l1_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_111, plain, (![B_19]: (~v2_struct_0('#skF_1'('#skF_1'('#skF_2', '#skF_3'), B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1('#skF_3')) | v1_xboole_0(B_19) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_101, c_32])).
% 2.75/1.52  tff(c_122, plain, (![B_19]: (~v2_struct_0('#skF_1'('#skF_1'('#skF_2', '#skF_3'), B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1('#skF_3')) | v1_xboole_0(B_19) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_85, c_111])).
% 2.75/1.52  tff(c_158, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_122])).
% 2.75/1.52  tff(c_171, plain, (![A_47, B_48]: (m1_pre_topc('#skF_1'(A_47, B_48), A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | v1_xboole_0(B_48) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_175, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_171])).
% 2.75/1.52  tff(c_179, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_175])).
% 2.75/1.52  tff(c_180, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_179])).
% 2.75/1.52  tff(c_190, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_180, c_6])).
% 2.75/1.52  tff(c_200, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_190])).
% 2.75/1.52  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_200])).
% 2.75/1.52  tff(c_204, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_122])).
% 2.75/1.52  tff(c_8, plain, (![A_8]: (~v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.52  tff(c_117, plain, (~v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 2.75/1.52  tff(c_125, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_117])).
% 2.75/1.52  tff(c_127, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_125])).
% 2.75/1.52  tff(c_131, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_127])).
% 2.75/1.52  tff(c_132, plain, (![A_45, B_46]: (m1_pre_topc('#skF_1'(A_45, B_46), A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | v1_xboole_0(B_46) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_136, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_132])).
% 2.75/1.52  tff(c_140, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_136])).
% 2.75/1.52  tff(c_141, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_140])).
% 2.75/1.52  tff(c_147, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_141, c_6])).
% 2.75/1.52  tff(c_153, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_147])).
% 2.75/1.52  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_153])).
% 2.75/1.52  tff(c_156, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_125])).
% 2.75/1.52  tff(c_14, plain, (![A_10]: (v1_tdlat_3(A_10) | ~v2_pre_topc(A_10) | ~v7_struct_0(A_10) | v2_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.52  tff(c_207, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_156, c_14])).
% 2.75/1.52  tff(c_213, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_207])).
% 2.75/1.52  tff(c_214, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_85, c_213])).
% 2.75/1.52  tff(c_219, plain, (~v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_214])).
% 2.75/1.52  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.52  tff(c_221, plain, (![A_52, B_53]: (m1_pre_topc('#skF_1'(A_52, B_53), A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(B_53) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_225, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_221])).
% 2.75/1.52  tff(c_231, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_225])).
% 2.75/1.52  tff(c_232, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_231])).
% 2.75/1.52  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.75/1.52  tff(c_235, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_232, c_2])).
% 2.75/1.52  tff(c_241, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_235])).
% 2.75/1.52  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_219, c_241])).
% 2.75/1.52  tff(c_244, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_214])).
% 2.75/1.52  tff(c_394, plain, (![B_70, A_71]: (v2_tex_2(u1_struct_0(B_70), A_71) | ~v1_tdlat_3(B_70) | ~m1_subset_1(u1_struct_0(B_70), k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_pre_topc(B_70, A_71) | v2_struct_0(B_70) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.75/1.52  tff(c_403, plain, (![A_71]: (v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_71) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_71) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(superposition, [status(thm), theory('equality')], [c_101, c_394])).
% 2.75/1.52  tff(c_408, plain, (![A_71]: (v2_tex_2('#skF_3', A_71) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_71) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_101, c_403])).
% 2.75/1.52  tff(c_413, plain, (![A_72]: (v2_tex_2('#skF_3', A_72) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_72) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(negUnitSimplification, [status(thm)], [c_85, c_408])).
% 2.75/1.52  tff(c_422, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_413])).
% 2.75/1.52  tff(c_428, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_257, c_422])).
% 2.75/1.52  tff(c_430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_60, c_428])).
% 2.75/1.52  tff(c_431, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 2.75/1.52  tff(c_452, plain, (![A_82, B_83]: (~v2_struct_0('#skF_1'(A_82, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | v1_xboole_0(B_83) | ~l1_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_455, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_452])).
% 2.75/1.52  tff(c_458, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_455])).
% 2.75/1.52  tff(c_459, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_458])).
% 2.75/1.52  tff(c_432, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 2.75/1.52  tff(c_487, plain, (![A_88, B_89]: (u1_struct_0('#skF_1'(A_88, B_89))=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(B_89) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.75/1.52  tff(c_490, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_487])).
% 2.75/1.52  tff(c_493, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_490])).
% 2.75/1.52  tff(c_494, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_493])).
% 2.75/1.52  tff(c_10, plain, (![A_9]: (v1_zfmisc_1(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.75/1.52  tff(c_512, plain, (v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_494, c_10])).
% 2.75/1.52  tff(c_527, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_432, c_512])).
% 2.75/1.52  tff(c_537, plain, (~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_527])).
% 2.75/1.52  tff(c_44, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.75/1.52  tff(c_529, plain, (![B_90, A_91]: (~v1_tdlat_3(B_90) | v7_struct_0(B_90) | v2_struct_0(B_90) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91) | ~v2_tdlat_3(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.75/1.52  tff(c_532, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_474, c_529])).
% 2.75/1.52  tff(c_535, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_532])).
% 2.75/1.52  tff(c_536, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_459, c_535])).
% 2.75/1.52  tff(c_538, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_537, c_536])).
% 2.75/1.52  tff(c_589, plain, (![B_98, A_99]: (v1_tdlat_3(B_98) | ~v2_tex_2(u1_struct_0(B_98), A_99) | ~m1_subset_1(u1_struct_0(B_98), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_pre_topc(B_98, A_99) | v2_struct_0(B_98) | ~l1_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.75/1.52  tff(c_598, plain, (![A_99]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_99) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_99) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_99) | v2_struct_0(A_99))), inference(superposition, [status(thm), theory('equality')], [c_494, c_589])).
% 2.75/1.52  tff(c_602, plain, (![A_99]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2('#skF_3', A_99) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_99) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_99) | v2_struct_0(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_598])).
% 2.75/1.52  tff(c_607, plain, (![A_100]: (~v2_tex_2('#skF_3', A_100) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_100) | ~l1_pre_topc(A_100) | v2_struct_0(A_100))), inference(negUnitSimplification, [status(thm)], [c_459, c_538, c_602])).
% 2.75/1.52  tff(c_616, plain, (~v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_607])).
% 2.75/1.52  tff(c_622, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_474, c_431, c_616])).
% 2.75/1.52  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_622])).
% 2.75/1.52  tff(c_625, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_527])).
% 2.75/1.52  tff(c_629, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_625])).
% 2.75/1.52  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_486, c_629])).
% 2.75/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.52  
% 2.75/1.52  Inference rules
% 2.75/1.52  ----------------------
% 2.75/1.52  #Ref     : 0
% 2.75/1.52  #Sup     : 102
% 2.75/1.52  #Fact    : 0
% 2.75/1.52  #Define  : 0
% 2.75/1.52  #Split   : 5
% 2.75/1.52  #Chain   : 0
% 2.75/1.52  #Close   : 0
% 2.75/1.52  
% 2.75/1.52  Ordering : KBO
% 2.75/1.52  
% 2.75/1.52  Simplification rules
% 2.75/1.52  ----------------------
% 2.75/1.52  #Subsume      : 6
% 2.94/1.52  #Demod        : 89
% 2.94/1.52  #Tautology    : 27
% 2.94/1.52  #SimpNegUnit  : 47
% 2.94/1.52  #BackRed      : 0
% 2.94/1.52  
% 2.94/1.52  #Partial instantiations: 0
% 2.94/1.52  #Strategies tried      : 1
% 2.94/1.52  
% 2.94/1.52  Timing (in seconds)
% 2.94/1.52  ----------------------
% 2.94/1.53  Preprocessing        : 0.29
% 2.94/1.53  Parsing              : 0.16
% 2.94/1.53  CNF conversion       : 0.02
% 2.94/1.53  Main loop            : 0.32
% 2.94/1.53  Inferencing          : 0.11
% 2.94/1.53  Reduction            : 0.10
% 2.94/1.53  Demodulation         : 0.06
% 2.94/1.53  BG Simplification    : 0.02
% 2.94/1.53  Subsumption          : 0.07
% 2.94/1.53  Abstraction          : 0.01
% 2.94/1.53  MUC search           : 0.00
% 2.94/1.53  Cooper               : 0.00
% 2.94/1.53  Total                : 0.66
% 2.94/1.53  Index Insertion      : 0.00
% 2.94/1.53  Index Deletion       : 0.00
% 2.94/1.53  Index Matching       : 0.00
% 2.94/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:12 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 806 expanded)
%              Number of leaves         :   38 ( 283 expanded)
%              Depth                    :   12
%              Number of atoms          :  279 (2069 expanded)
%              Number of equality atoms :   21 ( 247 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_234,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_157,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_tops_1)).

tff(f_200,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_216,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_175,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_17] :
      ( m1_subset_1(k2_struct_0(A_17),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1545,plain,(
    ! [B_218,A_219] :
      ( v1_subset_1(B_218,A_219)
      | B_218 = A_219
      | ~ m1_subset_1(B_218,k1_zfmisc_1(A_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1581,plain,(
    ! [A_227] :
      ( v1_subset_1(k2_struct_0(A_227),u1_struct_0(A_227))
      | u1_struct_0(A_227) = k2_struct_0(A_227)
      | ~ l1_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_18,c_1545])).

tff(c_22,plain,(
    ! [A_19] :
      ( ~ v1_subset_1(k2_struct_0(A_19),u1_struct_0(A_19))
      | ~ l1_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1586,plain,(
    ! [A_228] :
      ( u1_struct_0(A_228) = k2_struct_0(A_228)
      | ~ l1_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_1581,c_22])).

tff(c_1591,plain,(
    ! [A_229] :
      ( u1_struct_0(A_229) = k2_struct_0(A_229)
      | ~ l1_pre_topc(A_229) ) ),
    inference(resolution,[status(thm)],[c_20,c_1586])).

tff(c_1595,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1591])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_1598,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1595,c_72])).

tff(c_88,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_91,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_82,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_92,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_82])).

tff(c_117,plain,(
    ! [B_84,A_85] :
      ( v1_subset_1(B_84,A_85)
      | B_84 = A_85
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_126,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_117])).

tff(c_131,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_126])).

tff(c_110,plain,(
    ! [A_81] :
      ( m1_subset_1(k2_struct_0(A_81),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,(
    ! [A_81] :
      ( r1_tarski(k2_struct_0(A_81),u1_struct_0(A_81))
      | ~ l1_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_110,c_14])).

tff(c_138,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),'#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_114])).

tff(c_164,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_167,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_167])).

tff(c_173,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_144,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_3'),'#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_22])).

tff(c_184,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_144])).

tff(c_141,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1('#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_18])).

tff(c_186,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_141])).

tff(c_46,plain,(
    ! [B_51,A_50] :
      ( v1_subset_1(B_51,A_50)
      | B_51 = A_50
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_189,plain,
    ( v1_subset_1(k2_struct_0('#skF_3'),'#skF_4')
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_186,c_46])).

tff(c_195,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_189])).

tff(c_38,plain,(
    ! [A_39] :
      ( v1_tops_1(k2_struct_0(A_39),A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_215,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_38])).

tff(c_225,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_215])).

tff(c_134,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_72])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_78,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_76,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_757,plain,(
    ! [B_150,A_151] :
      ( v2_tex_2(B_150,A_151)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v1_tdlat_3(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_767,plain,(
    ! [B_150] :
      ( v2_tex_2(B_150,'#skF_3')
      | ~ m1_subset_1(B_150,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_757])).

tff(c_778,plain,(
    ! [B_150] :
      ( v2_tex_2(B_150,'#skF_3')
      | ~ m1_subset_1(B_150,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_767])).

tff(c_782,plain,(
    ! [B_152] :
      ( v2_tex_2(B_152,'#skF_3')
      | ~ m1_subset_1(B_152,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_778])).

tff(c_795,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_782])).

tff(c_1452,plain,(
    ! [B_204,A_205] :
      ( v3_tex_2(B_204,A_205)
      | ~ v2_tex_2(B_204,A_205)
      | ~ v1_tops_1(B_204,A_205)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1465,plain,(
    ! [B_204] :
      ( v3_tex_2(B_204,'#skF_3')
      | ~ v2_tex_2(B_204,'#skF_3')
      | ~ v1_tops_1(B_204,'#skF_3')
      | ~ m1_subset_1(B_204,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_1452])).

tff(c_1477,plain,(
    ! [B_204] :
      ( v3_tex_2(B_204,'#skF_3')
      | ~ v2_tex_2(B_204,'#skF_3')
      | ~ v1_tops_1(B_204,'#skF_3')
      | ~ m1_subset_1(B_204,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_1465])).

tff(c_1499,plain,(
    ! [B_208] :
      ( v3_tex_2(B_208,'#skF_3')
      | ~ v2_tex_2(B_208,'#skF_3')
      | ~ v1_tops_1(B_208,'#skF_3')
      | ~ m1_subset_1(B_208,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1477])).

tff(c_1506,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_1499])).

tff(c_1514,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_795,c_1506])).

tff(c_1516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1514])).

tff(c_1517,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1608,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1595,c_22])).

tff(c_1622,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1608])).

tff(c_1625,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1622])).

tff(c_1629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1625])).

tff(c_1631,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1608])).

tff(c_1605,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1595,c_18])).

tff(c_1659,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1605])).

tff(c_1682,plain,(
    ! [B_232,A_233] :
      ( v2_tex_2(B_232,A_233)
      | ~ v3_tex_2(B_232,A_233)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1688,plain,(
    ! [B_232] :
      ( v2_tex_2(B_232,'#skF_3')
      | ~ v3_tex_2(B_232,'#skF_3')
      | ~ m1_subset_1(B_232,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1595,c_1682])).

tff(c_1706,plain,(
    ! [B_234] :
      ( v2_tex_2(B_234,'#skF_3')
      | ~ v3_tex_2(B_234,'#skF_3')
      | ~ m1_subset_1(B_234,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1688])).

tff(c_1721,plain,
    ( v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1659,c_1706])).

tff(c_1786,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1721])).

tff(c_1804,plain,(
    ! [A_241,B_242] :
      ( k2_pre_topc(A_241,B_242) = k2_struct_0(A_241)
      | ~ v1_tops_1(B_242,A_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1810,plain,(
    ! [B_242] :
      ( k2_pre_topc('#skF_3',B_242) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_242,'#skF_3')
      | ~ m1_subset_1(B_242,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1595,c_1804])).

tff(c_1849,plain,(
    ! [B_247] :
      ( k2_pre_topc('#skF_3',B_247) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_247,'#skF_3')
      | ~ m1_subset_1(B_247,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1810])).

tff(c_1864,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1659,c_1849])).

tff(c_1869,plain,(
    ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1864])).

tff(c_1872,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1869])).

tff(c_1876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1872])).

tff(c_1878,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1864])).

tff(c_2184,plain,(
    ! [B_277,A_278] :
      ( v2_tex_2(B_277,A_278)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278)
      | ~ v1_tdlat_3(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_2190,plain,(
    ! [B_277] :
      ( v2_tex_2(B_277,'#skF_3')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1595,c_2184])).

tff(c_2204,plain,(
    ! [B_277] :
      ( v2_tex_2(B_277,'#skF_3')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_2190])).

tff(c_2209,plain,(
    ! [B_279] :
      ( v2_tex_2(B_279,'#skF_3')
      | ~ m1_subset_1(B_279,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2204])).

tff(c_2224,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1659,c_2209])).

tff(c_2806,plain,(
    ! [B_350,A_351] :
      ( v3_tex_2(B_350,A_351)
      | ~ v2_tex_2(B_350,A_351)
      | ~ v1_tops_1(B_350,A_351)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_2815,plain,(
    ! [B_350] :
      ( v3_tex_2(B_350,'#skF_3')
      | ~ v2_tex_2(B_350,'#skF_3')
      | ~ v1_tops_1(B_350,'#skF_3')
      | ~ m1_subset_1(B_350,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1595,c_2806])).

tff(c_2830,plain,(
    ! [B_350] :
      ( v3_tex_2(B_350,'#skF_3')
      | ~ v2_tex_2(B_350,'#skF_3')
      | ~ v1_tops_1(B_350,'#skF_3')
      | ~ m1_subset_1(B_350,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_2815])).

tff(c_2835,plain,(
    ! [B_352] :
      ( v3_tex_2(B_352,'#skF_3')
      | ~ v2_tex_2(B_352,'#skF_3')
      | ~ v1_tops_1(B_352,'#skF_3')
      | ~ m1_subset_1(B_352,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2830])).

tff(c_2841,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1659,c_2835])).

tff(c_2856,plain,(
    v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1878,c_2224,c_2841])).

tff(c_2858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1786,c_2856])).

tff(c_2859,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1721])).

tff(c_1530,plain,(
    ! [A_214,B_215] :
      ( r1_tarski(A_214,B_215)
      | ~ m1_subset_1(A_214,k1_zfmisc_1(B_215)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1538,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_1530])).

tff(c_1596,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1595,c_1538])).

tff(c_5547,plain,(
    ! [C_629,B_630,A_631] :
      ( C_629 = B_630
      | ~ r1_tarski(B_630,C_629)
      | ~ v2_tex_2(C_629,A_631)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(u1_struct_0(A_631)))
      | ~ v3_tex_2(B_630,A_631)
      | ~ m1_subset_1(B_630,k1_zfmisc_1(u1_struct_0(A_631)))
      | ~ l1_pre_topc(A_631) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_5576,plain,(
    ! [A_631] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_631)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_631)))
      | ~ v3_tex_2('#skF_4',A_631)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_631)))
      | ~ l1_pre_topc(A_631) ) ),
    inference(resolution,[status(thm)],[c_1596,c_5547])).

tff(c_5628,plain,(
    ! [A_640] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_640)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_640)))
      | ~ v3_tex_2('#skF_4',A_640)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_640)))
      | ~ l1_pre_topc(A_640) ) ),
    inference(splitLeft,[status(thm)],[c_5576])).

tff(c_5631,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1595,c_5628])).

tff(c_5641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1598,c_1595,c_1517,c_1659,c_2859,c_5631])).

tff(c_5642,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5576])).

tff(c_1630,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1608])).

tff(c_5683,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5642,c_5642,c_1630])).

tff(c_1518,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1597,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1595,c_1518])).

tff(c_5685,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5642,c_1597])).

tff(c_5809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5683,c_5685])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:56:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.36/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.72  
% 7.36/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.72  %$ v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.36/2.72  
% 7.36/2.72  %Foreground sorts:
% 7.36/2.72  
% 7.36/2.72  
% 7.36/2.72  %Background operators:
% 7.36/2.72  
% 7.36/2.72  
% 7.36/2.72  %Foreground operators:
% 7.36/2.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.36/2.72  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.36/2.72  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.36/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.36/2.72  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.36/2.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.36/2.72  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.36/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.36/2.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.36/2.72  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.36/2.72  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.36/2.72  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.36/2.72  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.36/2.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.36/2.72  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.36/2.72  tff('#skF_3', type, '#skF_3': $i).
% 7.36/2.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.36/2.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.36/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.36/2.72  tff('#skF_4', type, '#skF_4': $i).
% 7.36/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.36/2.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.36/2.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.36/2.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.36/2.72  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.36/2.72  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.36/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.36/2.72  
% 7.36/2.75  tff(f_234, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 7.36/2.75  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.36/2.75  tff(f_62, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 7.36/2.75  tff(f_157, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 7.36/2.75  tff(f_71, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 7.36/2.75  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.36/2.75  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => v1_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_tops_1)).
% 7.36/2.75  tff(f_200, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 7.36/2.75  tff(f_216, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 7.36/2.75  tff(f_175, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 7.36/2.75  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 7.36/2.75  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.36/2.75  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.36/2.75  tff(c_18, plain, (![A_17]: (m1_subset_1(k2_struct_0(A_17), k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.36/2.75  tff(c_1545, plain, (![B_218, A_219]: (v1_subset_1(B_218, A_219) | B_218=A_219 | ~m1_subset_1(B_218, k1_zfmisc_1(A_219)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.36/2.75  tff(c_1581, plain, (![A_227]: (v1_subset_1(k2_struct_0(A_227), u1_struct_0(A_227)) | u1_struct_0(A_227)=k2_struct_0(A_227) | ~l1_struct_0(A_227))), inference(resolution, [status(thm)], [c_18, c_1545])).
% 7.36/2.75  tff(c_22, plain, (![A_19]: (~v1_subset_1(k2_struct_0(A_19), u1_struct_0(A_19)) | ~l1_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.36/2.75  tff(c_1586, plain, (![A_228]: (u1_struct_0(A_228)=k2_struct_0(A_228) | ~l1_struct_0(A_228))), inference(resolution, [status(thm)], [c_1581, c_22])).
% 7.36/2.75  tff(c_1591, plain, (![A_229]: (u1_struct_0(A_229)=k2_struct_0(A_229) | ~l1_pre_topc(A_229))), inference(resolution, [status(thm)], [c_20, c_1586])).
% 7.36/2.75  tff(c_1595, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1591])).
% 7.36/2.75  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.36/2.75  tff(c_1598, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1595, c_72])).
% 7.36/2.75  tff(c_88, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.36/2.75  tff(c_91, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_88])).
% 7.36/2.75  tff(c_82, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.36/2.75  tff(c_92, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_91, c_82])).
% 7.36/2.75  tff(c_117, plain, (![B_84, A_85]: (v1_subset_1(B_84, A_85) | B_84=A_85 | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.36/2.75  tff(c_126, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_72, c_117])).
% 7.36/2.75  tff(c_131, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_91, c_126])).
% 7.36/2.75  tff(c_110, plain, (![A_81]: (m1_subset_1(k2_struct_0(A_81), k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.36/2.75  tff(c_14, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.36/2.75  tff(c_114, plain, (![A_81]: (r1_tarski(k2_struct_0(A_81), u1_struct_0(A_81)) | ~l1_struct_0(A_81))), inference(resolution, [status(thm)], [c_110, c_14])).
% 7.36/2.75  tff(c_138, plain, (r1_tarski(k2_struct_0('#skF_3'), '#skF_4') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_131, c_114])).
% 7.36/2.75  tff(c_164, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_138])).
% 7.36/2.75  tff(c_167, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_164])).
% 7.36/2.75  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_167])).
% 7.36/2.75  tff(c_173, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_138])).
% 7.36/2.75  tff(c_144, plain, (~v1_subset_1(k2_struct_0('#skF_3'), '#skF_4') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_131, c_22])).
% 7.36/2.75  tff(c_184, plain, (~v1_subset_1(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_144])).
% 7.36/2.75  tff(c_141, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1('#skF_4')) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_131, c_18])).
% 7.36/2.75  tff(c_186, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_141])).
% 7.36/2.75  tff(c_46, plain, (![B_51, A_50]: (v1_subset_1(B_51, A_50) | B_51=A_50 | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.36/2.75  tff(c_189, plain, (v1_subset_1(k2_struct_0('#skF_3'), '#skF_4') | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_186, c_46])).
% 7.36/2.75  tff(c_195, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_184, c_189])).
% 7.36/2.75  tff(c_38, plain, (![A_39]: (v1_tops_1(k2_struct_0(A_39), A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.36/2.75  tff(c_215, plain, (v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_195, c_38])).
% 7.36/2.75  tff(c_225, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_215])).
% 7.36/2.75  tff(c_134, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_72])).
% 7.36/2.75  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.36/2.75  tff(c_78, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.36/2.75  tff(c_76, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.36/2.75  tff(c_757, plain, (![B_150, A_151]: (v2_tex_2(B_150, A_151) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v1_tdlat_3(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.36/2.75  tff(c_767, plain, (![B_150]: (v2_tex_2(B_150, '#skF_3') | ~m1_subset_1(B_150, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_757])).
% 7.36/2.75  tff(c_778, plain, (![B_150]: (v2_tex_2(B_150, '#skF_3') | ~m1_subset_1(B_150, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_767])).
% 7.36/2.75  tff(c_782, plain, (![B_152]: (v2_tex_2(B_152, '#skF_3') | ~m1_subset_1(B_152, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_778])).
% 7.36/2.75  tff(c_795, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_134, c_782])).
% 7.36/2.75  tff(c_1452, plain, (![B_204, A_205]: (v3_tex_2(B_204, A_205) | ~v2_tex_2(B_204, A_205) | ~v1_tops_1(B_204, A_205) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.36/2.75  tff(c_1465, plain, (![B_204]: (v3_tex_2(B_204, '#skF_3') | ~v2_tex_2(B_204, '#skF_3') | ~v1_tops_1(B_204, '#skF_3') | ~m1_subset_1(B_204, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_1452])).
% 7.36/2.75  tff(c_1477, plain, (![B_204]: (v3_tex_2(B_204, '#skF_3') | ~v2_tex_2(B_204, '#skF_3') | ~v1_tops_1(B_204, '#skF_3') | ~m1_subset_1(B_204, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_1465])).
% 7.36/2.75  tff(c_1499, plain, (![B_208]: (v3_tex_2(B_208, '#skF_3') | ~v2_tex_2(B_208, '#skF_3') | ~v1_tops_1(B_208, '#skF_3') | ~m1_subset_1(B_208, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_1477])).
% 7.36/2.75  tff(c_1506, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_134, c_1499])).
% 7.36/2.75  tff(c_1514, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_795, c_1506])).
% 7.36/2.75  tff(c_1516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1514])).
% 7.36/2.75  tff(c_1517, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_88])).
% 7.36/2.75  tff(c_1608, plain, (~v1_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1595, c_22])).
% 7.36/2.75  tff(c_1622, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1608])).
% 7.36/2.75  tff(c_1625, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1622])).
% 7.36/2.75  tff(c_1629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1625])).
% 7.36/2.75  tff(c_1631, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1608])).
% 7.36/2.75  tff(c_1605, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1595, c_18])).
% 7.36/2.75  tff(c_1659, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1605])).
% 7.36/2.75  tff(c_1682, plain, (![B_232, A_233]: (v2_tex_2(B_232, A_233) | ~v3_tex_2(B_232, A_233) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.36/2.75  tff(c_1688, plain, (![B_232]: (v2_tex_2(B_232, '#skF_3') | ~v3_tex_2(B_232, '#skF_3') | ~m1_subset_1(B_232, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1595, c_1682])).
% 7.36/2.75  tff(c_1706, plain, (![B_234]: (v2_tex_2(B_234, '#skF_3') | ~v3_tex_2(B_234, '#skF_3') | ~m1_subset_1(B_234, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1688])).
% 7.36/2.75  tff(c_1721, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1659, c_1706])).
% 7.36/2.75  tff(c_1786, plain, (~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1721])).
% 7.36/2.75  tff(c_1804, plain, (![A_241, B_242]: (k2_pre_topc(A_241, B_242)=k2_struct_0(A_241) | ~v1_tops_1(B_242, A_241) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.36/2.75  tff(c_1810, plain, (![B_242]: (k2_pre_topc('#skF_3', B_242)=k2_struct_0('#skF_3') | ~v1_tops_1(B_242, '#skF_3') | ~m1_subset_1(B_242, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1595, c_1804])).
% 7.36/2.75  tff(c_1849, plain, (![B_247]: (k2_pre_topc('#skF_3', B_247)=k2_struct_0('#skF_3') | ~v1_tops_1(B_247, '#skF_3') | ~m1_subset_1(B_247, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1810])).
% 7.36/2.75  tff(c_1864, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1659, c_1849])).
% 7.36/2.75  tff(c_1869, plain, (~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1864])).
% 7.36/2.75  tff(c_1872, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1869])).
% 7.36/2.75  tff(c_1876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1872])).
% 7.36/2.75  tff(c_1878, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1864])).
% 7.36/2.75  tff(c_2184, plain, (![B_277, A_278]: (v2_tex_2(B_277, A_278) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278) | ~v1_tdlat_3(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.36/2.75  tff(c_2190, plain, (![B_277]: (v2_tex_2(B_277, '#skF_3') | ~m1_subset_1(B_277, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1595, c_2184])).
% 7.36/2.75  tff(c_2204, plain, (![B_277]: (v2_tex_2(B_277, '#skF_3') | ~m1_subset_1(B_277, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_2190])).
% 7.36/2.75  tff(c_2209, plain, (![B_279]: (v2_tex_2(B_279, '#skF_3') | ~m1_subset_1(B_279, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_2204])).
% 7.36/2.75  tff(c_2224, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1659, c_2209])).
% 7.36/2.75  tff(c_2806, plain, (![B_350, A_351]: (v3_tex_2(B_350, A_351) | ~v2_tex_2(B_350, A_351) | ~v1_tops_1(B_350, A_351) | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0(A_351))) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351))), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.36/2.75  tff(c_2815, plain, (![B_350]: (v3_tex_2(B_350, '#skF_3') | ~v2_tex_2(B_350, '#skF_3') | ~v1_tops_1(B_350, '#skF_3') | ~m1_subset_1(B_350, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1595, c_2806])).
% 7.36/2.75  tff(c_2830, plain, (![B_350]: (v3_tex_2(B_350, '#skF_3') | ~v2_tex_2(B_350, '#skF_3') | ~v1_tops_1(B_350, '#skF_3') | ~m1_subset_1(B_350, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_2815])).
% 7.36/2.75  tff(c_2835, plain, (![B_352]: (v3_tex_2(B_352, '#skF_3') | ~v2_tex_2(B_352, '#skF_3') | ~v1_tops_1(B_352, '#skF_3') | ~m1_subset_1(B_352, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_2830])).
% 7.36/2.75  tff(c_2841, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1659, c_2835])).
% 7.36/2.75  tff(c_2856, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1878, c_2224, c_2841])).
% 7.36/2.75  tff(c_2858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1786, c_2856])).
% 7.36/2.75  tff(c_2859, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1721])).
% 7.36/2.75  tff(c_1530, plain, (![A_214, B_215]: (r1_tarski(A_214, B_215) | ~m1_subset_1(A_214, k1_zfmisc_1(B_215)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.36/2.75  tff(c_1538, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_1530])).
% 7.36/2.75  tff(c_1596, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1595, c_1538])).
% 7.36/2.75  tff(c_5547, plain, (![C_629, B_630, A_631]: (C_629=B_630 | ~r1_tarski(B_630, C_629) | ~v2_tex_2(C_629, A_631) | ~m1_subset_1(C_629, k1_zfmisc_1(u1_struct_0(A_631))) | ~v3_tex_2(B_630, A_631) | ~m1_subset_1(B_630, k1_zfmisc_1(u1_struct_0(A_631))) | ~l1_pre_topc(A_631))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.36/2.75  tff(c_5576, plain, (![A_631]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_631) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_631))) | ~v3_tex_2('#skF_4', A_631) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_631))) | ~l1_pre_topc(A_631))), inference(resolution, [status(thm)], [c_1596, c_5547])).
% 7.36/2.75  tff(c_5628, plain, (![A_640]: (~v2_tex_2(k2_struct_0('#skF_3'), A_640) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_640))) | ~v3_tex_2('#skF_4', A_640) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_640))) | ~l1_pre_topc(A_640))), inference(splitLeft, [status(thm)], [c_5576])).
% 7.36/2.75  tff(c_5631, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1595, c_5628])).
% 7.36/2.75  tff(c_5641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1598, c_1595, c_1517, c_1659, c_2859, c_5631])).
% 7.36/2.75  tff(c_5642, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_5576])).
% 7.36/2.75  tff(c_1630, plain, (~v1_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1608])).
% 7.36/2.75  tff(c_5683, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5642, c_5642, c_1630])).
% 7.36/2.75  tff(c_1518, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_88])).
% 7.36/2.75  tff(c_1597, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1595, c_1518])).
% 7.36/2.75  tff(c_5685, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5642, c_1597])).
% 7.36/2.75  tff(c_5809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5683, c_5685])).
% 7.36/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.75  
% 7.36/2.75  Inference rules
% 7.36/2.75  ----------------------
% 7.36/2.75  #Ref     : 0
% 7.36/2.75  #Sup     : 1160
% 7.36/2.75  #Fact    : 0
% 7.36/2.75  #Define  : 0
% 7.36/2.75  #Split   : 13
% 7.36/2.75  #Chain   : 0
% 7.36/2.75  #Close   : 0
% 7.36/2.75  
% 7.36/2.75  Ordering : KBO
% 7.36/2.75  
% 7.36/2.75  Simplification rules
% 7.36/2.75  ----------------------
% 7.36/2.75  #Subsume      : 251
% 7.36/2.75  #Demod        : 1008
% 7.36/2.75  #Tautology    : 336
% 7.36/2.75  #SimpNegUnit  : 47
% 7.36/2.75  #BackRed      : 101
% 7.36/2.75  
% 7.36/2.75  #Partial instantiations: 0
% 7.36/2.75  #Strategies tried      : 1
% 7.36/2.75  
% 7.36/2.75  Timing (in seconds)
% 7.36/2.75  ----------------------
% 7.36/2.75  Preprocessing        : 0.62
% 7.36/2.75  Parsing              : 0.33
% 7.36/2.75  CNF conversion       : 0.05
% 7.36/2.75  Main loop            : 1.25
% 7.36/2.75  Inferencing          : 0.47
% 7.36/2.75  Reduction            : 0.36
% 7.36/2.75  Demodulation         : 0.24
% 7.36/2.75  BG Simplification    : 0.06
% 7.36/2.75  Subsumption          : 0.26
% 7.36/2.75  Abstraction          : 0.06
% 7.36/2.75  MUC search           : 0.00
% 7.36/2.75  Cooper               : 0.00
% 7.36/2.75  Total                : 1.92
% 7.36/2.75  Index Insertion      : 0.00
% 7.36/2.75  Index Deletion       : 0.00
% 7.36/2.75  Index Matching       : 0.00
% 7.36/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------

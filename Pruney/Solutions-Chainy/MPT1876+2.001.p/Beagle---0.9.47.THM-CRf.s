%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:50 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 479 expanded)
%              Number of leaves         :   32 ( 184 expanded)
%              Depth                    :   14
%              Number of atoms          :  356 (1930 expanded)
%              Number of equality atoms :   10 (  68 expanded)
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

tff(f_181,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_141,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v2_tdlat_3(B)
           => v2_pre_topc(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc15_tex_2)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc25_tex_2)).

tff(f_161,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v1_tdlat_3(B) )
           => ( ~ v2_struct_0(B)
              & v7_struct_0(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc31_tex_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_360,plain,(
    ! [A_82,B_83] :
      ( ~ v2_struct_0('#skF_1'(A_82,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | v1_xboole_0(B_83)
      | ~ l1_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_363,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_360])).

tff(c_366,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_363])).

tff(c_367,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_366])).

tff(c_377,plain,(
    ! [A_88,B_89] :
      ( u1_struct_0('#skF_1'(A_88,B_89)) = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(B_89)
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_380,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_377])).

tff(c_383,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_380])).

tff(c_384,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_383])).

tff(c_30,plain,(
    ! [A_19,B_23] :
      ( ~ v2_struct_0('#skF_1'(A_19,B_23))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | v1_xboole_0(B_23)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_394,plain,(
    ! [B_23] :
      ( ~ v2_struct_0('#skF_1'('#skF_1'('#skF_2','#skF_3'),B_23))
      | ~ m1_subset_1(B_23,k1_zfmisc_1('#skF_3'))
      | v1_xboole_0(B_23)
      | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
      | v2_struct_0('#skF_1'('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_30])).

tff(c_405,plain,(
    ! [B_23] :
      ( ~ v2_struct_0('#skF_1'('#skF_1'('#skF_2','#skF_3'),B_23))
      | ~ m1_subset_1(B_23,k1_zfmisc_1('#skF_3'))
      | v1_xboole_0(B_23)
      | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_394])).

tff(c_632,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_633,plain,(
    ! [A_105,B_106] :
      ( m1_pre_topc('#skF_1'(A_105,B_106),A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | v1_xboole_0(B_106)
      | ~ l1_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_637,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_633])).

tff(c_641,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_637])).

tff(c_642,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_641])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_657,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_642,c_4])).

tff(c_676,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_657])).

tff(c_678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_632,c_676])).

tff(c_680,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_459,plain,(
    ! [A_93,B_94] :
      ( m1_pre_topc('#skF_1'(A_93,B_94),A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | v1_xboole_0(B_94)
      | ~ l1_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_463,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_459])).

tff(c_469,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_463])).

tff(c_470,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_469])).

tff(c_54,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_58,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48])).

tff(c_86,plain,(
    ! [A_50,B_51] :
      ( m1_pre_topc('#skF_1'(A_50,B_51),A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(B_51)
      | ~ l1_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_88,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_86])).

tff(c_91,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_88])).

tff(c_92,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_91])).

tff(c_69,plain,(
    ! [A_44,B_45] :
      ( ~ v2_struct_0('#skF_1'(A_44,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | v1_xboole_0(B_45)
      | ~ l1_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_72,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_69])).

tff(c_75,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_72])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_75])).

tff(c_107,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_126,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_107])).

tff(c_127,plain,(
    ! [A_52,B_53] :
      ( u1_struct_0('#skF_1'(A_52,B_53)) = B_53
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(B_53)
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_130,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_127])).

tff(c_133,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_130])).

tff(c_134,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_133])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v7_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_152,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_6])).

tff(c_169,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_152])).

tff(c_173,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_179,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_173])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_179])).

tff(c_184,plain,(
    v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_42,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_22,plain,(
    ! [B_18,A_16] :
      ( v2_tdlat_3(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_tdlat_3(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_101,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_22])).

tff(c_118,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_101])).

tff(c_119,plain,(
    v2_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_118])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( v2_pre_topc(B_9)
      | ~ v2_tdlat_3(B_9)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_10])).

tff(c_122,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_104])).

tff(c_123,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_122])).

tff(c_172,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_123])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( v1_tdlat_3(B_12)
      | ~ v2_pre_topc(B_12)
      | ~ v7_struct_0(B_12)
      | v2_struct_0(B_12)
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_95,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_14])).

tff(c_110,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_95])).

tff(c_111,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_76,c_110])).

tff(c_187,plain,(
    v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_172,c_111])).

tff(c_309,plain,(
    ! [B_69,A_70] :
      ( v2_tex_2(u1_struct_0(B_69),A_70)
      | ~ v1_tdlat_3(B_69)
      | ~ m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_pre_topc(B_69,A_70)
      | v2_struct_0(B_69)
      | ~ l1_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_318,plain,(
    ! [A_70] :
      ( v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_70)
      | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_70)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_309])).

tff(c_323,plain,(
    ! [A_70] :
      ( v2_tex_2('#skF_3',A_70)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_70)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_134,c_318])).

tff(c_328,plain,(
    ! [A_71] :
      ( v2_tex_2('#skF_3',A_71)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_71)
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_323])).

tff(c_337,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_328])).

tff(c_343,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_92,c_337])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_58,c_343])).

tff(c_346,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_347,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | ~ v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_400,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_8])).

tff(c_406,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_347,c_400])).

tff(c_408,plain,(
    ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_547,plain,(
    ! [B_99,A_100] :
      ( v7_struct_0(B_99)
      | ~ v1_tdlat_3(B_99)
      | v2_struct_0(B_99)
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_tdlat_3(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_553,plain,
    ( v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_470,c_547])).

tff(c_560,plain,
    ( v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_553])).

tff(c_561,plain,(
    ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_367,c_408,c_560])).

tff(c_562,plain,(
    ! [B_101,A_102] :
      ( v1_tdlat_3(B_101)
      | ~ v2_tex_2(u1_struct_0(B_101),A_102)
      | ~ m1_subset_1(u1_struct_0(B_101),k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc(B_101,A_102)
      | v2_struct_0(B_101)
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_565,plain,(
    ! [A_102] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_102)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_102)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_562])).

tff(c_569,plain,(
    ! [A_102] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2('#skF_3',A_102)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_102)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_565])).

tff(c_608,plain,(
    ! [A_104] :
      ( ~ v2_tex_2('#skF_3',A_104)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_104)
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_561,c_569])).

tff(c_617,plain,
    ( ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_608])).

tff(c_623,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_470,c_346,c_617])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_623])).

tff(c_626,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_631,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_626])).

tff(c_692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:25:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.40  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.82/1.40  
% 2.82/1.40  %Foreground sorts:
% 2.82/1.40  
% 2.82/1.40  
% 2.82/1.40  %Background operators:
% 2.82/1.40  
% 2.82/1.40  
% 2.82/1.40  %Foreground operators:
% 2.82/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.40  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.82/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.82/1.40  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.82/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.82/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.40  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.82/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.40  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.82/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.82/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.82/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.40  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.82/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.40  
% 3.07/1.43  tff(f_181, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 3.07/1.43  tff(f_141, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 3.07/1.43  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.07/1.43  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.07/1.43  tff(f_44, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.07/1.43  tff(f_120, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 3.07/1.43  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v2_tdlat_3(B) => v2_pre_topc(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc15_tex_2)).
% 3.07/1.43  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & v7_struct_0(B)) & v2_pre_topc(B)) => ((~v2_struct_0(B) & v1_tdlat_3(B)) & v2_tdlat_3(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc25_tex_2)).
% 3.07/1.43  tff(f_161, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 3.07/1.43  tff(f_50, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.07/1.43  tff(f_106, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & v1_tdlat_3(B)) => (~v2_struct_0(B) & v7_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc31_tex_2)).
% 3.07/1.43  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.07/1.43  tff(c_38, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.07/1.43  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.07/1.43  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.07/1.43  tff(c_360, plain, (![A_82, B_83]: (~v2_struct_0('#skF_1'(A_82, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | v1_xboole_0(B_83) | ~l1_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.07/1.43  tff(c_363, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_360])).
% 3.07/1.43  tff(c_366, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_363])).
% 3.07/1.43  tff(c_367, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_366])).
% 3.07/1.43  tff(c_377, plain, (![A_88, B_89]: (u1_struct_0('#skF_1'(A_88, B_89))=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(B_89) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.07/1.43  tff(c_380, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_377])).
% 3.07/1.43  tff(c_383, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_380])).
% 3.07/1.43  tff(c_384, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_383])).
% 3.07/1.43  tff(c_30, plain, (![A_19, B_23]: (~v2_struct_0('#skF_1'(A_19, B_23)) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_19))) | v1_xboole_0(B_23) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.07/1.43  tff(c_394, plain, (![B_23]: (~v2_struct_0('#skF_1'('#skF_1'('#skF_2', '#skF_3'), B_23)) | ~m1_subset_1(B_23, k1_zfmisc_1('#skF_3')) | v1_xboole_0(B_23) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_384, c_30])).
% 3.07/1.43  tff(c_405, plain, (![B_23]: (~v2_struct_0('#skF_1'('#skF_1'('#skF_2', '#skF_3'), B_23)) | ~m1_subset_1(B_23, k1_zfmisc_1('#skF_3')) | v1_xboole_0(B_23) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_367, c_394])).
% 3.07/1.43  tff(c_632, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_405])).
% 3.07/1.43  tff(c_633, plain, (![A_105, B_106]: (m1_pre_topc('#skF_1'(A_105, B_106), A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | v1_xboole_0(B_106) | ~l1_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.07/1.43  tff(c_637, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_633])).
% 3.07/1.43  tff(c_641, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_637])).
% 3.07/1.43  tff(c_642, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_641])).
% 3.07/1.43  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.07/1.43  tff(c_657, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_642, c_4])).
% 3.07/1.43  tff(c_676, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_657])).
% 3.07/1.43  tff(c_678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_632, c_676])).
% 3.07/1.43  tff(c_680, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_405])).
% 3.07/1.43  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.07/1.43  tff(c_459, plain, (![A_93, B_94]: (m1_pre_topc('#skF_1'(A_93, B_94), A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | v1_xboole_0(B_94) | ~l1_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.07/1.43  tff(c_463, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_459])).
% 3.07/1.43  tff(c_469, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_463])).
% 3.07/1.43  tff(c_470, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_469])).
% 3.07/1.43  tff(c_54, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.07/1.43  tff(c_56, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 3.07/1.43  tff(c_48, plain, (~v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.07/1.43  tff(c_58, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48])).
% 3.07/1.43  tff(c_86, plain, (![A_50, B_51]: (m1_pre_topc('#skF_1'(A_50, B_51), A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.07/1.43  tff(c_88, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_86])).
% 3.07/1.43  tff(c_91, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_88])).
% 3.07/1.43  tff(c_92, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_91])).
% 3.07/1.43  tff(c_69, plain, (![A_44, B_45]: (~v2_struct_0('#skF_1'(A_44, B_45)) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | v1_xboole_0(B_45) | ~l1_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.07/1.43  tff(c_72, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_69])).
% 3.07/1.43  tff(c_75, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_72])).
% 3.07/1.43  tff(c_76, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_75])).
% 3.07/1.43  tff(c_107, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_92, c_4])).
% 3.07/1.43  tff(c_126, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_107])).
% 3.07/1.43  tff(c_127, plain, (![A_52, B_53]: (u1_struct_0('#skF_1'(A_52, B_53))=B_53 | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(B_53) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.07/1.43  tff(c_130, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_127])).
% 3.07/1.43  tff(c_133, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_130])).
% 3.07/1.43  tff(c_134, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_133])).
% 3.07/1.43  tff(c_6, plain, (![A_5]: (~v1_zfmisc_1(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v7_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.07/1.43  tff(c_152, plain, (~v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_6])).
% 3.07/1.43  tff(c_169, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_152])).
% 3.07/1.43  tff(c_173, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_169])).
% 3.07/1.43  tff(c_179, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_173])).
% 3.07/1.43  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_179])).
% 3.07/1.43  tff(c_184, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_169])).
% 3.07/1.43  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.07/1.43  tff(c_42, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.07/1.43  tff(c_22, plain, (![B_18, A_16]: (v2_tdlat_3(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16) | ~v2_tdlat_3(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.07/1.43  tff(c_101, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_92, c_22])).
% 3.07/1.43  tff(c_118, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_101])).
% 3.07/1.43  tff(c_119, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_118])).
% 3.07/1.43  tff(c_10, plain, (![B_9, A_7]: (v2_pre_topc(B_9) | ~v2_tdlat_3(B_9) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.07/1.43  tff(c_104, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_92, c_10])).
% 3.07/1.43  tff(c_122, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_104])).
% 3.07/1.43  tff(c_123, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_122])).
% 3.07/1.43  tff(c_172, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_123])).
% 3.07/1.43  tff(c_14, plain, (![B_12, A_10]: (v1_tdlat_3(B_12) | ~v2_pre_topc(B_12) | ~v7_struct_0(B_12) | v2_struct_0(B_12) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.07/1.43  tff(c_95, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_92, c_14])).
% 3.07/1.43  tff(c_110, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_95])).
% 3.07/1.43  tff(c_111, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_76, c_110])).
% 3.07/1.43  tff(c_187, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_172, c_111])).
% 3.07/1.43  tff(c_309, plain, (![B_69, A_70]: (v2_tex_2(u1_struct_0(B_69), A_70) | ~v1_tdlat_3(B_69) | ~m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_pre_topc(B_69, A_70) | v2_struct_0(B_69) | ~l1_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.07/1.43  tff(c_318, plain, (![A_70]: (v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_70) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_70) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_70) | v2_struct_0(A_70))), inference(superposition, [status(thm), theory('equality')], [c_134, c_309])).
% 3.07/1.43  tff(c_323, plain, (![A_70]: (v2_tex_2('#skF_3', A_70) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_70) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_70) | v2_struct_0(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_134, c_318])).
% 3.07/1.43  tff(c_328, plain, (![A_71]: (v2_tex_2('#skF_3', A_71) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_71) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(negUnitSimplification, [status(thm)], [c_76, c_323])).
% 3.07/1.43  tff(c_337, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_328])).
% 3.07/1.43  tff(c_343, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_92, c_337])).
% 3.07/1.43  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_58, c_343])).
% 3.07/1.43  tff(c_346, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 3.07/1.43  tff(c_347, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 3.07/1.43  tff(c_8, plain, (![A_6]: (v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | ~v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.07/1.43  tff(c_400, plain, (v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_384, c_8])).
% 3.07/1.43  tff(c_406, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_347, c_400])).
% 3.07/1.43  tff(c_408, plain, (~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_406])).
% 3.07/1.43  tff(c_547, plain, (![B_99, A_100]: (v7_struct_0(B_99) | ~v1_tdlat_3(B_99) | v2_struct_0(B_99) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100) | ~v2_tdlat_3(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.07/1.43  tff(c_553, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_470, c_547])).
% 3.07/1.43  tff(c_560, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_553])).
% 3.07/1.43  tff(c_561, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_367, c_408, c_560])).
% 3.07/1.43  tff(c_562, plain, (![B_101, A_102]: (v1_tdlat_3(B_101) | ~v2_tex_2(u1_struct_0(B_101), A_102) | ~m1_subset_1(u1_struct_0(B_101), k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_pre_topc(B_101, A_102) | v2_struct_0(B_101) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.07/1.43  tff(c_565, plain, (![A_102]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_102) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_102) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(superposition, [status(thm), theory('equality')], [c_384, c_562])).
% 3.07/1.43  tff(c_569, plain, (![A_102]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2('#skF_3', A_102) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_102) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_384, c_565])).
% 3.07/1.43  tff(c_608, plain, (![A_104]: (~v2_tex_2('#skF_3', A_104) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_104))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_104) | ~l1_pre_topc(A_104) | v2_struct_0(A_104))), inference(negUnitSimplification, [status(thm)], [c_367, c_561, c_569])).
% 3.07/1.43  tff(c_617, plain, (~v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_608])).
% 3.07/1.43  tff(c_623, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_470, c_346, c_617])).
% 3.07/1.43  tff(c_625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_623])).
% 3.07/1.43  tff(c_626, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_406])).
% 3.07/1.43  tff(c_631, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_626])).
% 3.07/1.43  tff(c_692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_680, c_631])).
% 3.07/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.43  
% 3.07/1.43  Inference rules
% 3.07/1.43  ----------------------
% 3.07/1.43  #Ref     : 0
% 3.07/1.43  #Sup     : 106
% 3.07/1.43  #Fact    : 0
% 3.07/1.43  #Define  : 0
% 3.07/1.43  #Split   : 6
% 3.07/1.43  #Chain   : 0
% 3.07/1.43  #Close   : 0
% 3.07/1.43  
% 3.07/1.43  Ordering : KBO
% 3.07/1.43  
% 3.07/1.43  Simplification rules
% 3.07/1.43  ----------------------
% 3.07/1.43  #Subsume      : 10
% 3.07/1.43  #Demod        : 108
% 3.07/1.43  #Tautology    : 21
% 3.07/1.43  #SimpNegUnit  : 64
% 3.07/1.43  #BackRed      : 0
% 3.07/1.43  
% 3.07/1.43  #Partial instantiations: 0
% 3.07/1.43  #Strategies tried      : 1
% 3.07/1.43  
% 3.07/1.43  Timing (in seconds)
% 3.07/1.43  ----------------------
% 3.07/1.43  Preprocessing        : 0.31
% 3.07/1.43  Parsing              : 0.17
% 3.07/1.43  CNF conversion       : 0.02
% 3.07/1.43  Main loop            : 0.35
% 3.07/1.43  Inferencing          : 0.13
% 3.07/1.43  Reduction            : 0.11
% 3.07/1.43  Demodulation         : 0.07
% 3.07/1.43  BG Simplification    : 0.02
% 3.07/1.43  Subsumption          : 0.07
% 3.07/1.43  Abstraction          : 0.01
% 3.07/1.43  MUC search           : 0.00
% 3.07/1.43  Cooper               : 0.00
% 3.07/1.44  Total                : 0.71
% 3.07/1.44  Index Insertion      : 0.00
% 3.07/1.44  Index Deletion       : 0.00
% 3.07/1.44  Index Matching       : 0.00
% 3.07/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

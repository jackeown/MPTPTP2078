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
% DateTime   : Thu Dec  3 10:29:51 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 566 expanded)
%              Number of leaves         :   32 ( 217 expanded)
%              Depth                    :   16
%              Number of atoms          :  347 (2307 expanded)
%              Number of equality atoms :   14 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_180,negated_conjecture,(
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

tff(f_140,axiom,(
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

tff(f_160,axiom,(
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

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_374,plain,(
    ! [A_85,B_86] :
      ( m1_pre_topc('#skF_1'(A_85,B_86),A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | v1_xboole_0(B_86)
      | ~ l1_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_376,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_374])).

tff(c_379,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_376])).

tff(c_380,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_379])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_395,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_380,c_6])).

tff(c_413,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_395])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_60,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52])).

tff(c_131,plain,(
    ! [A_53,B_54] :
      ( m1_pre_topc('#skF_1'(A_53,B_54),A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(B_54)
      | ~ l1_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_135,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_131])).

tff(c_139,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_135])).

tff(c_140,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_139])).

tff(c_82,plain,(
    ! [A_47,B_48] :
      ( ~ v2_struct_0('#skF_1'(A_47,B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | v1_xboole_0(B_48)
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_85,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_82])).

tff(c_88,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_85])).

tff(c_89,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_88])).

tff(c_155,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_6])).

tff(c_173,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_155])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_152,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_170,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_152])).

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

tff(c_146,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_14])).

tff(c_162,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_146])).

tff(c_163,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_89,c_162])).

tff(c_179,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_163])).

tff(c_180,plain,(
    ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_98,plain,(
    ! [A_51,B_52] :
      ( u1_struct_0('#skF_1'(A_51,B_52)) = B_52
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | v1_xboole_0(B_52)
      | ~ l1_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_101,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_104,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_101])).

tff(c_105,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_104])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_8])).

tff(c_128,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_118])).

tff(c_188,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_128])).

tff(c_191,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_191])).

tff(c_196,plain,(
    v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_291,plain,(
    ! [B_61,A_62] :
      ( v2_tex_2(u1_struct_0(B_61),A_62)
      | ~ v1_tdlat_3(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc(B_61,A_62)
      | v2_struct_0(B_61)
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_300,plain,(
    ! [A_62] :
      ( v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_62)
      | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_62)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_291])).

tff(c_305,plain,(
    ! [A_62] :
      ( v2_tex_2('#skF_3',A_62)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_62)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_105,c_300])).

tff(c_317,plain,(
    ! [A_66] :
      ( v2_tex_2('#skF_3',A_66)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_66)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_305])).

tff(c_326,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_317])).

tff(c_332,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_140,c_326])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_62,c_332])).

tff(c_336,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_335,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_358,plain,(
    ! [A_81,B_82] :
      ( ~ v2_struct_0('#skF_1'(A_81,B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(B_82)
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_361,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_358])).

tff(c_364,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_361])).

tff(c_365,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_364])).

tff(c_392,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_380,c_2])).

tff(c_410,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_392])).

tff(c_46,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_26,plain,(
    ! [B_17,A_15] :
      ( v2_tdlat_3(B_17)
      | ~ m1_pre_topc(B_17,A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_tdlat_3(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_389,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_380,c_26])).

tff(c_406,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_389])).

tff(c_407,plain,(
    v2_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_406])).

tff(c_22,plain,(
    ! [A_14] :
      ( v7_struct_0(A_14)
      | ~ v2_tdlat_3(A_14)
      | ~ v1_tdlat_3(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_386,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_380,c_14])).

tff(c_402,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_386])).

tff(c_403,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_365,c_402])).

tff(c_421,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_403])).

tff(c_422,plain,(
    ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_425,plain,
    ( ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_422])).

tff(c_428,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_410,c_407,c_425])).

tff(c_429,plain,(
    ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_428])).

tff(c_430,plain,(
    ! [A_87,B_88] :
      ( u1_struct_0('#skF_1'(A_87,B_88)) = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(B_88)
      | ~ l1_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_433,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_430])).

tff(c_436,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_433])).

tff(c_437,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_436])).

tff(c_543,plain,(
    ! [B_95,A_96] :
      ( v1_tdlat_3(B_95)
      | ~ v2_tex_2(u1_struct_0(B_95),A_96)
      | ~ m1_subset_1(u1_struct_0(B_95),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_pre_topc(B_95,A_96)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_552,plain,(
    ! [A_96] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_96)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_96)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_543])).

tff(c_556,plain,(
    ! [A_96] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2('#skF_3',A_96)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_96)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_552])).

tff(c_562,plain,(
    ! [A_98] :
      ( ~ v2_tex_2('#skF_3',A_98)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_98)
      | ~ l1_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_429,c_556])).

tff(c_571,plain,
    ( ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_562])).

tff(c_577,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_380,c_335,c_571])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_577])).

tff(c_581,plain,(
    v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_584,plain,(
    ! [A_99,B_100] :
      ( u1_struct_0('#skF_1'(A_99,B_100)) = B_100
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | v1_xboole_0(B_100)
      | ~ l1_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_587,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_584])).

tff(c_590,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_587])).

tff(c_591,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_590])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_609,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_10])).

tff(c_626,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_609])).

tff(c_627,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_626])).

tff(c_631,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_627])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.47  
% 3.20/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.47  
% 3.21/1.47  %Foreground sorts:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Background operators:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Foreground operators:
% 3.21/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.47  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.21/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.47  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.21/1.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.21/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.47  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.21/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.47  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.21/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.21/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.21/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.47  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.21/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.47  
% 3.21/1.49  tff(f_180, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.21/1.49  tff(f_140, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 3.21/1.49  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.21/1.49  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.21/1.49  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.21/1.49  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & v7_struct_0(B)) & v2_pre_topc(B)) => ((~v2_struct_0(B) & v1_tdlat_3(B)) & v2_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc25_tex_2)).
% 3.21/1.49  tff(f_53, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.21/1.49  tff(f_160, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 3.21/1.49  tff(f_119, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 3.21/1.49  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_1)).
% 3.21/1.49  tff(f_59, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.21/1.49  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.21/1.49  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.21/1.49  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.21/1.49  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.21/1.49  tff(c_374, plain, (![A_85, B_86]: (m1_pre_topc('#skF_1'(A_85, B_86), A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | v1_xboole_0(B_86) | ~l1_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.21/1.49  tff(c_376, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_374])).
% 3.21/1.49  tff(c_379, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_376])).
% 3.21/1.49  tff(c_380, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_379])).
% 3.21/1.49  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.49  tff(c_395, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_380, c_6])).
% 3.21/1.49  tff(c_413, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_395])).
% 3.21/1.49  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.49  tff(c_58, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.21/1.49  tff(c_60, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 3.21/1.49  tff(c_52, plain, (~v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.21/1.49  tff(c_62, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52])).
% 3.21/1.49  tff(c_131, plain, (![A_53, B_54]: (m1_pre_topc('#skF_1'(A_53, B_54), A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(B_54) | ~l1_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.21/1.49  tff(c_135, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_131])).
% 3.21/1.49  tff(c_139, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_135])).
% 3.21/1.49  tff(c_140, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_139])).
% 3.21/1.49  tff(c_82, plain, (![A_47, B_48]: (~v2_struct_0('#skF_1'(A_47, B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | v1_xboole_0(B_48) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.21/1.49  tff(c_85, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_82])).
% 3.21/1.49  tff(c_88, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_85])).
% 3.21/1.49  tff(c_89, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_88])).
% 3.21/1.49  tff(c_155, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_140, c_6])).
% 3.21/1.49  tff(c_173, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_155])).
% 3.21/1.49  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.21/1.49  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.21/1.49  tff(c_152, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_140, c_2])).
% 3.21/1.49  tff(c_170, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_152])).
% 3.21/1.49  tff(c_14, plain, (![B_12, A_10]: (v1_tdlat_3(B_12) | ~v2_pre_topc(B_12) | ~v7_struct_0(B_12) | v2_struct_0(B_12) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.21/1.49  tff(c_146, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_140, c_14])).
% 3.21/1.49  tff(c_162, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_146])).
% 3.21/1.49  tff(c_163, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_89, c_162])).
% 3.21/1.49  tff(c_179, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_163])).
% 3.21/1.49  tff(c_180, plain, (~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_179])).
% 3.21/1.49  tff(c_98, plain, (![A_51, B_52]: (u1_struct_0('#skF_1'(A_51, B_52))=B_52 | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | v1_xboole_0(B_52) | ~l1_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.21/1.49  tff(c_101, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_98])).
% 3.21/1.49  tff(c_104, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_101])).
% 3.21/1.49  tff(c_105, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_104])).
% 3.21/1.49  tff(c_8, plain, (![A_8]: (~v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.49  tff(c_118, plain, (~v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_8])).
% 3.21/1.49  tff(c_128, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_118])).
% 3.21/1.49  tff(c_188, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_180, c_128])).
% 3.21/1.49  tff(c_191, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_188])).
% 3.21/1.49  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_191])).
% 3.21/1.49  tff(c_196, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_179])).
% 3.21/1.49  tff(c_291, plain, (![B_61, A_62]: (v2_tex_2(u1_struct_0(B_61), A_62) | ~v1_tdlat_3(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc(B_61, A_62) | v2_struct_0(B_61) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.21/1.49  tff(c_300, plain, (![A_62]: (v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_62) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_62) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_105, c_291])).
% 3.21/1.49  tff(c_305, plain, (![A_62]: (v2_tex_2('#skF_3', A_62) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_62) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_105, c_300])).
% 3.21/1.49  tff(c_317, plain, (![A_66]: (v2_tex_2('#skF_3', A_66) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_66) | ~l1_pre_topc(A_66) | v2_struct_0(A_66))), inference(negUnitSimplification, [status(thm)], [c_89, c_305])).
% 3.21/1.49  tff(c_326, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_317])).
% 3.21/1.49  tff(c_332, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_140, c_326])).
% 3.21/1.49  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_62, c_332])).
% 3.21/1.49  tff(c_336, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 3.21/1.49  tff(c_335, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 3.21/1.49  tff(c_358, plain, (![A_81, B_82]: (~v2_struct_0('#skF_1'(A_81, B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(B_82) | ~l1_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.21/1.49  tff(c_361, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_358])).
% 3.21/1.49  tff(c_364, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_361])).
% 3.21/1.49  tff(c_365, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_364])).
% 3.21/1.49  tff(c_392, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_380, c_2])).
% 3.21/1.49  tff(c_410, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_392])).
% 3.21/1.49  tff(c_46, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.21/1.49  tff(c_26, plain, (![B_17, A_15]: (v2_tdlat_3(B_17) | ~m1_pre_topc(B_17, A_15) | ~l1_pre_topc(A_15) | ~v2_tdlat_3(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.21/1.49  tff(c_389, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_380, c_26])).
% 3.21/1.49  tff(c_406, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_389])).
% 3.21/1.49  tff(c_407, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_406])).
% 3.21/1.49  tff(c_22, plain, (![A_14]: (v7_struct_0(A_14) | ~v2_tdlat_3(A_14) | ~v1_tdlat_3(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.21/1.49  tff(c_386, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_380, c_14])).
% 3.21/1.49  tff(c_402, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_386])).
% 3.21/1.49  tff(c_403, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_365, c_402])).
% 3.21/1.49  tff(c_421, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_410, c_403])).
% 3.21/1.49  tff(c_422, plain, (~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_421])).
% 3.21/1.49  tff(c_425, plain, (~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_422])).
% 3.21/1.49  tff(c_428, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_410, c_407, c_425])).
% 3.21/1.49  tff(c_429, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_365, c_428])).
% 3.21/1.49  tff(c_430, plain, (![A_87, B_88]: (u1_struct_0('#skF_1'(A_87, B_88))=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(B_88) | ~l1_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.21/1.49  tff(c_433, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_430])).
% 3.21/1.49  tff(c_436, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_433])).
% 3.21/1.49  tff(c_437, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_436])).
% 3.21/1.49  tff(c_543, plain, (![B_95, A_96]: (v1_tdlat_3(B_95) | ~v2_tex_2(u1_struct_0(B_95), A_96) | ~m1_subset_1(u1_struct_0(B_95), k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_pre_topc(B_95, A_96) | v2_struct_0(B_95) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.21/1.49  tff(c_552, plain, (![A_96]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_96) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_96) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(superposition, [status(thm), theory('equality')], [c_437, c_543])).
% 3.21/1.49  tff(c_556, plain, (![A_96]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2('#skF_3', A_96) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_96) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_552])).
% 3.21/1.49  tff(c_562, plain, (![A_98]: (~v2_tex_2('#skF_3', A_98) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_98) | ~l1_pre_topc(A_98) | v2_struct_0(A_98))), inference(negUnitSimplification, [status(thm)], [c_365, c_429, c_556])).
% 3.21/1.49  tff(c_571, plain, (~v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_562])).
% 3.21/1.49  tff(c_577, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_380, c_335, c_571])).
% 3.21/1.49  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_577])).
% 3.21/1.49  tff(c_581, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_421])).
% 3.21/1.49  tff(c_584, plain, (![A_99, B_100]: (u1_struct_0('#skF_1'(A_99, B_100))=B_100 | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | v1_xboole_0(B_100) | ~l1_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.21/1.49  tff(c_587, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_584])).
% 3.21/1.49  tff(c_590, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_587])).
% 3.21/1.49  tff(c_591, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_590])).
% 3.21/1.49  tff(c_10, plain, (![A_9]: (v1_zfmisc_1(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.21/1.49  tff(c_609, plain, (v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_591, c_10])).
% 3.21/1.49  tff(c_626, plain, (v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_609])).
% 3.21/1.49  tff(c_627, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_336, c_626])).
% 3.21/1.49  tff(c_631, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_627])).
% 3.21/1.49  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_413, c_631])).
% 3.21/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  Inference rules
% 3.21/1.49  ----------------------
% 3.21/1.49  #Ref     : 0
% 3.21/1.49  #Sup     : 99
% 3.21/1.49  #Fact    : 0
% 3.21/1.49  #Define  : 0
% 3.21/1.49  #Split   : 3
% 3.21/1.49  #Chain   : 0
% 3.21/1.49  #Close   : 0
% 3.21/1.49  
% 3.21/1.49  Ordering : KBO
% 3.21/1.49  
% 3.21/1.49  Simplification rules
% 3.21/1.49  ----------------------
% 3.21/1.49  #Subsume      : 5
% 3.21/1.49  #Demod        : 99
% 3.21/1.49  #Tautology    : 25
% 3.21/1.49  #SimpNegUnit  : 49
% 3.21/1.49  #BackRed      : 0
% 3.21/1.49  
% 3.21/1.49  #Partial instantiations: 0
% 3.21/1.49  #Strategies tried      : 1
% 3.21/1.49  
% 3.21/1.49  Timing (in seconds)
% 3.21/1.49  ----------------------
% 3.21/1.50  Preprocessing        : 0.33
% 3.21/1.50  Parsing              : 0.18
% 3.21/1.50  CNF conversion       : 0.02
% 3.21/1.50  Main loop            : 0.37
% 3.21/1.50  Inferencing          : 0.14
% 3.21/1.50  Reduction            : 0.11
% 3.21/1.50  Demodulation         : 0.07
% 3.21/1.50  BG Simplification    : 0.02
% 3.21/1.50  Subsumption          : 0.07
% 3.21/1.50  Abstraction          : 0.02
% 3.21/1.50  MUC search           : 0.00
% 3.21/1.50  Cooper               : 0.00
% 3.21/1.50  Total                : 0.76
% 3.21/1.50  Index Insertion      : 0.00
% 3.21/1.50  Index Deletion       : 0.00
% 3.21/1.50  Index Matching       : 0.00
% 3.21/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

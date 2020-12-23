%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:50 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 434 expanded)
%              Number of leaves         :   32 ( 168 expanded)
%              Depth                    :   15
%              Number of atoms          :  304 (1698 expanded)
%              Number of equality atoms :   10 (  55 expanded)
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

tff(f_176,negated_conjecture,(
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

tff(f_136,axiom,(
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

tff(f_156,axiom,(
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

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_101,axiom,(
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

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_372,plain,(
    ! [A_81,B_82] :
      ( m1_pre_topc('#skF_1'(A_81,B_82),A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(B_82)
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_374,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_372])).

tff(c_377,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_374])).

tff(c_378,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_377])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_413,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_378,c_6])).

tff(c_423,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_413])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_62,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_64,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54])).

tff(c_141,plain,(
    ! [A_49,B_50] :
      ( m1_pre_topc('#skF_1'(A_49,B_50),A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | v1_xboole_0(B_50)
      | ~ l1_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_145,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_141])).

tff(c_149,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_145])).

tff(c_150,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_149])).

tff(c_92,plain,(
    ! [A_43,B_44] :
      ( ~ v2_struct_0('#skF_1'(A_43,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | v1_xboole_0(B_44)
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_95,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_92])).

tff(c_98,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_95])).

tff(c_99,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_98])).

tff(c_159,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_6])).

tff(c_169,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_159])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_156,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_166,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_156])).

tff(c_108,plain,(
    ! [A_47,B_48] :
      ( u1_struct_0('#skF_1'(A_47,B_48)) = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | v1_xboole_0(B_48)
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_111,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_108])).

tff(c_114,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_111])).

tff(c_115,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_114])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_128,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_8])).

tff(c_138,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_128])).

tff(c_175,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_178,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_175])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_178])).

tff(c_183,plain,(
    v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_14,plain,(
    ! [A_10] :
      ( v1_tdlat_3(A_10)
      | ~ v2_pre_topc(A_10)
      | ~ v7_struct_0(A_10)
      | v2_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_187,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_183,c_14])).

tff(c_193,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_166,c_187])).

tff(c_194,plain,(
    v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_193])).

tff(c_280,plain,(
    ! [B_60,A_61] :
      ( v2_tex_2(u1_struct_0(B_60),A_61)
      | ~ v1_tdlat_3(B_60)
      | ~ m1_subset_1(u1_struct_0(B_60),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(B_60,A_61)
      | v2_struct_0(B_60)
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_289,plain,(
    ! [A_61] :
      ( v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_61)
      | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_61)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_280])).

tff(c_294,plain,(
    ! [A_61] :
      ( v2_tex_2('#skF_3',A_61)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_61)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_115,c_289])).

tff(c_299,plain,(
    ! [A_62] :
      ( v2_tex_2('#skF_3',A_62)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_62)
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_294])).

tff(c_308,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_299])).

tff(c_314,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_150,c_308])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_64,c_314])).

tff(c_317,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_356,plain,(
    ! [A_77,B_78] :
      ( ~ v2_struct_0('#skF_1'(A_77,B_78))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(B_78)
      | ~ l1_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_359,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_356])).

tff(c_362,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_359])).

tff(c_363,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_362])).

tff(c_410,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_378,c_2])).

tff(c_420,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_410])).

tff(c_48,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_28,plain,(
    ! [B_15,A_13] :
      ( v2_tdlat_3(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_tdlat_3(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_407,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_378,c_28])).

tff(c_416,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_407])).

tff(c_417,plain,(
    v2_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_416])).

tff(c_24,plain,(
    ! [A_12] :
      ( v7_struct_0(A_12)
      | ~ v2_tdlat_3(A_12)
      | ~ v1_tdlat_3(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_318,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_364,plain,(
    ! [A_79,B_80] :
      ( u1_struct_0('#skF_1'(A_79,B_80)) = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | v1_xboole_0(B_80)
      | ~ l1_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_367,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_364])).

tff(c_370,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_367])).

tff(c_371,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_370])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_396,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_10])).

tff(c_403,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_318,c_396])).

tff(c_428,plain,(
    ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_431,plain,
    ( ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_428])).

tff(c_434,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_420,c_417,c_431])).

tff(c_435,plain,(
    ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_434])).

tff(c_438,plain,(
    ! [B_83,A_84] :
      ( v1_tdlat_3(B_83)
      | ~ v2_tex_2(u1_struct_0(B_83),A_84)
      | ~ m1_subset_1(u1_struct_0(B_83),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_pre_topc(B_83,A_84)
      | v2_struct_0(B_83)
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_441,plain,(
    ! [A_84] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_84)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_84)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_438])).

tff(c_445,plain,(
    ! [A_84] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2('#skF_3',A_84)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_84)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_441])).

tff(c_490,plain,(
    ! [A_88] :
      ( ~ v2_tex_2('#skF_3',A_88)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_88)
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_435,c_445])).

tff(c_499,plain,
    ( ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_490])).

tff(c_505,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_378,c_317,c_499])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_505])).

tff(c_508,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_526,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_508])).

tff(c_530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.38  
% 2.56/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.39  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.56/1.39  
% 2.56/1.39  %Foreground sorts:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Background operators:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Foreground operators:
% 2.56/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.39  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.56/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.39  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.56/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.56/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.56/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.56/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.56/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.39  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.56/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.39  
% 2.85/1.41  tff(f_176, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.85/1.41  tff(f_136, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 2.85/1.41  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.85/1.41  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.85/1.41  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.85/1.41  tff(f_53, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.85/1.41  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A)) => (((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tex_1)).
% 2.85/1.41  tff(f_156, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.85/1.41  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 2.85/1.41  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_1)).
% 2.85/1.41  tff(f_59, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.85/1.41  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.85/1.41  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.85/1.41  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.85/1.41  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.85/1.41  tff(c_372, plain, (![A_81, B_82]: (m1_pre_topc('#skF_1'(A_81, B_82), A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(B_82) | ~l1_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.41  tff(c_374, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_372])).
% 2.85/1.41  tff(c_377, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_374])).
% 2.85/1.41  tff(c_378, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_377])).
% 2.85/1.41  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.85/1.41  tff(c_413, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_378, c_6])).
% 2.85/1.41  tff(c_423, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_413])).
% 2.85/1.41  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.85/1.41  tff(c_60, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.85/1.41  tff(c_62, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 2.85/1.41  tff(c_54, plain, (~v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.85/1.41  tff(c_64, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54])).
% 2.85/1.41  tff(c_141, plain, (![A_49, B_50]: (m1_pre_topc('#skF_1'(A_49, B_50), A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | v1_xboole_0(B_50) | ~l1_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.41  tff(c_145, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_141])).
% 2.85/1.41  tff(c_149, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_145])).
% 2.85/1.41  tff(c_150, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_149])).
% 2.85/1.41  tff(c_92, plain, (![A_43, B_44]: (~v2_struct_0('#skF_1'(A_43, B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | v1_xboole_0(B_44) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.41  tff(c_95, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_92])).
% 2.85/1.41  tff(c_98, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_95])).
% 2.85/1.41  tff(c_99, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_98])).
% 2.85/1.41  tff(c_159, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_150, c_6])).
% 2.85/1.41  tff(c_169, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_159])).
% 2.85/1.41  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.85/1.41  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.85/1.41  tff(c_156, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_150, c_2])).
% 2.85/1.41  tff(c_166, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_156])).
% 2.85/1.41  tff(c_108, plain, (![A_47, B_48]: (u1_struct_0('#skF_1'(A_47, B_48))=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | v1_xboole_0(B_48) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.41  tff(c_111, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_108])).
% 2.85/1.41  tff(c_114, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_111])).
% 2.85/1.41  tff(c_115, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_114])).
% 2.85/1.41  tff(c_8, plain, (![A_8]: (~v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.85/1.41  tff(c_128, plain, (~v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_8])).
% 2.85/1.41  tff(c_138, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_128])).
% 2.85/1.41  tff(c_175, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_138])).
% 2.85/1.41  tff(c_178, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_175])).
% 2.85/1.41  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_178])).
% 2.85/1.41  tff(c_183, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_138])).
% 2.85/1.41  tff(c_14, plain, (![A_10]: (v1_tdlat_3(A_10) | ~v2_pre_topc(A_10) | ~v7_struct_0(A_10) | v2_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.85/1.41  tff(c_187, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_183, c_14])).
% 2.85/1.41  tff(c_193, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_166, c_187])).
% 2.85/1.41  tff(c_194, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_99, c_193])).
% 2.85/1.41  tff(c_280, plain, (![B_60, A_61]: (v2_tex_2(u1_struct_0(B_60), A_61) | ~v1_tdlat_3(B_60) | ~m1_subset_1(u1_struct_0(B_60), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc(B_60, A_61) | v2_struct_0(B_60) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.85/1.41  tff(c_289, plain, (![A_61]: (v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_61) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_61) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_115, c_280])).
% 2.85/1.41  tff(c_294, plain, (![A_61]: (v2_tex_2('#skF_3', A_61) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_61) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_115, c_289])).
% 2.85/1.41  tff(c_299, plain, (![A_62]: (v2_tex_2('#skF_3', A_62) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_62) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(negUnitSimplification, [status(thm)], [c_99, c_294])).
% 2.85/1.41  tff(c_308, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_299])).
% 2.85/1.41  tff(c_314, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_150, c_308])).
% 2.85/1.41  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_64, c_314])).
% 2.85/1.41  tff(c_317, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 2.85/1.41  tff(c_356, plain, (![A_77, B_78]: (~v2_struct_0('#skF_1'(A_77, B_78)) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(B_78) | ~l1_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.41  tff(c_359, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_356])).
% 2.85/1.41  tff(c_362, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_359])).
% 2.85/1.41  tff(c_363, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_362])).
% 2.85/1.41  tff(c_410, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_378, c_2])).
% 2.85/1.41  tff(c_420, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_410])).
% 2.85/1.41  tff(c_48, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.85/1.41  tff(c_28, plain, (![B_15, A_13]: (v2_tdlat_3(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13) | ~v2_tdlat_3(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.85/1.41  tff(c_407, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_378, c_28])).
% 2.85/1.41  tff(c_416, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_407])).
% 2.85/1.41  tff(c_417, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_416])).
% 2.85/1.41  tff(c_24, plain, (![A_12]: (v7_struct_0(A_12) | ~v2_tdlat_3(A_12) | ~v1_tdlat_3(A_12) | ~v2_pre_topc(A_12) | v2_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.85/1.41  tff(c_318, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 2.85/1.41  tff(c_364, plain, (![A_79, B_80]: (u1_struct_0('#skF_1'(A_79, B_80))=B_80 | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | v1_xboole_0(B_80) | ~l1_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.41  tff(c_367, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_364])).
% 2.85/1.41  tff(c_370, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_367])).
% 2.85/1.41  tff(c_371, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_370])).
% 2.85/1.41  tff(c_10, plain, (![A_9]: (v1_zfmisc_1(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.41  tff(c_396, plain, (v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_10])).
% 2.85/1.41  tff(c_403, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_318, c_396])).
% 2.85/1.41  tff(c_428, plain, (~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_403])).
% 2.85/1.41  tff(c_431, plain, (~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_428])).
% 2.85/1.41  tff(c_434, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_420, c_417, c_431])).
% 2.85/1.41  tff(c_435, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_363, c_434])).
% 2.85/1.41  tff(c_438, plain, (![B_83, A_84]: (v1_tdlat_3(B_83) | ~v2_tex_2(u1_struct_0(B_83), A_84) | ~m1_subset_1(u1_struct_0(B_83), k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_pre_topc(B_83, A_84) | v2_struct_0(B_83) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.85/1.41  tff(c_441, plain, (![A_84]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_84) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_84) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_371, c_438])).
% 2.85/1.41  tff(c_445, plain, (![A_84]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2('#skF_3', A_84) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_84) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_441])).
% 2.85/1.41  tff(c_490, plain, (![A_88]: (~v2_tex_2('#skF_3', A_88) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_88) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(negUnitSimplification, [status(thm)], [c_363, c_435, c_445])).
% 2.85/1.41  tff(c_499, plain, (~v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_490])).
% 2.85/1.41  tff(c_505, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_378, c_317, c_499])).
% 2.85/1.41  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_505])).
% 2.85/1.41  tff(c_508, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_403])).
% 2.85/1.41  tff(c_526, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_508])).
% 2.85/1.41  tff(c_530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_423, c_526])).
% 2.85/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.41  
% 2.85/1.41  Inference rules
% 2.85/1.41  ----------------------
% 2.85/1.41  #Ref     : 0
% 2.85/1.41  #Sup     : 85
% 2.85/1.41  #Fact    : 0
% 2.85/1.41  #Define  : 0
% 2.85/1.41  #Split   : 3
% 2.85/1.41  #Chain   : 0
% 2.85/1.41  #Close   : 0
% 2.85/1.41  
% 2.85/1.41  Ordering : KBO
% 2.85/1.41  
% 2.85/1.41  Simplification rules
% 2.85/1.41  ----------------------
% 2.85/1.41  #Subsume      : 3
% 2.85/1.41  #Demod        : 71
% 2.85/1.41  #Tautology    : 27
% 2.85/1.41  #SimpNegUnit  : 35
% 2.85/1.41  #BackRed      : 0
% 2.85/1.41  
% 2.85/1.41  #Partial instantiations: 0
% 2.85/1.41  #Strategies tried      : 1
% 2.85/1.41  
% 2.85/1.41  Timing (in seconds)
% 2.85/1.41  ----------------------
% 2.85/1.41  Preprocessing        : 0.32
% 2.85/1.41  Parsing              : 0.17
% 2.85/1.41  CNF conversion       : 0.02
% 2.85/1.41  Main loop            : 0.30
% 2.85/1.41  Inferencing          : 0.11
% 2.85/1.41  Reduction            : 0.09
% 2.85/1.41  Demodulation         : 0.06
% 2.85/1.41  BG Simplification    : 0.02
% 2.85/1.41  Subsumption          : 0.06
% 2.85/1.41  Abstraction          : 0.01
% 2.85/1.41  MUC search           : 0.00
% 2.85/1.41  Cooper               : 0.00
% 2.85/1.41  Total                : 0.67
% 2.85/1.41  Index Insertion      : 0.00
% 2.85/1.41  Index Deletion       : 0.00
% 2.85/1.41  Index Matching       : 0.00
% 2.85/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

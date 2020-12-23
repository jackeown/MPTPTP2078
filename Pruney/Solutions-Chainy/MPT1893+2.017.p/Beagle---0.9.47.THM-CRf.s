%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:28 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 456 expanded)
%              Number of leaves         :   31 ( 167 expanded)
%              Depth                    :   11
%              Number of atoms          :  179 (1335 expanded)
%              Number of equality atoms :   20 ( 185 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_23] :
      ( u1_struct_0(A_23) = k2_struct_0(A_23)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [A_24] :
      ( u1_struct_0(A_24) = k2_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_60,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_61,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40])).

tff(c_102,plain,(
    ! [A_32,B_33] :
      ( k2_pre_topc(A_32,B_33) = B_33
      | ~ v4_pre_topc(B_33,A_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_111,plain,(
    ! [B_33] :
      ( k2_pre_topc('#skF_3',B_33) = B_33
      | ~ v4_pre_topc(B_33,'#skF_3')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_102])).

tff(c_116,plain,(
    ! [B_34] :
      ( k2_pre_topc('#skF_3',B_34) = B_34
      | ~ v4_pre_topc(B_34,'#skF_3')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_111])).

tff(c_120,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_116])).

tff(c_121,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_38,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_55,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_231,plain,(
    ! [B_54,A_55] :
      ( v4_pre_topc(B_54,A_55)
      | ~ v3_pre_topc(B_54,A_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ v3_tdlat_3(A_55)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_240,plain,(
    ! [B_54] :
      ( v4_pre_topc(B_54,'#skF_3')
      | ~ v3_pre_topc(B_54,'#skF_3')
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_231])).

tff(c_245,plain,(
    ! [B_56] :
      ( v4_pre_topc(B_56,'#skF_3')
      | ~ v3_pre_topc(B_56,'#skF_3')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_44,c_240])).

tff(c_248,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_245])).

tff(c_251,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_248])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_251])).

tff(c_254,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_260,plain,(
    ! [A_57,B_58] :
      ( k2_pre_topc(A_57,B_58) = u1_struct_0(A_57)
      | ~ v1_tops_1(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_269,plain,(
    ! [B_58] :
      ( k2_pre_topc('#skF_3',B_58) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_58,'#skF_3')
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_260])).

tff(c_274,plain,(
    ! [B_59] :
      ( k2_pre_topc('#skF_3',B_59) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_59,'#skF_3')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_60,c_269])).

tff(c_277,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_274])).

tff(c_279,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_277])).

tff(c_294,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_36,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_397,plain,(
    ! [B_80,A_81] :
      ( v1_tops_1(B_80,A_81)
      | ~ v3_tex_2(B_80,A_81)
      | ~ v3_pre_topc(B_80,A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_406,plain,(
    ! [B_80] :
      ( v1_tops_1(B_80,'#skF_3')
      | ~ v3_tex_2(B_80,'#skF_3')
      | ~ v3_pre_topc(B_80,'#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_397])).

tff(c_410,plain,(
    ! [B_80] :
      ( v1_tops_1(B_80,'#skF_3')
      | ~ v3_tex_2(B_80,'#skF_3')
      | ~ v3_pre_topc(B_80,'#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_406])).

tff(c_413,plain,(
    ! [B_83] :
      ( v1_tops_1(B_83,'#skF_3')
      | ~ v3_tex_2(B_83,'#skF_3')
      | ~ v3_pre_topc(B_83,'#skF_3')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_410])).

tff(c_416,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_413])).

tff(c_419,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_36,c_416])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_419])).

tff(c_422,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_34,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_428,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_62])).

tff(c_67,plain,(
    ! [A_25] :
      ( ~ v1_subset_1(k2_struct_0(A_25),u1_struct_0(A_25))
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_67])).

tff(c_71,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_74,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74])).

tff(c_79,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_426,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_422,c_79])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_426])).

tff(c_442,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_441,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_443,plain,(
    ! [A_84] :
      ( u1_struct_0(A_84) = k2_struct_0(A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_447,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_443])).

tff(c_448,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_40])).

tff(c_624,plain,(
    ! [B_114,A_115] :
      ( v3_pre_topc(B_114,A_115)
      | ~ v4_pre_topc(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v3_tdlat_3(A_115)
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_633,plain,(
    ! [B_114] :
      ( v3_pre_topc(B_114,'#skF_3')
      | ~ v4_pre_topc(B_114,'#skF_3')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_624])).

tff(c_638,plain,(
    ! [B_116] :
      ( v3_pre_topc(B_116,'#skF_3')
      | ~ v4_pre_topc(B_116,'#skF_3')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_44,c_633])).

tff(c_641,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_448,c_638])).

tff(c_644,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_641])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.47  
% 2.94/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.47  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.94/1.47  
% 2.94/1.47  %Foreground sorts:
% 2.94/1.47  
% 2.94/1.47  
% 2.94/1.47  %Background operators:
% 2.94/1.47  
% 2.94/1.47  
% 2.94/1.47  %Foreground operators:
% 2.94/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.94/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.94/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.94/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.94/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.94/1.47  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.94/1.47  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.94/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.94/1.47  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.94/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.94/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.94/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.94/1.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.94/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.47  
% 3.08/1.49  tff(f_126, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 3.08/1.49  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.08/1.49  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.08/1.49  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.08/1.49  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 3.08/1.49  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.08/1.49  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 3.08/1.49  tff(f_38, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 3.08/1.49  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.08/1.49  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.08/1.49  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.49  tff(c_50, plain, (![A_23]: (u1_struct_0(A_23)=k2_struct_0(A_23) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.49  tff(c_56, plain, (![A_24]: (u1_struct_0(A_24)=k2_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_4, c_50])).
% 3.08/1.49  tff(c_60, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_56])).
% 3.08/1.49  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.08/1.49  tff(c_61, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40])).
% 3.08/1.49  tff(c_102, plain, (![A_32, B_33]: (k2_pre_topc(A_32, B_33)=B_33 | ~v4_pre_topc(B_33, A_32) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.49  tff(c_111, plain, (![B_33]: (k2_pre_topc('#skF_3', B_33)=B_33 | ~v4_pre_topc(B_33, '#skF_3') | ~m1_subset_1(B_33, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_102])).
% 3.08/1.49  tff(c_116, plain, (![B_34]: (k2_pre_topc('#skF_3', B_34)=B_34 | ~v4_pre_topc(B_34, '#skF_3') | ~m1_subset_1(B_34, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_111])).
% 3.08/1.49  tff(c_120, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_61, c_116])).
% 3.08/1.49  tff(c_121, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_120])).
% 3.08/1.49  tff(c_38, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.08/1.49  tff(c_55, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 3.08/1.49  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.08/1.49  tff(c_44, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.08/1.49  tff(c_231, plain, (![B_54, A_55]: (v4_pre_topc(B_54, A_55) | ~v3_pre_topc(B_54, A_55) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_55))) | ~v3_tdlat_3(A_55) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.08/1.49  tff(c_240, plain, (![B_54]: (v4_pre_topc(B_54, '#skF_3') | ~v3_pre_topc(B_54, '#skF_3') | ~m1_subset_1(B_54, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_231])).
% 3.08/1.49  tff(c_245, plain, (![B_56]: (v4_pre_topc(B_56, '#skF_3') | ~v3_pre_topc(B_56, '#skF_3') | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_44, c_240])).
% 3.08/1.49  tff(c_248, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_61, c_245])).
% 3.08/1.49  tff(c_251, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_248])).
% 3.08/1.49  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_251])).
% 3.08/1.49  tff(c_254, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_120])).
% 3.08/1.49  tff(c_260, plain, (![A_57, B_58]: (k2_pre_topc(A_57, B_58)=u1_struct_0(A_57) | ~v1_tops_1(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.08/1.49  tff(c_269, plain, (![B_58]: (k2_pre_topc('#skF_3', B_58)=u1_struct_0('#skF_3') | ~v1_tops_1(B_58, '#skF_3') | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_260])).
% 3.08/1.49  tff(c_274, plain, (![B_59]: (k2_pre_topc('#skF_3', B_59)=k2_struct_0('#skF_3') | ~v1_tops_1(B_59, '#skF_3') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_60, c_269])).
% 3.08/1.49  tff(c_277, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_61, c_274])).
% 3.08/1.49  tff(c_279, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_277])).
% 3.08/1.49  tff(c_294, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_279])).
% 3.08/1.49  tff(c_36, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.08/1.49  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.08/1.49  tff(c_397, plain, (![B_80, A_81]: (v1_tops_1(B_80, A_81) | ~v3_tex_2(B_80, A_81) | ~v3_pre_topc(B_80, A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.08/1.49  tff(c_406, plain, (![B_80]: (v1_tops_1(B_80, '#skF_3') | ~v3_tex_2(B_80, '#skF_3') | ~v3_pre_topc(B_80, '#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_397])).
% 3.08/1.49  tff(c_410, plain, (![B_80]: (v1_tops_1(B_80, '#skF_3') | ~v3_tex_2(B_80, '#skF_3') | ~v3_pre_topc(B_80, '#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_406])).
% 3.08/1.49  tff(c_413, plain, (![B_83]: (v1_tops_1(B_83, '#skF_3') | ~v3_tex_2(B_83, '#skF_3') | ~v3_pre_topc(B_83, '#skF_3') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_410])).
% 3.08/1.49  tff(c_416, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_61, c_413])).
% 3.08/1.49  tff(c_419, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_36, c_416])).
% 3.08/1.49  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_294, c_419])).
% 3.08/1.49  tff(c_422, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_279])).
% 3.08/1.49  tff(c_34, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.08/1.49  tff(c_62, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_34])).
% 3.08/1.49  tff(c_428, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_62])).
% 3.08/1.49  tff(c_67, plain, (![A_25]: (~v1_subset_1(k2_struct_0(A_25), u1_struct_0(A_25)) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.49  tff(c_70, plain, (~v1_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60, c_67])).
% 3.08/1.49  tff(c_71, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_70])).
% 3.08/1.49  tff(c_74, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_71])).
% 3.08/1.49  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_74])).
% 3.08/1.49  tff(c_79, plain, (~v1_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_70])).
% 3.08/1.49  tff(c_426, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_422, c_79])).
% 3.08/1.49  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_428, c_426])).
% 3.08/1.49  tff(c_442, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.08/1.49  tff(c_441, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.08/1.49  tff(c_443, plain, (![A_84]: (u1_struct_0(A_84)=k2_struct_0(A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_4, c_50])).
% 3.08/1.49  tff(c_447, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_443])).
% 3.08/1.49  tff(c_448, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_40])).
% 3.08/1.49  tff(c_624, plain, (![B_114, A_115]: (v3_pre_topc(B_114, A_115) | ~v4_pre_topc(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~v3_tdlat_3(A_115) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.08/1.49  tff(c_633, plain, (![B_114]: (v3_pre_topc(B_114, '#skF_3') | ~v4_pre_topc(B_114, '#skF_3') | ~m1_subset_1(B_114, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_447, c_624])).
% 3.08/1.49  tff(c_638, plain, (![B_116]: (v3_pre_topc(B_116, '#skF_3') | ~v4_pre_topc(B_116, '#skF_3') | ~m1_subset_1(B_116, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_44, c_633])).
% 3.08/1.49  tff(c_641, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_448, c_638])).
% 3.08/1.49  tff(c_644, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_441, c_641])).
% 3.08/1.49  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_442, c_644])).
% 3.08/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.49  
% 3.08/1.49  Inference rules
% 3.08/1.49  ----------------------
% 3.08/1.49  #Ref     : 0
% 3.08/1.49  #Sup     : 112
% 3.08/1.49  #Fact    : 0
% 3.08/1.49  #Define  : 0
% 3.08/1.49  #Split   : 7
% 3.08/1.49  #Chain   : 0
% 3.08/1.49  #Close   : 0
% 3.08/1.49  
% 3.08/1.49  Ordering : KBO
% 3.08/1.49  
% 3.08/1.49  Simplification rules
% 3.08/1.49  ----------------------
% 3.08/1.49  #Subsume      : 20
% 3.08/1.49  #Demod        : 89
% 3.08/1.49  #Tautology    : 36
% 3.08/1.49  #SimpNegUnit  : 8
% 3.08/1.49  #BackRed      : 10
% 3.08/1.49  
% 3.08/1.49  #Partial instantiations: 0
% 3.08/1.49  #Strategies tried      : 1
% 3.08/1.49  
% 3.08/1.49  Timing (in seconds)
% 3.08/1.49  ----------------------
% 3.08/1.49  Preprocessing        : 0.33
% 3.08/1.49  Parsing              : 0.18
% 3.08/1.49  CNF conversion       : 0.02
% 3.08/1.49  Main loop            : 0.33
% 3.08/1.49  Inferencing          : 0.14
% 3.08/1.49  Reduction            : 0.10
% 3.08/1.49  Demodulation         : 0.06
% 3.08/1.49  BG Simplification    : 0.02
% 3.08/1.49  Subsumption          : 0.05
% 3.08/1.49  Abstraction          : 0.02
% 3.08/1.49  MUC search           : 0.00
% 3.08/1.49  Cooper               : 0.00
% 3.08/1.49  Total                : 0.70
% 3.08/1.49  Index Insertion      : 0.00
% 3.08/1.49  Index Deletion       : 0.00
% 3.08/1.49  Index Matching       : 0.00
% 3.08/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:30:29 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 344 expanded)
%              Number of leaves         :   33 ( 130 expanded)
%              Depth                    :   11
%              Number of atoms          :  189 (1016 expanded)
%              Number of equality atoms :   28 ( 133 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_30,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

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

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
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
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

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

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_subset_1(k2_subset_1(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_51,plain,(
    ! [A_2] : ~ v1_subset_1(A_2,A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_69,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_8,c_63])).

tff(c_73,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_42])).

tff(c_96,plain,(
    ! [A_34,B_35] :
      ( k2_pre_topc(A_34,B_35) = B_35
      | ~ v4_pre_topc(B_35,A_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_105,plain,(
    ! [B_35] :
      ( k2_pre_topc('#skF_3',B_35) = B_35
      | ~ v4_pre_topc(B_35,'#skF_3')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_96])).

tff(c_110,plain,(
    ! [B_36] :
      ( k2_pre_topc('#skF_3',B_36) = B_36
      | ~ v4_pre_topc(B_36,'#skF_3')
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_105])).

tff(c_114,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_110])).

tff(c_129,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_68,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_171,plain,(
    ! [B_45,A_46] :
      ( v4_pre_topc(B_45,A_46)
      | ~ v3_pre_topc(B_45,A_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ v3_tdlat_3(A_46)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_180,plain,(
    ! [B_45] :
      ( v4_pre_topc(B_45,'#skF_3')
      | ~ v3_pre_topc(B_45,'#skF_3')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_171])).

tff(c_185,plain,(
    ! [B_47] :
      ( v4_pre_topc(B_47,'#skF_3')
      | ~ v3_pre_topc(B_47,'#skF_3')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_180])).

tff(c_188,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_185])).

tff(c_191,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_188])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_191])).

tff(c_194,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_115,plain,(
    ! [B_37,A_38] :
      ( v1_tops_1(B_37,A_38)
      | k2_pre_topc(A_38,B_37) != k2_struct_0(A_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_124,plain,(
    ! [B_37] :
      ( v1_tops_1(B_37,'#skF_3')
      | k2_pre_topc('#skF_3',B_37) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_115])).

tff(c_200,plain,(
    ! [B_48] :
      ( v1_tops_1(B_48,'#skF_3')
      | k2_pre_topc('#skF_3',B_48) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_124])).

tff(c_203,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_200])).

tff(c_205,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_203])).

tff(c_206,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_207,plain,(
    ! [A_49,B_50] :
      ( k2_pre_topc(A_49,B_50) = k2_struct_0(A_49)
      | ~ v1_tops_1(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_216,plain,(
    ! [B_50] :
      ( k2_pre_topc('#skF_3',B_50) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_50,'#skF_3')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_207])).

tff(c_221,plain,(
    ! [B_51] :
      ( k2_pre_topc('#skF_3',B_51) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_51,'#skF_3')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_216])).

tff(c_224,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_221])).

tff(c_226,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_224])).

tff(c_227,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_226])).

tff(c_38,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_323,plain,(
    ! [B_69,A_70] :
      ( v1_tops_1(B_69,A_70)
      | ~ v3_tex_2(B_69,A_70)
      | ~ v3_pre_topc(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_332,plain,(
    ! [B_69] :
      ( v1_tops_1(B_69,'#skF_3')
      | ~ v3_tex_2(B_69,'#skF_3')
      | ~ v3_pre_topc(B_69,'#skF_3')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_323])).

tff(c_336,plain,(
    ! [B_69] :
      ( v1_tops_1(B_69,'#skF_3')
      | ~ v3_tex_2(B_69,'#skF_3')
      | ~ v3_pre_topc(B_69,'#skF_3')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_332])).

tff(c_338,plain,(
    ! [B_71] :
      ( v1_tops_1(B_71,'#skF_3')
      | ~ v3_tex_2(B_71,'#skF_3')
      | ~ v3_pre_topc(B_71,'#skF_3')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_336])).

tff(c_341,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_338])).

tff(c_344,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_38,c_341])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_344])).

tff(c_348,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_36,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_75,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_36])).

tff(c_352,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_75])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_352])).

tff(c_357,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_356,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_359,plain,(
    ! [A_73] :
      ( u1_struct_0(A_73) = k2_struct_0(A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_8,c_63])).

tff(c_363,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_359])).

tff(c_364,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_42])).

tff(c_487,plain,(
    ! [B_93,A_94] :
      ( v3_pre_topc(B_93,A_94)
      | ~ v4_pre_topc(B_93,A_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v3_tdlat_3(A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_496,plain,(
    ! [B_93] :
      ( v3_pre_topc(B_93,'#skF_3')
      | ~ v4_pre_topc(B_93,'#skF_3')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_487])).

tff(c_501,plain,(
    ! [B_95] :
      ( v3_pre_topc(B_95,'#skF_3')
      | ~ v4_pre_topc(B_95,'#skF_3')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_496])).

tff(c_504,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_364,c_501])).

tff(c_507,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_504])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:04:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.32  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.66/1.32  
% 2.66/1.32  %Foreground sorts:
% 2.66/1.32  
% 2.66/1.32  
% 2.66/1.32  %Background operators:
% 2.66/1.32  
% 2.66/1.32  
% 2.66/1.32  %Foreground operators:
% 2.66/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.66/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.66/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.32  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.66/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.66/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.66/1.32  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.66/1.32  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.66/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.66/1.32  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.66/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.66/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.66/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.66/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.66/1.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.66/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.32  
% 2.66/1.34  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.66/1.34  tff(f_30, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.66/1.34  tff(f_126, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 2.66/1.34  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.66/1.34  tff(f_34, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.66/1.34  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.66/1.34  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 2.66/1.34  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.66/1.34  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 2.66/1.34  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.66/1.34  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.34  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_subset_1(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.66/1.34  tff(c_51, plain, (![A_2]: (~v1_subset_1(A_2, A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.66/1.34  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.66/1.34  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.34  tff(c_63, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.34  tff(c_69, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_8, c_63])).
% 2.66/1.34  tff(c_73, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_69])).
% 2.66/1.34  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.66/1.34  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_42])).
% 2.66/1.34  tff(c_96, plain, (![A_34, B_35]: (k2_pre_topc(A_34, B_35)=B_35 | ~v4_pre_topc(B_35, A_34) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.34  tff(c_105, plain, (![B_35]: (k2_pre_topc('#skF_3', B_35)=B_35 | ~v4_pre_topc(B_35, '#skF_3') | ~m1_subset_1(B_35, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_96])).
% 2.66/1.34  tff(c_110, plain, (![B_36]: (k2_pre_topc('#skF_3', B_36)=B_36 | ~v4_pre_topc(B_36, '#skF_3') | ~m1_subset_1(B_36, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_105])).
% 2.66/1.34  tff(c_114, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_110])).
% 2.66/1.34  tff(c_129, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_114])).
% 2.66/1.34  tff(c_40, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.66/1.34  tff(c_68, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 2.66/1.34  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.66/1.34  tff(c_46, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.66/1.34  tff(c_171, plain, (![B_45, A_46]: (v4_pre_topc(B_45, A_46) | ~v3_pre_topc(B_45, A_46) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_46))) | ~v3_tdlat_3(A_46) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.66/1.34  tff(c_180, plain, (![B_45]: (v4_pre_topc(B_45, '#skF_3') | ~v3_pre_topc(B_45, '#skF_3') | ~m1_subset_1(B_45, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_171])).
% 2.66/1.34  tff(c_185, plain, (![B_47]: (v4_pre_topc(B_47, '#skF_3') | ~v3_pre_topc(B_47, '#skF_3') | ~m1_subset_1(B_47, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_180])).
% 2.66/1.34  tff(c_188, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_185])).
% 2.66/1.34  tff(c_191, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_188])).
% 2.66/1.34  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_191])).
% 2.66/1.34  tff(c_194, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_114])).
% 2.66/1.34  tff(c_115, plain, (![B_37, A_38]: (v1_tops_1(B_37, A_38) | k2_pre_topc(A_38, B_37)!=k2_struct_0(A_38) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.34  tff(c_124, plain, (![B_37]: (v1_tops_1(B_37, '#skF_3') | k2_pre_topc('#skF_3', B_37)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_37, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_115])).
% 2.66/1.34  tff(c_200, plain, (![B_48]: (v1_tops_1(B_48, '#skF_3') | k2_pre_topc('#skF_3', B_48)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_48, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_124])).
% 2.66/1.34  tff(c_203, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_200])).
% 2.66/1.34  tff(c_205, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_203])).
% 2.66/1.34  tff(c_206, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_205])).
% 2.66/1.34  tff(c_207, plain, (![A_49, B_50]: (k2_pre_topc(A_49, B_50)=k2_struct_0(A_49) | ~v1_tops_1(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.34  tff(c_216, plain, (![B_50]: (k2_pre_topc('#skF_3', B_50)=k2_struct_0('#skF_3') | ~v1_tops_1(B_50, '#skF_3') | ~m1_subset_1(B_50, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_207])).
% 2.66/1.34  tff(c_221, plain, (![B_51]: (k2_pre_topc('#skF_3', B_51)=k2_struct_0('#skF_3') | ~v1_tops_1(B_51, '#skF_3') | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_216])).
% 2.66/1.34  tff(c_224, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_221])).
% 2.66/1.34  tff(c_226, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_224])).
% 2.66/1.34  tff(c_227, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_206, c_226])).
% 2.66/1.34  tff(c_38, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.66/1.34  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.66/1.34  tff(c_323, plain, (![B_69, A_70]: (v1_tops_1(B_69, A_70) | ~v3_tex_2(B_69, A_70) | ~v3_pre_topc(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.34  tff(c_332, plain, (![B_69]: (v1_tops_1(B_69, '#skF_3') | ~v3_tex_2(B_69, '#skF_3') | ~v3_pre_topc(B_69, '#skF_3') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_323])).
% 2.66/1.34  tff(c_336, plain, (![B_69]: (v1_tops_1(B_69, '#skF_3') | ~v3_tex_2(B_69, '#skF_3') | ~v3_pre_topc(B_69, '#skF_3') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_332])).
% 2.66/1.34  tff(c_338, plain, (![B_71]: (v1_tops_1(B_71, '#skF_3') | ~v3_tex_2(B_71, '#skF_3') | ~v3_pre_topc(B_71, '#skF_3') | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_336])).
% 2.66/1.34  tff(c_341, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_338])).
% 2.66/1.34  tff(c_344, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_38, c_341])).
% 2.66/1.34  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_344])).
% 2.66/1.34  tff(c_348, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_205])).
% 2.66/1.34  tff(c_36, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.66/1.34  tff(c_75, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_36])).
% 2.66/1.34  tff(c_352, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_75])).
% 2.66/1.34  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_352])).
% 2.66/1.34  tff(c_357, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 2.66/1.34  tff(c_356, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 2.66/1.34  tff(c_359, plain, (![A_73]: (u1_struct_0(A_73)=k2_struct_0(A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_8, c_63])).
% 2.66/1.34  tff(c_363, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_359])).
% 2.66/1.34  tff(c_364, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_42])).
% 2.66/1.34  tff(c_487, plain, (![B_93, A_94]: (v3_pre_topc(B_93, A_94) | ~v4_pre_topc(B_93, A_94) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~v3_tdlat_3(A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.66/1.34  tff(c_496, plain, (![B_93]: (v3_pre_topc(B_93, '#skF_3') | ~v4_pre_topc(B_93, '#skF_3') | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_363, c_487])).
% 2.66/1.34  tff(c_501, plain, (![B_95]: (v3_pre_topc(B_95, '#skF_3') | ~v4_pre_topc(B_95, '#skF_3') | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_496])).
% 2.66/1.34  tff(c_504, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_364, c_501])).
% 2.66/1.34  tff(c_507, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_504])).
% 2.66/1.34  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_507])).
% 2.66/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.34  
% 2.66/1.34  Inference rules
% 2.66/1.34  ----------------------
% 2.66/1.34  #Ref     : 0
% 2.66/1.34  #Sup     : 86
% 2.66/1.34  #Fact    : 0
% 2.66/1.34  #Define  : 0
% 2.66/1.34  #Split   : 5
% 2.66/1.34  #Chain   : 0
% 2.66/1.34  #Close   : 0
% 2.66/1.34  
% 2.66/1.34  Ordering : KBO
% 2.66/1.34  
% 2.66/1.34  Simplification rules
% 2.66/1.34  ----------------------
% 2.66/1.34  #Subsume      : 13
% 2.66/1.34  #Demod        : 67
% 2.66/1.34  #Tautology    : 28
% 2.66/1.34  #SimpNegUnit  : 8
% 2.66/1.34  #BackRed      : 9
% 2.66/1.34  
% 2.66/1.34  #Partial instantiations: 0
% 2.66/1.34  #Strategies tried      : 1
% 2.66/1.34  
% 2.66/1.34  Timing (in seconds)
% 2.66/1.34  ----------------------
% 2.66/1.34  Preprocessing        : 0.31
% 2.66/1.34  Parsing              : 0.17
% 2.66/1.34  CNF conversion       : 0.02
% 2.66/1.34  Main loop            : 0.28
% 2.66/1.34  Inferencing          : 0.11
% 2.66/1.34  Reduction            : 0.08
% 2.66/1.34  Demodulation         : 0.06
% 2.66/1.34  BG Simplification    : 0.02
% 2.66/1.34  Subsumption          : 0.04
% 2.66/1.34  Abstraction          : 0.02
% 2.66/1.34  MUC search           : 0.00
% 2.66/1.34  Cooper               : 0.00
% 2.66/1.34  Total                : 0.62
% 2.66/1.34  Index Insertion      : 0.00
% 2.66/1.34  Index Deletion       : 0.00
% 2.66/1.34  Index Matching       : 0.00
% 2.66/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

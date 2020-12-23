%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:29 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 408 expanded)
%              Number of leaves         :   31 ( 150 expanded)
%              Depth                    :   12
%              Number of atoms          :  193 (1217 expanded)
%              Number of equality atoms :   28 ( 166 expanded)
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

tff(f_128,negated_conjecture,(
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

tff(f_48,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_106,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_24] :
      ( u1_struct_0(A_24) = k2_struct_0(A_24)
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_62,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_63,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42])).

tff(c_100,plain,(
    ! [A_35,B_36] :
      ( k2_pre_topc(A_35,B_36) = B_36
      | ~ v4_pre_topc(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [B_36] :
      ( k2_pre_topc('#skF_3',B_36) = B_36
      | ~ v4_pre_topc(B_36,'#skF_3')
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_100])).

tff(c_114,plain,(
    ! [B_37] :
      ( k2_pre_topc('#skF_3',B_37) = B_37
      | ~ v4_pre_topc(B_37,'#skF_3')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_109])).

tff(c_118,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_114])).

tff(c_133,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_52,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_230,plain,(
    ! [B_56,A_57] :
      ( v4_pre_topc(B_56,A_57)
      | ~ v3_pre_topc(B_56,A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ v3_tdlat_3(A_57)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_239,plain,(
    ! [B_56] :
      ( v4_pre_topc(B_56,'#skF_3')
      | ~ v3_pre_topc(B_56,'#skF_3')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_230])).

tff(c_244,plain,(
    ! [B_58] :
      ( v4_pre_topc(B_58,'#skF_3')
      | ~ v3_pre_topc(B_58,'#skF_3')
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_239])).

tff(c_247,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_244])).

tff(c_250,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_247])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_250])).

tff(c_253,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_119,plain,(
    ! [B_38,A_39] :
      ( v1_tops_1(B_38,A_39)
      | k2_pre_topc(A_39,B_38) != k2_struct_0(A_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    ! [B_38] :
      ( v1_tops_1(B_38,'#skF_3')
      | k2_pre_topc('#skF_3',B_38) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_119])).

tff(c_259,plain,(
    ! [B_59] :
      ( v1_tops_1(B_59,'#skF_3')
      | k2_pre_topc('#skF_3',B_59) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_128])).

tff(c_262,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_259])).

tff(c_264,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_262])).

tff(c_265,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_266,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,B_61) = k2_struct_0(A_60)
      | ~ v1_tops_1(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_275,plain,(
    ! [B_61] :
      ( k2_pre_topc('#skF_3',B_61) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_61,'#skF_3')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_266])).

tff(c_280,plain,(
    ! [B_62] :
      ( k2_pre_topc('#skF_3',B_62) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_62,'#skF_3')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_275])).

tff(c_283,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_280])).

tff(c_285,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_283])).

tff(c_286,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_285])).

tff(c_38,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_388,plain,(
    ! [B_80,A_81] :
      ( v1_tops_1(B_80,A_81)
      | ~ v3_tex_2(B_80,A_81)
      | ~ v3_pre_topc(B_80,A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_397,plain,(
    ! [B_80] :
      ( v1_tops_1(B_80,'#skF_3')
      | ~ v3_tex_2(B_80,'#skF_3')
      | ~ v3_pre_topc(B_80,'#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_388])).

tff(c_401,plain,(
    ! [B_80] :
      ( v1_tops_1(B_80,'#skF_3')
      | ~ v3_tex_2(B_80,'#skF_3')
      | ~ v3_pre_topc(B_80,'#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_397])).

tff(c_404,plain,(
    ! [B_83] :
      ( v1_tops_1(B_83,'#skF_3')
      | ~ v3_tex_2(B_83,'#skF_3')
      | ~ v3_pre_topc(B_83,'#skF_3')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_401])).

tff(c_407,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_404])).

tff(c_410,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38,c_407])).

tff(c_412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_410])).

tff(c_414,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_36,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_64,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36])).

tff(c_418,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_64])).

tff(c_417,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_63])).

tff(c_16,plain,(
    ! [B_10] :
      ( ~ v1_subset_1(B_10,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_467,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_417,c_16])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_467])).

tff(c_476,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_475,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_477,plain,(
    ! [A_86] :
      ( u1_struct_0(A_86) = k2_struct_0(A_86)
      | ~ l1_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_482,plain,(
    ! [A_87] :
      ( u1_struct_0(A_87) = k2_struct_0(A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_4,c_477])).

tff(c_486,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_482])).

tff(c_487,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_42])).

tff(c_630,plain,(
    ! [B_113,A_114] :
      ( v3_pre_topc(B_113,A_114)
      | ~ v4_pre_topc(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v3_tdlat_3(A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_639,plain,(
    ! [B_113] :
      ( v3_pre_topc(B_113,'#skF_3')
      | ~ v4_pre_topc(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_630])).

tff(c_644,plain,(
    ! [B_115] :
      ( v3_pre_topc(B_115,'#skF_3')
      | ~ v4_pre_topc(B_115,'#skF_3')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_639])).

tff(c_647,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_487,c_644])).

tff(c_650,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_647])).

tff(c_652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.41  
% 2.63/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.41  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.63/1.41  
% 2.63/1.41  %Foreground sorts:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Background operators:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Foreground operators:
% 2.63/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.63/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.63/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.63/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.63/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.41  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.63/1.41  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.63/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.63/1.41  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.63/1.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.63/1.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.63/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.41  
% 3.01/1.43  tff(f_128, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 3.01/1.43  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.01/1.43  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.01/1.43  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.01/1.43  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 3.01/1.43  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.01/1.43  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 3.01/1.43  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.01/1.43  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.01/1.43  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.01/1.43  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.43  tff(c_53, plain, (![A_24]: (u1_struct_0(A_24)=k2_struct_0(A_24) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.01/1.43  tff(c_58, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_4, c_53])).
% 3.01/1.43  tff(c_62, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_58])).
% 3.01/1.43  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.01/1.43  tff(c_63, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42])).
% 3.01/1.43  tff(c_100, plain, (![A_35, B_36]: (k2_pre_topc(A_35, B_36)=B_36 | ~v4_pre_topc(B_36, A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.01/1.43  tff(c_109, plain, (![B_36]: (k2_pre_topc('#skF_3', B_36)=B_36 | ~v4_pre_topc(B_36, '#skF_3') | ~m1_subset_1(B_36, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_100])).
% 3.01/1.43  tff(c_114, plain, (![B_37]: (k2_pre_topc('#skF_3', B_37)=B_37 | ~v4_pre_topc(B_37, '#skF_3') | ~m1_subset_1(B_37, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_109])).
% 3.01/1.43  tff(c_118, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_63, c_114])).
% 3.01/1.43  tff(c_133, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_118])).
% 3.01/1.43  tff(c_40, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.01/1.43  tff(c_52, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 3.01/1.43  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.01/1.43  tff(c_46, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.01/1.43  tff(c_230, plain, (![B_56, A_57]: (v4_pre_topc(B_56, A_57) | ~v3_pre_topc(B_56, A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~v3_tdlat_3(A_57) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.01/1.43  tff(c_239, plain, (![B_56]: (v4_pre_topc(B_56, '#skF_3') | ~v3_pre_topc(B_56, '#skF_3') | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_230])).
% 3.01/1.43  tff(c_244, plain, (![B_58]: (v4_pre_topc(B_58, '#skF_3') | ~v3_pre_topc(B_58, '#skF_3') | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_239])).
% 3.01/1.43  tff(c_247, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_63, c_244])).
% 3.01/1.43  tff(c_250, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_247])).
% 3.01/1.43  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_250])).
% 3.01/1.43  tff(c_253, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_118])).
% 3.01/1.43  tff(c_119, plain, (![B_38, A_39]: (v1_tops_1(B_38, A_39) | k2_pre_topc(A_39, B_38)!=k2_struct_0(A_39) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.43  tff(c_128, plain, (![B_38]: (v1_tops_1(B_38, '#skF_3') | k2_pre_topc('#skF_3', B_38)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_38, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_119])).
% 3.01/1.43  tff(c_259, plain, (![B_59]: (v1_tops_1(B_59, '#skF_3') | k2_pre_topc('#skF_3', B_59)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_128])).
% 3.01/1.43  tff(c_262, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_63, c_259])).
% 3.01/1.43  tff(c_264, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_253, c_262])).
% 3.01/1.43  tff(c_265, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_264])).
% 3.01/1.43  tff(c_266, plain, (![A_60, B_61]: (k2_pre_topc(A_60, B_61)=k2_struct_0(A_60) | ~v1_tops_1(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.43  tff(c_275, plain, (![B_61]: (k2_pre_topc('#skF_3', B_61)=k2_struct_0('#skF_3') | ~v1_tops_1(B_61, '#skF_3') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_266])).
% 3.01/1.43  tff(c_280, plain, (![B_62]: (k2_pre_topc('#skF_3', B_62)=k2_struct_0('#skF_3') | ~v1_tops_1(B_62, '#skF_3') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_275])).
% 3.01/1.43  tff(c_283, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_63, c_280])).
% 3.01/1.43  tff(c_285, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_283])).
% 3.01/1.43  tff(c_286, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_265, c_285])).
% 3.01/1.43  tff(c_38, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.01/1.43  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.01/1.43  tff(c_388, plain, (![B_80, A_81]: (v1_tops_1(B_80, A_81) | ~v3_tex_2(B_80, A_81) | ~v3_pre_topc(B_80, A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.01/1.43  tff(c_397, plain, (![B_80]: (v1_tops_1(B_80, '#skF_3') | ~v3_tex_2(B_80, '#skF_3') | ~v3_pre_topc(B_80, '#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_388])).
% 3.01/1.43  tff(c_401, plain, (![B_80]: (v1_tops_1(B_80, '#skF_3') | ~v3_tex_2(B_80, '#skF_3') | ~v3_pre_topc(B_80, '#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_397])).
% 3.01/1.43  tff(c_404, plain, (![B_83]: (v1_tops_1(B_83, '#skF_3') | ~v3_tex_2(B_83, '#skF_3') | ~v3_pre_topc(B_83, '#skF_3') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_401])).
% 3.01/1.43  tff(c_407, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_63, c_404])).
% 3.01/1.43  tff(c_410, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38, c_407])).
% 3.01/1.43  tff(c_412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_410])).
% 3.01/1.43  tff(c_414, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_264])).
% 3.01/1.43  tff(c_36, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.01/1.43  tff(c_64, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36])).
% 3.01/1.43  tff(c_418, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_64])).
% 3.01/1.43  tff(c_417, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_63])).
% 3.01/1.43  tff(c_16, plain, (![B_10]: (~v1_subset_1(B_10, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.43  tff(c_467, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_417, c_16])).
% 3.01/1.43  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_418, c_467])).
% 3.01/1.43  tff(c_476, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.01/1.43  tff(c_475, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.01/1.43  tff(c_477, plain, (![A_86]: (u1_struct_0(A_86)=k2_struct_0(A_86) | ~l1_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.01/1.43  tff(c_482, plain, (![A_87]: (u1_struct_0(A_87)=k2_struct_0(A_87) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_4, c_477])).
% 3.01/1.43  tff(c_486, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_482])).
% 3.01/1.43  tff(c_487, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_42])).
% 3.01/1.43  tff(c_630, plain, (![B_113, A_114]: (v3_pre_topc(B_113, A_114) | ~v4_pre_topc(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~v3_tdlat_3(A_114) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.43  tff(c_639, plain, (![B_113]: (v3_pre_topc(B_113, '#skF_3') | ~v4_pre_topc(B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_486, c_630])).
% 3.01/1.43  tff(c_644, plain, (![B_115]: (v3_pre_topc(B_115, '#skF_3') | ~v4_pre_topc(B_115, '#skF_3') | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_639])).
% 3.01/1.43  tff(c_647, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_487, c_644])).
% 3.01/1.43  tff(c_650, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_475, c_647])).
% 3.01/1.43  tff(c_652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_476, c_650])).
% 3.01/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.43  
% 3.01/1.43  Inference rules
% 3.01/1.43  ----------------------
% 3.01/1.43  #Ref     : 0
% 3.01/1.43  #Sup     : 115
% 3.01/1.43  #Fact    : 0
% 3.01/1.43  #Define  : 0
% 3.01/1.43  #Split   : 5
% 3.01/1.43  #Chain   : 0
% 3.01/1.43  #Close   : 0
% 3.01/1.43  
% 3.01/1.43  Ordering : KBO
% 3.01/1.43  
% 3.01/1.43  Simplification rules
% 3.01/1.43  ----------------------
% 3.01/1.43  #Subsume      : 15
% 3.01/1.43  #Demod        : 109
% 3.01/1.43  #Tautology    : 41
% 3.01/1.43  #SimpNegUnit  : 8
% 3.01/1.43  #BackRed      : 9
% 3.01/1.43  
% 3.01/1.43  #Partial instantiations: 0
% 3.01/1.43  #Strategies tried      : 1
% 3.01/1.43  
% 3.01/1.43  Timing (in seconds)
% 3.01/1.43  ----------------------
% 3.01/1.43  Preprocessing        : 0.33
% 3.01/1.43  Parsing              : 0.18
% 3.01/1.43  CNF conversion       : 0.02
% 3.01/1.43  Main loop            : 0.32
% 3.01/1.43  Inferencing          : 0.13
% 3.01/1.43  Reduction            : 0.09
% 3.01/1.43  Demodulation         : 0.06
% 3.01/1.43  BG Simplification    : 0.02
% 3.01/1.43  Subsumption          : 0.04
% 3.01/1.43  Abstraction          : 0.02
% 3.01/1.43  MUC search           : 0.00
% 3.01/1.43  Cooper               : 0.00
% 3.01/1.43  Total                : 0.69
% 3.01/1.43  Index Insertion      : 0.00
% 3.01/1.43  Index Deletion       : 0.00
% 3.01/1.43  Index Matching       : 0.00
% 3.01/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

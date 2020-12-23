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
% DateTime   : Thu Dec  3 10:30:27 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 228 expanded)
%              Number of leaves         :   32 (  94 expanded)
%              Depth                    :    9
%              Number of atoms          :  197 ( 791 expanded)
%              Number of equality atoms :   23 (  51 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_130,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_108,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
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
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : ~ v1_subset_1(k2_subset_1(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_104,plain,(
    ! [B_45,A_46] :
      ( v1_tops_1(B_45,A_46)
      | k2_pre_topc(A_46,B_45) != u1_struct_0(A_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_113,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_104])).

tff(c_118,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_113])).

tff(c_119,plain,(
    k2_pre_topc('#skF_3','#skF_4') != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_120,plain,(
    ! [A_47,B_48] :
      ( k2_pre_topc(A_47,B_48) = u1_struct_0(A_47)
      | ~ v1_tops_1(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_129,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_120])).

tff(c_134,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_129])).

tff(c_135,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_134])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_66,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_180,plain,(
    ! [B_59,A_60] :
      ( v1_tops_1(B_59,A_60)
      | ~ v3_tex_2(B_59,A_60)
      | ~ v3_pre_topc(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_189,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_180])).

tff(c_194,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_66,c_40,c_189])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_135,c_194])).

tff(c_198,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_78,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(B_39,k2_pre_topc(A_40,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_78])).

tff(c_83,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_80])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_87,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_199,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_87])).

tff(c_48,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_230,plain,(
    ! [B_66,A_67] :
      ( v4_pre_topc(B_66,A_67)
      | ~ v3_pre_topc(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ v3_tdlat_3(A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_239,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_230])).

tff(c_244,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_66,c_239])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_284,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(k2_pre_topc(A_76,C_77),B_78)
      | ~ r1_tarski(C_77,B_78)
      | ~ v4_pre_topc(B_78,A_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_290,plain,(
    ! [B_78] :
      ( r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_78)
      | ~ r1_tarski('#skF_4',B_78)
      | ~ v4_pre_topc(B_78,'#skF_3')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_284])).

tff(c_296,plain,(
    ! [B_79] :
      ( r1_tarski(u1_struct_0('#skF_3'),B_79)
      | ~ r1_tarski('#skF_4',B_79)
      | ~ v4_pre_topc(B_79,'#skF_3')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_198,c_290])).

tff(c_307,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),'#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_296])).

tff(c_316,plain,(
    r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_6,c_307])).

tff(c_318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_316])).

tff(c_319,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_344,plain,(
    ! [B_84,A_85] :
      ( v1_tops_1(B_84,A_85)
      | k2_pre_topc(A_85,B_84) != u1_struct_0(A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_353,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_344])).

tff(c_358,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | u1_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_319,c_353])).

tff(c_359,plain,(
    u1_struct_0('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_360,plain,(
    ! [A_86,B_87] :
      ( k2_pre_topc(A_86,B_87) = u1_struct_0(A_86)
      | ~ v1_tops_1(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_369,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_360])).

tff(c_374,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_319,c_369])).

tff(c_375,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_374])).

tff(c_420,plain,(
    ! [B_98,A_99] :
      ( v1_tops_1(B_98,A_99)
      | ~ v3_tex_2(B_98,A_99)
      | ~ v3_pre_topc(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_429,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_420])).

tff(c_434,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_66,c_40,c_429])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_375,c_434])).

tff(c_438,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_38,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_440,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_38])).

tff(c_442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_440])).

tff(c_444,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_443,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_541,plain,(
    ! [B_122,A_123] :
      ( v3_pre_topc(B_122,A_123)
      | ~ v4_pre_topc(B_122,A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ v3_tdlat_3(A_123)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_550,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_541])).

tff(c_555,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_443,c_550])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.36  
% 2.64/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.37  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.64/1.37  
% 2.64/1.37  %Foreground sorts:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Background operators:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Foreground operators:
% 2.64/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.64/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.37  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.64/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.64/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.64/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.37  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.64/1.37  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.64/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.37  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.64/1.37  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.64/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.64/1.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.64/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.37  
% 2.94/1.38  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.94/1.38  tff(f_36, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.94/1.38  tff(f_130, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 2.94/1.38  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 2.94/1.38  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 2.94/1.38  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.94/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.38  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 2.94/1.38  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 2.94/1.38  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.94/1.38  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.38  tff(c_10, plain, (![A_4]: (~v1_subset_1(k2_subset_1(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.94/1.38  tff(c_53, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.94/1.38  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.94/1.38  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.94/1.38  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.94/1.38  tff(c_104, plain, (![B_45, A_46]: (v1_tops_1(B_45, A_46) | k2_pre_topc(A_46, B_45)!=u1_struct_0(A_46) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.94/1.38  tff(c_113, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_104])).
% 2.94/1.38  tff(c_118, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_113])).
% 2.94/1.38  tff(c_119, plain, (k2_pre_topc('#skF_3', '#skF_4')!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_118])).
% 2.94/1.38  tff(c_120, plain, (![A_47, B_48]: (k2_pre_topc(A_47, B_48)=u1_struct_0(A_47) | ~v1_tops_1(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.94/1.38  tff(c_129, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_120])).
% 2.94/1.38  tff(c_134, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_129])).
% 2.94/1.38  tff(c_135, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_119, c_134])).
% 2.94/1.38  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.94/1.38  tff(c_42, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.94/1.38  tff(c_66, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 2.94/1.38  tff(c_40, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.94/1.38  tff(c_180, plain, (![B_59, A_60]: (v1_tops_1(B_59, A_60) | ~v3_tex_2(B_59, A_60) | ~v3_pre_topc(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.94/1.38  tff(c_189, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_180])).
% 2.94/1.38  tff(c_194, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_66, c_40, c_189])).
% 2.94/1.38  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_135, c_194])).
% 2.94/1.38  tff(c_198, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_118])).
% 2.94/1.38  tff(c_78, plain, (![B_39, A_40]: (r1_tarski(B_39, k2_pre_topc(A_40, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.94/1.38  tff(c_80, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_78])).
% 2.94/1.38  tff(c_83, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_80])).
% 2.94/1.38  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.38  tff(c_86, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski(k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_83, c_2])).
% 2.94/1.38  tff(c_87, plain, (~r1_tarski(k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 2.94/1.38  tff(c_199, plain, (~r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_87])).
% 2.94/1.38  tff(c_48, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.94/1.38  tff(c_230, plain, (![B_66, A_67]: (v4_pre_topc(B_66, A_67) | ~v3_pre_topc(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~v3_tdlat_3(A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.94/1.38  tff(c_239, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_230])).
% 2.94/1.38  tff(c_244, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_66, c_239])).
% 2.94/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.38  tff(c_284, plain, (![A_76, C_77, B_78]: (r1_tarski(k2_pre_topc(A_76, C_77), B_78) | ~r1_tarski(C_77, B_78) | ~v4_pre_topc(B_78, A_76) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.94/1.38  tff(c_290, plain, (![B_78]: (r1_tarski(k2_pre_topc('#skF_3', '#skF_4'), B_78) | ~r1_tarski('#skF_4', B_78) | ~v4_pre_topc(B_78, '#skF_3') | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_284])).
% 2.94/1.38  tff(c_296, plain, (![B_79]: (r1_tarski(u1_struct_0('#skF_3'), B_79) | ~r1_tarski('#skF_4', B_79) | ~v4_pre_topc(B_79, '#skF_3') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_198, c_290])).
% 2.94/1.38  tff(c_307, plain, (r1_tarski(u1_struct_0('#skF_3'), '#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_296])).
% 2.94/1.38  tff(c_316, plain, (r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_6, c_307])).
% 2.94/1.38  tff(c_318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_316])).
% 2.94/1.38  tff(c_319, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_86])).
% 2.94/1.38  tff(c_344, plain, (![B_84, A_85]: (v1_tops_1(B_84, A_85) | k2_pre_topc(A_85, B_84)!=u1_struct_0(A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.94/1.38  tff(c_353, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_344])).
% 2.94/1.38  tff(c_358, plain, (v1_tops_1('#skF_4', '#skF_3') | u1_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_319, c_353])).
% 2.94/1.38  tff(c_359, plain, (u1_struct_0('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_358])).
% 2.94/1.38  tff(c_360, plain, (![A_86, B_87]: (k2_pre_topc(A_86, B_87)=u1_struct_0(A_86) | ~v1_tops_1(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.94/1.38  tff(c_369, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_360])).
% 2.94/1.38  tff(c_374, plain, (u1_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_319, c_369])).
% 2.94/1.38  tff(c_375, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_359, c_374])).
% 2.94/1.38  tff(c_420, plain, (![B_98, A_99]: (v1_tops_1(B_98, A_99) | ~v3_tex_2(B_98, A_99) | ~v3_pre_topc(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.94/1.38  tff(c_429, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_420])).
% 2.94/1.38  tff(c_434, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_66, c_40, c_429])).
% 2.94/1.38  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_375, c_434])).
% 2.94/1.38  tff(c_438, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_358])).
% 2.94/1.38  tff(c_38, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.94/1.38  tff(c_440, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_38])).
% 2.94/1.38  tff(c_442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_440])).
% 2.94/1.38  tff(c_444, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 2.94/1.38  tff(c_443, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 2.94/1.38  tff(c_541, plain, (![B_122, A_123]: (v3_pre_topc(B_122, A_123) | ~v4_pre_topc(B_122, A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~v3_tdlat_3(A_123) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.94/1.38  tff(c_550, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_541])).
% 2.94/1.38  tff(c_555, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_443, c_550])).
% 2.94/1.38  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_444, c_555])).
% 2.94/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.38  
% 2.94/1.38  Inference rules
% 2.94/1.38  ----------------------
% 2.94/1.38  #Ref     : 0
% 2.94/1.38  #Sup     : 93
% 2.94/1.38  #Fact    : 0
% 2.94/1.38  #Define  : 0
% 2.94/1.38  #Split   : 6
% 2.94/1.38  #Chain   : 0
% 2.94/1.38  #Close   : 0
% 2.94/1.38  
% 2.94/1.38  Ordering : KBO
% 2.94/1.38  
% 2.94/1.38  Simplification rules
% 2.94/1.38  ----------------------
% 2.94/1.38  #Subsume      : 13
% 2.94/1.38  #Demod        : 81
% 2.94/1.38  #Tautology    : 34
% 2.94/1.38  #SimpNegUnit  : 9
% 2.94/1.38  #BackRed      : 5
% 2.94/1.38  
% 2.94/1.38  #Partial instantiations: 0
% 2.94/1.38  #Strategies tried      : 1
% 2.94/1.38  
% 2.94/1.38  Timing (in seconds)
% 2.94/1.38  ----------------------
% 2.94/1.39  Preprocessing        : 0.31
% 2.94/1.39  Parsing              : 0.16
% 2.94/1.39  CNF conversion       : 0.02
% 2.94/1.39  Main loop            : 0.31
% 2.94/1.39  Inferencing          : 0.12
% 2.94/1.39  Reduction            : 0.09
% 2.94/1.39  Demodulation         : 0.06
% 2.94/1.39  BG Simplification    : 0.02
% 2.94/1.39  Subsumption          : 0.05
% 2.94/1.39  Abstraction          : 0.02
% 2.94/1.39  MUC search           : 0.00
% 2.94/1.39  Cooper               : 0.00
% 2.94/1.39  Total                : 0.66
% 2.94/1.39  Index Insertion      : 0.00
% 2.94/1.39  Index Deletion       : 0.00
% 2.94/1.39  Index Matching       : 0.00
% 2.94/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

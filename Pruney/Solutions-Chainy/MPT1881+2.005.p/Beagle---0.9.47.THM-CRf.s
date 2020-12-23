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
% DateTime   : Thu Dec  3 10:30:06 EST 2020

% Result     : Theorem 6.22s
% Output     : CNFRefutation 6.22s
% Verified   : 
% Statistics : Number of formulae       :  194 (1276 expanded)
%              Number of leaves         :   47 ( 447 expanded)
%              Depth                    :   15
%              Number of atoms          :  494 (3516 expanded)
%              Number of equality atoms :   66 ( 499 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_30,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_233,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

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

tff(f_143,axiom,(
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

tff(f_122,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_168,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_215,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_183,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

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

tff(f_154,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_199,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_subset_1(k2_subset_1(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_79,plain,(
    ! [A_2] : ~ v1_subset_1(A_2,A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_66,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1105,plain,(
    ! [A_159] :
      ( u1_struct_0(A_159) = k2_struct_0(A_159)
      | ~ l1_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1110,plain,(
    ! [A_160] :
      ( u1_struct_0(A_160) = k2_struct_0(A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(resolution,[status(thm)],[c_8,c_1105])).

tff(c_1114,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1110])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_1116,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_62])).

tff(c_2708,plain,(
    ! [A_306,B_307] :
      ( v1_pre_topc('#skF_1'(A_306,B_307))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_306)))
      | v1_xboole_0(B_307)
      | ~ l1_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2720,plain,(
    ! [B_307] :
      ( v1_pre_topc('#skF_1'('#skF_3',B_307))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(B_307)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_2708])).

tff(c_2725,plain,(
    ! [B_307] :
      ( v1_pre_topc('#skF_1'('#skF_3',B_307))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(B_307)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2720])).

tff(c_2727,plain,(
    ! [B_308] :
      ( v1_pre_topc('#skF_1'('#skF_3',B_308))
      | ~ m1_subset_1(B_308,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(B_308) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2725])).

tff(c_2735,plain,
    ( v1_pre_topc('#skF_1'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1116,c_2727])).

tff(c_2736,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2735])).

tff(c_93,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_102,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_98])).

tff(c_78,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_92,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_103,plain,(
    ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_92])).

tff(c_72,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_109,plain,
    ( v1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_72])).

tff(c_110,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_109])).

tff(c_104,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_62])).

tff(c_120,plain,(
    ! [B_58,A_59] :
      ( v1_subset_1(B_58,A_59)
      | B_58 = A_59
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_123,plain,
    ( v1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_104,c_120])).

tff(c_126,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_123])).

tff(c_14,plain,(
    ! [A_8] :
      ( k2_pre_topc(A_8,k2_struct_0(A_8)) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_133,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_14])).

tff(c_137,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_126,c_133])).

tff(c_127,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_104])).

tff(c_129,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_102])).

tff(c_300,plain,(
    ! [B_88,A_89] :
      ( v1_tops_1(B_88,A_89)
      | k2_pre_topc(A_89,B_88) != u1_struct_0(A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_312,plain,(
    ! [B_88] :
      ( v1_tops_1(B_88,'#skF_3')
      | k2_pre_topc('#skF_3',B_88) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_88,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_300])).

tff(c_336,plain,(
    ! [B_92] :
      ( v1_tops_1(B_92,'#skF_3')
      | k2_pre_topc('#skF_3',B_92) != '#skF_4'
      | ~ m1_subset_1(B_92,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_129,c_312])).

tff(c_342,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_127,c_336])).

tff(c_346,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_342])).

tff(c_819,plain,(
    ! [B_136,A_137] :
      ( v2_tex_2(B_136,A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137)
      | ~ v1_tdlat_3(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_837,plain,(
    ! [B_136] :
      ( v2_tex_2(B_136,'#skF_3')
      | ~ m1_subset_1(B_136,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_819])).

tff(c_843,plain,(
    ! [B_136] :
      ( v2_tex_2(B_136,'#skF_3')
      | ~ m1_subset_1(B_136,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_837])).

tff(c_845,plain,(
    ! [B_138] :
      ( v2_tex_2(B_138,'#skF_3')
      | ~ m1_subset_1(B_138,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_843])).

tff(c_853,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_845])).

tff(c_1044,plain,(
    ! [B_155,A_156] :
      ( v3_tex_2(B_155,A_156)
      | ~ v2_tex_2(B_155,A_156)
      | ~ v1_tops_1(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_1065,plain,(
    ! [B_155] :
      ( v3_tex_2(B_155,'#skF_3')
      | ~ v2_tex_2(B_155,'#skF_3')
      | ~ v1_tops_1(B_155,'#skF_3')
      | ~ m1_subset_1(B_155,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_1044])).

tff(c_1072,plain,(
    ! [B_155] :
      ( v3_tex_2(B_155,'#skF_3')
      | ~ v2_tex_2(B_155,'#skF_3')
      | ~ v1_tops_1(B_155,'#skF_3')
      | ~ m1_subset_1(B_155,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1065])).

tff(c_1087,plain,(
    ! [B_158] :
      ( v3_tex_2(B_158,'#skF_3')
      | ~ v2_tex_2(B_158,'#skF_3')
      | ~ v1_tops_1(B_158,'#skF_3')
      | ~ m1_subset_1(B_158,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1072])).

tff(c_1093,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_1087])).

tff(c_1097,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_853,c_1093])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_1097])).

tff(c_1100,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_3122,plain,(
    ! [B_347,A_348] :
      ( ~ v3_tex_2(B_347,A_348)
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ v1_xboole_0(B_347)
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348)
      | v2_struct_0(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_3137,plain,(
    ! [B_347] :
      ( ~ v3_tex_2(B_347,'#skF_3')
      | ~ m1_subset_1(B_347,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v1_xboole_0(B_347)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_3122])).

tff(c_3144,plain,(
    ! [B_347] :
      ( ~ v3_tex_2(B_347,'#skF_3')
      | ~ m1_subset_1(B_347,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v1_xboole_0(B_347)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_3137])).

tff(c_3146,plain,(
    ! [B_349] :
      ( ~ v3_tex_2(B_349,'#skF_3')
      | ~ m1_subset_1(B_349,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v1_xboole_0(B_349) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3144])).

tff(c_3152,plain,
    ( ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1116,c_3146])).

tff(c_3157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2736,c_1100,c_3152])).

tff(c_3159,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2735])).

tff(c_3247,plain,(
    ! [A_365,B_366] :
      ( m1_pre_topc('#skF_1'(A_365,B_366),A_365)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_365)))
      | v1_xboole_0(B_366)
      | ~ l1_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3255,plain,(
    ! [B_366] :
      ( m1_pre_topc('#skF_1'('#skF_3',B_366),'#skF_3')
      | ~ m1_subset_1(B_366,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(B_366)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_3247])).

tff(c_3260,plain,(
    ! [B_366] :
      ( m1_pre_topc('#skF_1'('#skF_3',B_366),'#skF_3')
      | ~ m1_subset_1(B_366,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(B_366)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3255])).

tff(c_3262,plain,(
    ! [B_367] :
      ( m1_pre_topc('#skF_1'('#skF_3',B_367),'#skF_3')
      | ~ m1_subset_1(B_367,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(B_367) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3260])).

tff(c_3268,plain,
    ( m1_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1116,c_3262])).

tff(c_3272,plain,(
    m1_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3159,c_3268])).

tff(c_30,plain,(
    ! [B_22,A_20] :
      ( v1_borsuk_1(B_22,A_20)
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v1_tdlat_3(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1187,plain,(
    ! [A_175,B_176] :
      ( k2_pre_topc(A_175,B_176) = B_176
      | ~ v4_pre_topc(B_176,A_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1199,plain,(
    ! [B_176] :
      ( k2_pre_topc('#skF_3',B_176) = B_176
      | ~ v4_pre_topc(B_176,'#skF_3')
      | ~ m1_subset_1(B_176,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_1187])).

tff(c_1205,plain,(
    ! [B_177] :
      ( k2_pre_topc('#skF_3',B_177) = B_177
      | ~ v4_pre_topc(B_177,'#skF_3')
      | ~ m1_subset_1(B_177,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1199])).

tff(c_1213,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1116,c_1205])).

tff(c_1214,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1213])).

tff(c_1280,plain,(
    ! [A_191,B_192] :
      ( k2_pre_topc(A_191,B_192) = u1_struct_0(A_191)
      | ~ v1_tops_1(B_192,A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1292,plain,(
    ! [B_192] :
      ( k2_pre_topc('#skF_3',B_192) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_192,'#skF_3')
      | ~ m1_subset_1(B_192,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_1280])).

tff(c_1332,plain,(
    ! [B_197] :
      ( k2_pre_topc('#skF_3',B_197) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_197,'#skF_3')
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1114,c_1292])).

tff(c_1340,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1116,c_1332])).

tff(c_1341,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1340])).

tff(c_1220,plain,(
    ! [B_179,A_180] :
      ( v3_pre_topc(B_179,A_180)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ v1_tdlat_3(A_180)
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1232,plain,(
    ! [B_179] :
      ( v3_pre_topc(B_179,'#skF_3')
      | ~ m1_subset_1(B_179,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v1_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_1220])).

tff(c_1238,plain,(
    ! [B_181] :
      ( v3_pre_topc(B_181,'#skF_3')
      | ~ m1_subset_1(B_181,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_66,c_1232])).

tff(c_1246,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1116,c_1238])).

tff(c_2653,plain,(
    ! [B_301,A_302] :
      ( v1_tops_1(B_301,A_302)
      | ~ v3_tex_2(B_301,A_302)
      | ~ v3_pre_topc(B_301,A_302)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302)
      | v2_struct_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_2674,plain,(
    ! [B_301] :
      ( v1_tops_1(B_301,'#skF_3')
      | ~ v3_tex_2(B_301,'#skF_3')
      | ~ v3_pre_topc(B_301,'#skF_3')
      | ~ m1_subset_1(B_301,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_2653])).

tff(c_2681,plain,(
    ! [B_301] :
      ( v1_tops_1(B_301,'#skF_3')
      | ~ v3_tex_2(B_301,'#skF_3')
      | ~ v3_pre_topc(B_301,'#skF_3')
      | ~ m1_subset_1(B_301,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2674])).

tff(c_2683,plain,(
    ! [B_303] :
      ( v1_tops_1(B_303,'#skF_3')
      | ~ v3_tex_2(B_303,'#skF_3')
      | ~ v3_pre_topc(B_303,'#skF_3')
      | ~ m1_subset_1(B_303,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2681])).

tff(c_2689,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1116,c_2683])).

tff(c_2693,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1246,c_1100,c_2689])).

tff(c_2695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1341,c_2693])).

tff(c_2696,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1340])).

tff(c_3308,plain,(
    ! [B_373,A_374] :
      ( v4_pre_topc(B_373,A_374)
      | k2_pre_topc(A_374,B_373) != B_373
      | ~ v2_pre_topc(A_374)
      | ~ m1_subset_1(B_373,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ l1_pre_topc(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3320,plain,(
    ! [B_373] :
      ( v4_pre_topc(B_373,'#skF_3')
      | k2_pre_topc('#skF_3',B_373) != B_373
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(B_373,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_3308])).

tff(c_3326,plain,(
    ! [B_375] :
      ( v4_pre_topc(B_375,'#skF_3')
      | k2_pre_topc('#skF_3',B_375) != B_375
      | ~ m1_subset_1(B_375,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_3320])).

tff(c_3332,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1116,c_3326])).

tff(c_3335,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2696,c_3332])).

tff(c_3336,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1214,c_3335])).

tff(c_3355,plain,(
    ! [A_377,B_378] :
      ( u1_struct_0('#skF_1'(A_377,B_378)) = B_378
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | v1_xboole_0(B_378)
      | ~ l1_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3367,plain,(
    ! [B_378] :
      ( u1_struct_0('#skF_1'('#skF_3',B_378)) = B_378
      | ~ m1_subset_1(B_378,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(B_378)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_3355])).

tff(c_3373,plain,(
    ! [B_378] :
      ( u1_struct_0('#skF_1'('#skF_3',B_378)) = B_378
      | ~ m1_subset_1(B_378,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(B_378)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3367])).

tff(c_3375,plain,(
    ! [B_379] :
      ( u1_struct_0('#skF_1'('#skF_3',B_379)) = B_379
      | ~ m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(B_379) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3373])).

tff(c_3381,plain,
    ( u1_struct_0('#skF_1'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1116,c_3375])).

tff(c_3385,plain,(
    u1_struct_0('#skF_1'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3159,c_3381])).

tff(c_22,plain,(
    ! [B_18,A_16] :
      ( m1_subset_1(u1_struct_0(B_18),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4190,plain,(
    ! [B_423,A_424] :
      ( v4_pre_topc(u1_struct_0(B_423),A_424)
      | ~ v1_borsuk_1(B_423,A_424)
      | ~ m1_subset_1(u1_struct_0(B_423),k1_zfmisc_1(u1_struct_0(A_424)))
      | ~ m1_pre_topc(B_423,A_424)
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4217,plain,(
    ! [B_425,A_426] :
      ( v4_pre_topc(u1_struct_0(B_425),A_426)
      | ~ v1_borsuk_1(B_425,A_426)
      | ~ v2_pre_topc(A_426)
      | ~ m1_pre_topc(B_425,A_426)
      | ~ l1_pre_topc(A_426) ) ),
    inference(resolution,[status(thm)],[c_22,c_4190])).

tff(c_1137,plain,(
    ! [B_165,A_166] :
      ( m1_subset_1(u1_struct_0(B_165),k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ m1_pre_topc(B_165,A_166)
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1146,plain,(
    ! [B_165] :
      ( m1_subset_1(u1_struct_0(B_165),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_165,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_1137])).

tff(c_1149,plain,(
    ! [B_165] :
      ( m1_subset_1(u1_struct_0(B_165),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_165,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1146])).

tff(c_1212,plain,(
    ! [B_165] :
      ( k2_pre_topc('#skF_3',u1_struct_0(B_165)) = u1_struct_0(B_165)
      | ~ v4_pre_topc(u1_struct_0(B_165),'#skF_3')
      | ~ m1_pre_topc(B_165,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1149,c_1205])).

tff(c_4231,plain,(
    ! [B_425] :
      ( k2_pre_topc('#skF_3',u1_struct_0(B_425)) = u1_struct_0(B_425)
      | ~ v1_borsuk_1(B_425,'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_425,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4217,c_1212])).

tff(c_4249,plain,(
    ! [B_427] :
      ( k2_pre_topc('#skF_3',u1_struct_0(B_427)) = u1_struct_0(B_427)
      | ~ v1_borsuk_1(B_427,'#skF_3')
      | ~ m1_pre_topc(B_427,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_4231])).

tff(c_4264,plain,
    ( u1_struct_0('#skF_1'('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4')
    | ~ v1_borsuk_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3385,c_4249])).

tff(c_4272,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_borsuk_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3385,c_2696,c_4264])).

tff(c_4273,plain,(
    ~ v1_borsuk_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3336,c_4272])).

tff(c_4277,plain,
    ( ~ m1_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_4273])).

tff(c_4280,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_3272,c_4277])).

tff(c_4282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4280])).

tff(c_4283,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1213])).

tff(c_4694,plain,(
    ! [B_490,A_491] :
      ( v1_tops_1(B_490,A_491)
      | k2_pre_topc(A_491,B_490) != u1_struct_0(A_491)
      | ~ m1_subset_1(B_490,k1_zfmisc_1(u1_struct_0(A_491)))
      | ~ l1_pre_topc(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4706,plain,(
    ! [B_490] :
      ( v1_tops_1(B_490,'#skF_3')
      | k2_pre_topc('#skF_3',B_490) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_490,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_4694])).

tff(c_4712,plain,(
    ! [B_492] :
      ( v1_tops_1(B_492,'#skF_3')
      | k2_pre_topc('#skF_3',B_492) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_492,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1114,c_4706])).

tff(c_4718,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1116,c_4712])).

tff(c_4721,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4283,c_4718])).

tff(c_4740,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4721])).

tff(c_4722,plain,(
    ! [A_493,B_494] :
      ( k2_pre_topc(A_493,B_494) = u1_struct_0(A_493)
      | ~ v1_tops_1(B_494,A_493)
      | ~ m1_subset_1(B_494,k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ l1_pre_topc(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4734,plain,(
    ! [B_494] :
      ( k2_pre_topc('#skF_3',B_494) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_494,'#skF_3')
      | ~ m1_subset_1(B_494,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_4722])).

tff(c_4741,plain,(
    ! [B_495] :
      ( k2_pre_topc('#skF_3',B_495) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_495,'#skF_3')
      | ~ m1_subset_1(B_495,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1114,c_4734])).

tff(c_4747,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1116,c_4741])).

tff(c_4750,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4283,c_4747])).

tff(c_4751,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_4740,c_4750])).

tff(c_4295,plain,(
    ! [B_431,A_432] :
      ( v3_pre_topc(B_431,A_432)
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0(A_432)))
      | ~ v1_tdlat_3(A_432)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4307,plain,(
    ! [B_431] :
      ( v3_pre_topc(B_431,'#skF_3')
      | ~ m1_subset_1(B_431,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v1_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_4295])).

tff(c_4313,plain,(
    ! [B_433] :
      ( v3_pre_topc(B_433,'#skF_3')
      | ~ m1_subset_1(B_433,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_66,c_4307])).

tff(c_4321,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1116,c_4313])).

tff(c_5540,plain,(
    ! [B_553,A_554] :
      ( v1_tops_1(B_553,A_554)
      | ~ v3_tex_2(B_553,A_554)
      | ~ v3_pre_topc(B_553,A_554)
      | ~ m1_subset_1(B_553,k1_zfmisc_1(u1_struct_0(A_554)))
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554)
      | v2_struct_0(A_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_5561,plain,(
    ! [B_553] :
      ( v1_tops_1(B_553,'#skF_3')
      | ~ v3_tex_2(B_553,'#skF_3')
      | ~ v3_pre_topc(B_553,'#skF_3')
      | ~ m1_subset_1(B_553,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_5540])).

tff(c_5568,plain,(
    ! [B_553] :
      ( v1_tops_1(B_553,'#skF_3')
      | ~ v3_tex_2(B_553,'#skF_3')
      | ~ v3_pre_topc(B_553,'#skF_3')
      | ~ m1_subset_1(B_553,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_5561])).

tff(c_5570,plain,(
    ! [B_555] :
      ( v1_tops_1(B_555,'#skF_3')
      | ~ v3_tex_2(B_555,'#skF_3')
      | ~ v3_pre_topc(B_555,'#skF_3')
      | ~ m1_subset_1(B_555,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5568])).

tff(c_5576,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1116,c_5570])).

tff(c_5580,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4321,c_1100,c_5576])).

tff(c_5582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4751,c_5580])).

tff(c_5584,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4721])).

tff(c_1103,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_72])).

tff(c_1115,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_1103])).

tff(c_5596,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5584,c_1115])).

tff(c_5599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_5596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.22/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.22/2.31  
% 6.22/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.22/2.32  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.22/2.32  
% 6.22/2.32  %Foreground sorts:
% 6.22/2.32  
% 6.22/2.32  
% 6.22/2.32  %Background operators:
% 6.22/2.32  
% 6.22/2.32  
% 6.22/2.32  %Foreground operators:
% 6.22/2.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.22/2.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.22/2.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.22/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.22/2.32  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.22/2.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.22/2.32  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 6.22/2.32  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 6.22/2.32  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.22/2.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.22/2.32  tff('#skF_3', type, '#skF_3': $i).
% 6.22/2.32  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.22/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.22/2.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.22/2.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.22/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.22/2.32  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 6.22/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.22/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.22/2.32  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.22/2.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.22/2.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.22/2.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.22/2.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.22/2.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.22/2.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.22/2.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.22/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.22/2.32  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 6.22/2.32  
% 6.22/2.34  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.22/2.34  tff(f_30, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 6.22/2.34  tff(f_233, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 6.22/2.34  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.22/2.34  tff(f_34, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.22/2.34  tff(f_143, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 6.22/2.34  tff(f_122, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 6.22/2.34  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 6.22/2.34  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 6.22/2.34  tff(f_168, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 6.22/2.34  tff(f_215, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 6.22/2.34  tff(f_183, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 6.22/2.34  tff(f_106, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 6.22/2.34  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.22/2.34  tff(f_154, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 6.22/2.34  tff(f_199, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 6.22/2.34  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.22/2.34  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tsep_1)).
% 6.22/2.34  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.22/2.34  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_subset_1(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.22/2.34  tff(c_79, plain, (![A_2]: (~v1_subset_1(A_2, A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 6.22/2.34  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.22/2.34  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.22/2.34  tff(c_66, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.22/2.34  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.22/2.34  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.22/2.34  tff(c_1105, plain, (![A_159]: (u1_struct_0(A_159)=k2_struct_0(A_159) | ~l1_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.22/2.34  tff(c_1110, plain, (![A_160]: (u1_struct_0(A_160)=k2_struct_0(A_160) | ~l1_pre_topc(A_160))), inference(resolution, [status(thm)], [c_8, c_1105])).
% 6.22/2.34  tff(c_1114, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1110])).
% 6.22/2.34  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.22/2.34  tff(c_1116, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_62])).
% 6.22/2.34  tff(c_2708, plain, (![A_306, B_307]: (v1_pre_topc('#skF_1'(A_306, B_307)) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_306))) | v1_xboole_0(B_307) | ~l1_pre_topc(A_306) | v2_struct_0(A_306))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.22/2.34  tff(c_2720, plain, (![B_307]: (v1_pre_topc('#skF_1'('#skF_3', B_307)) | ~m1_subset_1(B_307, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(B_307) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_2708])).
% 6.22/2.34  tff(c_2725, plain, (![B_307]: (v1_pre_topc('#skF_1'('#skF_3', B_307)) | ~m1_subset_1(B_307, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(B_307) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2720])).
% 6.22/2.34  tff(c_2727, plain, (![B_308]: (v1_pre_topc('#skF_1'('#skF_3', B_308)) | ~m1_subset_1(B_308, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(B_308))), inference(negUnitSimplification, [status(thm)], [c_70, c_2725])).
% 6.22/2.34  tff(c_2735, plain, (v1_pre_topc('#skF_1'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1116, c_2727])).
% 6.22/2.34  tff(c_2736, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2735])).
% 6.22/2.34  tff(c_93, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.22/2.34  tff(c_98, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_8, c_93])).
% 6.22/2.34  tff(c_102, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_98])).
% 6.22/2.34  tff(c_78, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.22/2.34  tff(c_92, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_78])).
% 6.22/2.34  tff(c_103, plain, (~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_92])).
% 6.22/2.34  tff(c_72, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.22/2.34  tff(c_109, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_72])).
% 6.22/2.34  tff(c_110, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_103, c_109])).
% 6.22/2.34  tff(c_104, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_62])).
% 6.22/2.34  tff(c_120, plain, (![B_58, A_59]: (v1_subset_1(B_58, A_59) | B_58=A_59 | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.22/2.34  tff(c_123, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_104, c_120])).
% 6.22/2.34  tff(c_126, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_103, c_123])).
% 6.22/2.34  tff(c_14, plain, (![A_8]: (k2_pre_topc(A_8, k2_struct_0(A_8))=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.22/2.34  tff(c_133, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_126, c_14])).
% 6.22/2.34  tff(c_137, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_126, c_133])).
% 6.22/2.34  tff(c_127, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_104])).
% 6.22/2.34  tff(c_129, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_102])).
% 6.22/2.34  tff(c_300, plain, (![B_88, A_89]: (v1_tops_1(B_88, A_89) | k2_pre_topc(A_89, B_88)!=u1_struct_0(A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.22/2.34  tff(c_312, plain, (![B_88]: (v1_tops_1(B_88, '#skF_3') | k2_pre_topc('#skF_3', B_88)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_88, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_300])).
% 6.22/2.34  tff(c_336, plain, (![B_92]: (v1_tops_1(B_92, '#skF_3') | k2_pre_topc('#skF_3', B_92)!='#skF_4' | ~m1_subset_1(B_92, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_129, c_312])).
% 6.22/2.34  tff(c_342, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_127, c_336])).
% 6.22/2.34  tff(c_346, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_342])).
% 6.22/2.34  tff(c_819, plain, (![B_136, A_137]: (v2_tex_2(B_136, A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137) | ~v1_tdlat_3(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.22/2.34  tff(c_837, plain, (![B_136]: (v2_tex_2(B_136, '#skF_3') | ~m1_subset_1(B_136, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_819])).
% 6.22/2.34  tff(c_843, plain, (![B_136]: (v2_tex_2(B_136, '#skF_3') | ~m1_subset_1(B_136, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_837])).
% 6.22/2.34  tff(c_845, plain, (![B_138]: (v2_tex_2(B_138, '#skF_3') | ~m1_subset_1(B_138, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_843])).
% 6.22/2.34  tff(c_853, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_127, c_845])).
% 6.22/2.34  tff(c_1044, plain, (![B_155, A_156]: (v3_tex_2(B_155, A_156) | ~v2_tex_2(B_155, A_156) | ~v1_tops_1(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_215])).
% 6.22/2.34  tff(c_1065, plain, (![B_155]: (v3_tex_2(B_155, '#skF_3') | ~v2_tex_2(B_155, '#skF_3') | ~v1_tops_1(B_155, '#skF_3') | ~m1_subset_1(B_155, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_1044])).
% 6.22/2.34  tff(c_1072, plain, (![B_155]: (v3_tex_2(B_155, '#skF_3') | ~v2_tex_2(B_155, '#skF_3') | ~v1_tops_1(B_155, '#skF_3') | ~m1_subset_1(B_155, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1065])).
% 6.22/2.34  tff(c_1087, plain, (![B_158]: (v3_tex_2(B_158, '#skF_3') | ~v2_tex_2(B_158, '#skF_3') | ~v1_tops_1(B_158, '#skF_3') | ~m1_subset_1(B_158, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_1072])).
% 6.22/2.34  tff(c_1093, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_127, c_1087])).
% 6.22/2.34  tff(c_1097, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_853, c_1093])).
% 6.22/2.34  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_1097])).
% 6.22/2.34  tff(c_1100, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_78])).
% 6.22/2.34  tff(c_3122, plain, (![B_347, A_348]: (~v3_tex_2(B_347, A_348) | ~m1_subset_1(B_347, k1_zfmisc_1(u1_struct_0(A_348))) | ~v1_xboole_0(B_347) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348) | v2_struct_0(A_348))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.22/2.34  tff(c_3137, plain, (![B_347]: (~v3_tex_2(B_347, '#skF_3') | ~m1_subset_1(B_347, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v1_xboole_0(B_347) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_3122])).
% 6.22/2.34  tff(c_3144, plain, (![B_347]: (~v3_tex_2(B_347, '#skF_3') | ~m1_subset_1(B_347, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v1_xboole_0(B_347) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_3137])).
% 6.22/2.34  tff(c_3146, plain, (![B_349]: (~v3_tex_2(B_349, '#skF_3') | ~m1_subset_1(B_349, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v1_xboole_0(B_349))), inference(negUnitSimplification, [status(thm)], [c_70, c_3144])).
% 6.22/2.34  tff(c_3152, plain, (~v3_tex_2('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1116, c_3146])).
% 6.22/2.34  tff(c_3157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2736, c_1100, c_3152])).
% 6.22/2.34  tff(c_3159, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_2735])).
% 6.22/2.34  tff(c_3247, plain, (![A_365, B_366]: (m1_pre_topc('#skF_1'(A_365, B_366), A_365) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_365))) | v1_xboole_0(B_366) | ~l1_pre_topc(A_365) | v2_struct_0(A_365))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.22/2.34  tff(c_3255, plain, (![B_366]: (m1_pre_topc('#skF_1'('#skF_3', B_366), '#skF_3') | ~m1_subset_1(B_366, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(B_366) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_3247])).
% 6.22/2.34  tff(c_3260, plain, (![B_366]: (m1_pre_topc('#skF_1'('#skF_3', B_366), '#skF_3') | ~m1_subset_1(B_366, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(B_366) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3255])).
% 6.22/2.34  tff(c_3262, plain, (![B_367]: (m1_pre_topc('#skF_1'('#skF_3', B_367), '#skF_3') | ~m1_subset_1(B_367, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(B_367))), inference(negUnitSimplification, [status(thm)], [c_70, c_3260])).
% 6.22/2.34  tff(c_3268, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1116, c_3262])).
% 6.22/2.34  tff(c_3272, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_3159, c_3268])).
% 6.22/2.34  tff(c_30, plain, (![B_22, A_20]: (v1_borsuk_1(B_22, A_20) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20) | ~v1_tdlat_3(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.22/2.34  tff(c_1187, plain, (![A_175, B_176]: (k2_pre_topc(A_175, B_176)=B_176 | ~v4_pre_topc(B_176, A_175) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.22/2.34  tff(c_1199, plain, (![B_176]: (k2_pre_topc('#skF_3', B_176)=B_176 | ~v4_pre_topc(B_176, '#skF_3') | ~m1_subset_1(B_176, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_1187])).
% 6.22/2.34  tff(c_1205, plain, (![B_177]: (k2_pre_topc('#skF_3', B_177)=B_177 | ~v4_pre_topc(B_177, '#skF_3') | ~m1_subset_1(B_177, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1199])).
% 6.22/2.34  tff(c_1213, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1116, c_1205])).
% 6.22/2.34  tff(c_1214, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1213])).
% 6.22/2.34  tff(c_1280, plain, (![A_191, B_192]: (k2_pre_topc(A_191, B_192)=u1_struct_0(A_191) | ~v1_tops_1(B_192, A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.22/2.34  tff(c_1292, plain, (![B_192]: (k2_pre_topc('#skF_3', B_192)=u1_struct_0('#skF_3') | ~v1_tops_1(B_192, '#skF_3') | ~m1_subset_1(B_192, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_1280])).
% 6.22/2.34  tff(c_1332, plain, (![B_197]: (k2_pre_topc('#skF_3', B_197)=k2_struct_0('#skF_3') | ~v1_tops_1(B_197, '#skF_3') | ~m1_subset_1(B_197, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1114, c_1292])).
% 6.22/2.34  tff(c_1340, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1116, c_1332])).
% 6.22/2.34  tff(c_1341, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1340])).
% 6.22/2.34  tff(c_1220, plain, (![B_179, A_180]: (v3_pre_topc(B_179, A_180) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_180))) | ~v1_tdlat_3(A_180) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.22/2.34  tff(c_1232, plain, (![B_179]: (v3_pre_topc(B_179, '#skF_3') | ~m1_subset_1(B_179, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_1220])).
% 6.22/2.34  tff(c_1238, plain, (![B_181]: (v3_pre_topc(B_181, '#skF_3') | ~m1_subset_1(B_181, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_66, c_1232])).
% 6.22/2.34  tff(c_1246, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1116, c_1238])).
% 6.22/2.34  tff(c_2653, plain, (![B_301, A_302]: (v1_tops_1(B_301, A_302) | ~v3_tex_2(B_301, A_302) | ~v3_pre_topc(B_301, A_302) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_302))) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302) | v2_struct_0(A_302))), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.22/2.34  tff(c_2674, plain, (![B_301]: (v1_tops_1(B_301, '#skF_3') | ~v3_tex_2(B_301, '#skF_3') | ~v3_pre_topc(B_301, '#skF_3') | ~m1_subset_1(B_301, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_2653])).
% 6.22/2.34  tff(c_2681, plain, (![B_301]: (v1_tops_1(B_301, '#skF_3') | ~v3_tex_2(B_301, '#skF_3') | ~v3_pre_topc(B_301, '#skF_3') | ~m1_subset_1(B_301, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2674])).
% 6.22/2.34  tff(c_2683, plain, (![B_303]: (v1_tops_1(B_303, '#skF_3') | ~v3_tex_2(B_303, '#skF_3') | ~v3_pre_topc(B_303, '#skF_3') | ~m1_subset_1(B_303, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_2681])).
% 6.22/2.34  tff(c_2689, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1116, c_2683])).
% 6.22/2.34  tff(c_2693, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1246, c_1100, c_2689])).
% 6.22/2.34  tff(c_2695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1341, c_2693])).
% 6.22/2.34  tff(c_2696, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1340])).
% 6.22/2.34  tff(c_3308, plain, (![B_373, A_374]: (v4_pre_topc(B_373, A_374) | k2_pre_topc(A_374, B_373)!=B_373 | ~v2_pre_topc(A_374) | ~m1_subset_1(B_373, k1_zfmisc_1(u1_struct_0(A_374))) | ~l1_pre_topc(A_374))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.22/2.34  tff(c_3320, plain, (![B_373]: (v4_pre_topc(B_373, '#skF_3') | k2_pre_topc('#skF_3', B_373)!=B_373 | ~v2_pre_topc('#skF_3') | ~m1_subset_1(B_373, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_3308])).
% 6.22/2.34  tff(c_3326, plain, (![B_375]: (v4_pre_topc(B_375, '#skF_3') | k2_pre_topc('#skF_3', B_375)!=B_375 | ~m1_subset_1(B_375, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_3320])).
% 6.22/2.34  tff(c_3332, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_1116, c_3326])).
% 6.22/2.34  tff(c_3335, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2696, c_3332])).
% 6.22/2.34  tff(c_3336, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1214, c_3335])).
% 6.22/2.34  tff(c_3355, plain, (![A_377, B_378]: (u1_struct_0('#skF_1'(A_377, B_378))=B_378 | ~m1_subset_1(B_378, k1_zfmisc_1(u1_struct_0(A_377))) | v1_xboole_0(B_378) | ~l1_pre_topc(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.22/2.34  tff(c_3367, plain, (![B_378]: (u1_struct_0('#skF_1'('#skF_3', B_378))=B_378 | ~m1_subset_1(B_378, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(B_378) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_3355])).
% 6.22/2.34  tff(c_3373, plain, (![B_378]: (u1_struct_0('#skF_1'('#skF_3', B_378))=B_378 | ~m1_subset_1(B_378, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(B_378) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3367])).
% 6.22/2.34  tff(c_3375, plain, (![B_379]: (u1_struct_0('#skF_1'('#skF_3', B_379))=B_379 | ~m1_subset_1(B_379, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(B_379))), inference(negUnitSimplification, [status(thm)], [c_70, c_3373])).
% 6.22/2.34  tff(c_3381, plain, (u1_struct_0('#skF_1'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1116, c_3375])).
% 6.22/2.34  tff(c_3385, plain, (u1_struct_0('#skF_1'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3159, c_3381])).
% 6.22/2.34  tff(c_22, plain, (![B_18, A_16]: (m1_subset_1(u1_struct_0(B_18), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.22/2.34  tff(c_4190, plain, (![B_423, A_424]: (v4_pre_topc(u1_struct_0(B_423), A_424) | ~v1_borsuk_1(B_423, A_424) | ~m1_subset_1(u1_struct_0(B_423), k1_zfmisc_1(u1_struct_0(A_424))) | ~m1_pre_topc(B_423, A_424) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.22/2.34  tff(c_4217, plain, (![B_425, A_426]: (v4_pre_topc(u1_struct_0(B_425), A_426) | ~v1_borsuk_1(B_425, A_426) | ~v2_pre_topc(A_426) | ~m1_pre_topc(B_425, A_426) | ~l1_pre_topc(A_426))), inference(resolution, [status(thm)], [c_22, c_4190])).
% 6.22/2.34  tff(c_1137, plain, (![B_165, A_166]: (m1_subset_1(u1_struct_0(B_165), k1_zfmisc_1(u1_struct_0(A_166))) | ~m1_pre_topc(B_165, A_166) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.22/2.34  tff(c_1146, plain, (![B_165]: (m1_subset_1(u1_struct_0(B_165), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_165, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_1137])).
% 6.22/2.34  tff(c_1149, plain, (![B_165]: (m1_subset_1(u1_struct_0(B_165), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_165, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1146])).
% 6.22/2.34  tff(c_1212, plain, (![B_165]: (k2_pre_topc('#skF_3', u1_struct_0(B_165))=u1_struct_0(B_165) | ~v4_pre_topc(u1_struct_0(B_165), '#skF_3') | ~m1_pre_topc(B_165, '#skF_3'))), inference(resolution, [status(thm)], [c_1149, c_1205])).
% 6.22/2.34  tff(c_4231, plain, (![B_425]: (k2_pre_topc('#skF_3', u1_struct_0(B_425))=u1_struct_0(B_425) | ~v1_borsuk_1(B_425, '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc(B_425, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_4217, c_1212])).
% 6.22/2.34  tff(c_4249, plain, (![B_427]: (k2_pre_topc('#skF_3', u1_struct_0(B_427))=u1_struct_0(B_427) | ~v1_borsuk_1(B_427, '#skF_3') | ~m1_pre_topc(B_427, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_4231])).
% 6.22/2.34  tff(c_4264, plain, (u1_struct_0('#skF_1'('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4') | ~v1_borsuk_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3385, c_4249])).
% 6.22/2.34  tff(c_4272, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_borsuk_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3385, c_2696, c_4264])).
% 6.22/2.34  tff(c_4273, plain, (~v1_borsuk_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_3336, c_4272])).
% 6.22/2.34  tff(c_4277, plain, (~m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_4273])).
% 6.22/2.34  tff(c_4280, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_3272, c_4277])).
% 6.22/2.34  tff(c_4282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_4280])).
% 6.22/2.34  tff(c_4283, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1213])).
% 6.22/2.34  tff(c_4694, plain, (![B_490, A_491]: (v1_tops_1(B_490, A_491) | k2_pre_topc(A_491, B_490)!=u1_struct_0(A_491) | ~m1_subset_1(B_490, k1_zfmisc_1(u1_struct_0(A_491))) | ~l1_pre_topc(A_491))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.22/2.34  tff(c_4706, plain, (![B_490]: (v1_tops_1(B_490, '#skF_3') | k2_pre_topc('#skF_3', B_490)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_490, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_4694])).
% 6.22/2.34  tff(c_4712, plain, (![B_492]: (v1_tops_1(B_492, '#skF_3') | k2_pre_topc('#skF_3', B_492)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_492, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1114, c_4706])).
% 6.22/2.34  tff(c_4718, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1116, c_4712])).
% 6.22/2.34  tff(c_4721, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4283, c_4718])).
% 6.22/2.34  tff(c_4740, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_4721])).
% 6.22/2.34  tff(c_4722, plain, (![A_493, B_494]: (k2_pre_topc(A_493, B_494)=u1_struct_0(A_493) | ~v1_tops_1(B_494, A_493) | ~m1_subset_1(B_494, k1_zfmisc_1(u1_struct_0(A_493))) | ~l1_pre_topc(A_493))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.22/2.34  tff(c_4734, plain, (![B_494]: (k2_pre_topc('#skF_3', B_494)=u1_struct_0('#skF_3') | ~v1_tops_1(B_494, '#skF_3') | ~m1_subset_1(B_494, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_4722])).
% 6.22/2.34  tff(c_4741, plain, (![B_495]: (k2_pre_topc('#skF_3', B_495)=k2_struct_0('#skF_3') | ~v1_tops_1(B_495, '#skF_3') | ~m1_subset_1(B_495, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1114, c_4734])).
% 6.22/2.34  tff(c_4747, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1116, c_4741])).
% 6.22/2.34  tff(c_4750, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4283, c_4747])).
% 6.22/2.34  tff(c_4751, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_4740, c_4750])).
% 6.22/2.34  tff(c_4295, plain, (![B_431, A_432]: (v3_pre_topc(B_431, A_432) | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0(A_432))) | ~v1_tdlat_3(A_432) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.22/2.34  tff(c_4307, plain, (![B_431]: (v3_pre_topc(B_431, '#skF_3') | ~m1_subset_1(B_431, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_4295])).
% 6.22/2.34  tff(c_4313, plain, (![B_433]: (v3_pre_topc(B_433, '#skF_3') | ~m1_subset_1(B_433, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_66, c_4307])).
% 6.22/2.34  tff(c_4321, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1116, c_4313])).
% 6.22/2.34  tff(c_5540, plain, (![B_553, A_554]: (v1_tops_1(B_553, A_554) | ~v3_tex_2(B_553, A_554) | ~v3_pre_topc(B_553, A_554) | ~m1_subset_1(B_553, k1_zfmisc_1(u1_struct_0(A_554))) | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554) | v2_struct_0(A_554))), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.22/2.34  tff(c_5561, plain, (![B_553]: (v1_tops_1(B_553, '#skF_3') | ~v3_tex_2(B_553, '#skF_3') | ~v3_pre_topc(B_553, '#skF_3') | ~m1_subset_1(B_553, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_5540])).
% 6.22/2.34  tff(c_5568, plain, (![B_553]: (v1_tops_1(B_553, '#skF_3') | ~v3_tex_2(B_553, '#skF_3') | ~v3_pre_topc(B_553, '#skF_3') | ~m1_subset_1(B_553, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_5561])).
% 6.22/2.34  tff(c_5570, plain, (![B_555]: (v1_tops_1(B_555, '#skF_3') | ~v3_tex_2(B_555, '#skF_3') | ~v3_pre_topc(B_555, '#skF_3') | ~m1_subset_1(B_555, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_5568])).
% 6.22/2.34  tff(c_5576, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1116, c_5570])).
% 6.22/2.34  tff(c_5580, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4321, c_1100, c_5576])).
% 6.22/2.34  tff(c_5582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4751, c_5580])).
% 6.22/2.34  tff(c_5584, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_4721])).
% 6.22/2.34  tff(c_1103, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_72])).
% 6.22/2.34  tff(c_1115, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_1103])).
% 6.22/2.34  tff(c_5596, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5584, c_1115])).
% 6.22/2.34  tff(c_5599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_5596])).
% 6.22/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.22/2.34  
% 6.22/2.34  Inference rules
% 6.22/2.34  ----------------------
% 6.22/2.34  #Ref     : 0
% 6.22/2.34  #Sup     : 1231
% 6.22/2.34  #Fact    : 0
% 6.22/2.34  #Define  : 0
% 6.22/2.34  #Split   : 23
% 6.22/2.34  #Chain   : 0
% 6.22/2.34  #Close   : 0
% 6.22/2.34  
% 6.22/2.34  Ordering : KBO
% 6.22/2.34  
% 6.22/2.34  Simplification rules
% 6.22/2.34  ----------------------
% 6.22/2.34  #Subsume      : 264
% 6.22/2.34  #Demod        : 861
% 6.22/2.34  #Tautology    : 256
% 6.22/2.34  #SimpNegUnit  : 165
% 6.22/2.34  #BackRed      : 20
% 6.22/2.34  
% 6.22/2.34  #Partial instantiations: 0
% 6.22/2.34  #Strategies tried      : 1
% 6.22/2.34  
% 6.22/2.34  Timing (in seconds)
% 6.22/2.34  ----------------------
% 6.22/2.35  Preprocessing        : 0.37
% 6.22/2.35  Parsing              : 0.20
% 6.22/2.35  CNF conversion       : 0.02
% 6.22/2.35  Main loop            : 1.09
% 6.22/2.35  Inferencing          : 0.41
% 6.22/2.35  Reduction            : 0.33
% 6.22/2.35  Demodulation         : 0.21
% 6.22/2.35  BG Simplification    : 0.05
% 6.22/2.35  Subsumption          : 0.21
% 6.22/2.35  Abstraction          : 0.05
% 6.22/2.35  MUC search           : 0.00
% 6.22/2.35  Cooper               : 0.00
% 6.22/2.35  Total                : 1.52
% 6.22/2.35  Index Insertion      : 0.00
% 6.22/2.35  Index Deletion       : 0.00
% 6.22/2.35  Index Matching       : 0.00
% 6.22/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:09 EST 2020

% Result     : Theorem 7.14s
% Output     : CNFRefutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 661 expanded)
%              Number of leaves         :   39 ( 237 expanded)
%              Depth                    :   13
%              Number of atoms          :  306 (1680 expanded)
%              Number of equality atoms :   36 ( 226 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_46,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_151,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_133,axiom,(
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

tff(f_103,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_12] : ~ v1_subset_1(k2_subset_1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_13] :
      ( m1_subset_1(k2_struct_0(A_13),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_773,plain,(
    ! [B_157,A_158] :
      ( v1_subset_1(B_157,A_158)
      | B_157 = A_158
      | ~ m1_subset_1(B_157,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_794,plain,(
    ! [A_162] :
      ( v1_subset_1(k2_struct_0(A_162),u1_struct_0(A_162))
      | u1_struct_0(A_162) = k2_struct_0(A_162)
      | ~ l1_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_16,c_773])).

tff(c_20,plain,(
    ! [A_15] :
      ( ~ v1_subset_1(k2_struct_0(A_15),u1_struct_0(A_15))
      | ~ l1_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_799,plain,(
    ! [A_163] :
      ( u1_struct_0(A_163) = k2_struct_0(A_163)
      | ~ l1_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_794,c_20])).

tff(c_804,plain,(
    ! [A_164] :
      ( u1_struct_0(A_164) = k2_struct_0(A_164)
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_18,c_799])).

tff(c_808,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_804])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_810,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_50])).

tff(c_66,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_81,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_84,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_60])).

tff(c_103,plain,(
    ! [B_53,A_54] :
      ( v1_subset_1(B_53,A_54)
      | B_53 = A_54
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_109,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_103])).

tff(c_116,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_109])).

tff(c_130,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_3'),'#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_20])).

tff(c_134,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_137,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_134])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_137])).

tff(c_142,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_143,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_127,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1('#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_16])).

tff(c_149,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_127])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( v1_subset_1(B_22,A_21)
      | B_22 = A_21
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_152,plain,
    ( v1_subset_1(k2_struct_0('#skF_3'),'#skF_4')
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_149,c_30])).

tff(c_155,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_152])).

tff(c_22,plain,(
    ! [A_16] :
      ( k2_pre_topc(A_16,k2_struct_0(A_16)) = k2_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_165,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_22])).

tff(c_174,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_155,c_165])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_332,plain,(
    ! [B_86,A_87] :
      ( v1_tops_1(B_86,A_87)
      | k2_pre_topc(A_87,B_86) != u1_struct_0(A_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_335,plain,(
    ! [B_86] :
      ( v1_tops_1(B_86,'#skF_3')
      | k2_pre_topc('#skF_3',B_86) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_86,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_332])).

tff(c_347,plain,(
    ! [B_88] :
      ( v1_tops_1(B_88,'#skF_3')
      | k2_pre_topc('#skF_3',B_88) != '#skF_4'
      | ~ m1_subset_1(B_88,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_116,c_335])).

tff(c_351,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_68,c_347])).

tff(c_354,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_351])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_54,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_365,plain,(
    ! [B_90,A_91] :
      ( v2_tex_2(B_90,A_91)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ v1_tdlat_3(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_368,plain,(
    ! [B_90] :
      ( v2_tex_2(B_90,'#skF_3')
      | ~ m1_subset_1(B_90,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_365])).

tff(c_377,plain,(
    ! [B_90] :
      ( v2_tex_2(B_90,'#skF_3')
      | ~ m1_subset_1(B_90,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_368])).

tff(c_381,plain,(
    ! [B_92] :
      ( v2_tex_2(B_92,'#skF_3')
      | ~ m1_subset_1(B_92,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_377])).

tff(c_386,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_381])).

tff(c_711,plain,(
    ! [B_142,A_143] :
      ( v3_tex_2(B_142,A_143)
      | ~ v2_tex_2(B_142,A_143)
      | ~ v1_tops_1(B_142,A_143)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_717,plain,(
    ! [B_142] :
      ( v3_tex_2(B_142,'#skF_3')
      | ~ v2_tex_2(B_142,'#skF_3')
      | ~ v1_tops_1(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_711])).

tff(c_727,plain,(
    ! [B_142] :
      ( v3_tex_2(B_142,'#skF_3')
      | ~ v2_tex_2(B_142,'#skF_3')
      | ~ v1_tops_1(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_717])).

tff(c_731,plain,(
    ! [B_144] :
      ( v3_tex_2(B_144,'#skF_3')
      | ~ v2_tex_2(B_144,'#skF_3')
      | ~ v1_tops_1(B_144,'#skF_3')
      | ~ m1_subset_1(B_144,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_727])).

tff(c_738,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_731])).

tff(c_742,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_386,c_738])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_742])).

tff(c_745,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_822,plain,(
    ! [B_165,A_166] :
      ( v2_tex_2(B_165,A_166)
      | ~ v3_tex_2(B_165,A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_842,plain,(
    ! [A_167] :
      ( v2_tex_2(u1_struct_0(A_167),A_167)
      | ~ v3_tex_2(u1_struct_0(A_167),A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_68,c_822])).

tff(c_845,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_842])).

tff(c_847,plain,
    ( v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_808,c_845])).

tff(c_848,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_847])).

tff(c_885,plain,(
    ! [A_175,B_176] :
      ( k2_pre_topc(A_175,B_176) = u1_struct_0(A_175)
      | ~ v1_tops_1(B_176,A_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_888,plain,(
    ! [B_176] :
      ( k2_pre_topc('#skF_3',B_176) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_176,'#skF_3')
      | ~ m1_subset_1(B_176,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_885])).

tff(c_919,plain,(
    ! [B_180] :
      ( k2_pre_topc('#skF_3',B_180) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_180,'#skF_3')
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_808,c_888])).

tff(c_928,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_919])).

tff(c_930,plain,(
    ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_928])).

tff(c_937,plain,(
    ! [B_182,A_183] :
      ( v1_tops_1(B_182,A_183)
      | k2_pre_topc(A_183,B_182) != u1_struct_0(A_183)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_953,plain,(
    ! [A_185] :
      ( v1_tops_1(u1_struct_0(A_185),A_185)
      | k2_pre_topc(A_185,u1_struct_0(A_185)) != u1_struct_0(A_185)
      | ~ l1_pre_topc(A_185) ) ),
    inference(resolution,[status(thm)],[c_68,c_937])).

tff(c_959,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_953])).

tff(c_962,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_808,c_808,c_959])).

tff(c_963,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_930,c_962])).

tff(c_966,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_963])).

tff(c_970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_966])).

tff(c_972,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_928])).

tff(c_1108,plain,(
    ! [B_211,A_212] :
      ( v2_tex_2(B_211,A_212)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212)
      | ~ v1_tdlat_3(A_212)
      | ~ v2_pre_topc(A_212)
      | v2_struct_0(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1111,plain,(
    ! [B_211] :
      ( v2_tex_2(B_211,'#skF_3')
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_1108])).

tff(c_1120,plain,(
    ! [B_211] :
      ( v2_tex_2(B_211,'#skF_3')
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1111])).

tff(c_1124,plain,(
    ! [B_213] :
      ( v2_tex_2(B_213,'#skF_3')
      | ~ m1_subset_1(B_213,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1120])).

tff(c_1134,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1124])).

tff(c_1715,plain,(
    ! [B_287,A_288] :
      ( v3_tex_2(B_287,A_288)
      | ~ v2_tex_2(B_287,A_288)
      | ~ v1_tops_1(B_287,A_288)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1721,plain,(
    ! [B_287] :
      ( v3_tex_2(B_287,'#skF_3')
      | ~ v2_tex_2(B_287,'#skF_3')
      | ~ v1_tops_1(B_287,'#skF_3')
      | ~ m1_subset_1(B_287,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_1715])).

tff(c_1731,plain,(
    ! [B_287] :
      ( v3_tex_2(B_287,'#skF_3')
      | ~ v2_tex_2(B_287,'#skF_3')
      | ~ v1_tops_1(B_287,'#skF_3')
      | ~ m1_subset_1(B_287,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1721])).

tff(c_1768,plain,(
    ! [B_290] :
      ( v3_tex_2(B_290,'#skF_3')
      | ~ v2_tex_2(B_290,'#skF_3')
      | ~ v1_tops_1(B_290,'#skF_3')
      | ~ m1_subset_1(B_290,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1731])).

tff(c_1775,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1768])).

tff(c_1781,plain,(
    v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_1134,c_1775])).

tff(c_1783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_848,c_1781])).

tff(c_1784,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_847])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_790,plain,(
    ! [C_159,A_160,B_161] :
      ( r2_hidden(C_159,A_160)
      | ~ r2_hidden(C_159,B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1811,plain,(
    ! [A_295,B_296,A_297] :
      ( r2_hidden('#skF_1'(A_295,B_296),A_297)
      | ~ m1_subset_1(A_295,k1_zfmisc_1(A_297))
      | r1_tarski(A_295,B_296) ) ),
    inference(resolution,[status(thm)],[c_6,c_790])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1823,plain,(
    ! [A_298,A_299] :
      ( ~ m1_subset_1(A_298,k1_zfmisc_1(A_299))
      | r1_tarski(A_298,A_299) ) ),
    inference(resolution,[status(thm)],[c_1811,c_4])).

tff(c_1833,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_810,c_1823])).

tff(c_6780,plain,(
    ! [C_852,B_853,A_854] :
      ( C_852 = B_853
      | ~ r1_tarski(B_853,C_852)
      | ~ v2_tex_2(C_852,A_854)
      | ~ m1_subset_1(C_852,k1_zfmisc_1(u1_struct_0(A_854)))
      | ~ v3_tex_2(B_853,A_854)
      | ~ m1_subset_1(B_853,k1_zfmisc_1(u1_struct_0(A_854)))
      | ~ l1_pre_topc(A_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6806,plain,(
    ! [A_854] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_854)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_854)))
      | ~ v3_tex_2('#skF_4',A_854)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_854)))
      | ~ l1_pre_topc(A_854) ) ),
    inference(resolution,[status(thm)],[c_1833,c_6780])).

tff(c_7320,plain,(
    ! [A_919] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_919)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_919)))
      | ~ v3_tex_2('#skF_4',A_919)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_919)))
      | ~ l1_pre_topc(A_919) ) ),
    inference(splitLeft,[status(thm)],[c_6806])).

tff(c_7323,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_7320])).

tff(c_7330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_810,c_808,c_745,c_68,c_1784,c_7323])).

tff(c_7331,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6806])).

tff(c_746,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_809,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_746])).

tff(c_7374,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7331,c_809])).

tff(c_7383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_7374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.14/2.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.27/2.67  
% 7.27/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.27/2.67  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.27/2.67  
% 7.27/2.67  %Foreground sorts:
% 7.27/2.67  
% 7.27/2.67  
% 7.27/2.67  %Background operators:
% 7.27/2.67  
% 7.27/2.67  
% 7.27/2.67  %Foreground operators:
% 7.27/2.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.27/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.27/2.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.27/2.67  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.27/2.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.27/2.67  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.27/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.27/2.67  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.27/2.67  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.27/2.67  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.27/2.67  tff('#skF_3', type, '#skF_3': $i).
% 7.27/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.27/2.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.27/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.27/2.67  tff('#skF_4', type, '#skF_4': $i).
% 7.27/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.27/2.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.27/2.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.27/2.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.27/2.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.27/2.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.27/2.67  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.27/2.67  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.27/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.27/2.67  
% 7.35/2.69  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.35/2.69  tff(f_46, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 7.35/2.69  tff(f_151, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 7.35/2.69  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.35/2.69  tff(f_50, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 7.35/2.69  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 7.35/2.69  tff(f_59, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 7.35/2.69  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 7.35/2.69  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.35/2.69  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 7.35/2.69  tff(f_117, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 7.35/2.69  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 7.35/2.69  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 7.35/2.69  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.35/2.69  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.35/2.69  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.35/2.69  tff(c_14, plain, (![A_12]: (~v1_subset_1(k2_subset_1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.35/2.69  tff(c_67, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 7.35/2.69  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.35/2.69  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.35/2.69  tff(c_16, plain, (![A_13]: (m1_subset_1(k2_struct_0(A_13), k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.35/2.69  tff(c_773, plain, (![B_157, A_158]: (v1_subset_1(B_157, A_158) | B_157=A_158 | ~m1_subset_1(B_157, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.35/2.69  tff(c_794, plain, (![A_162]: (v1_subset_1(k2_struct_0(A_162), u1_struct_0(A_162)) | u1_struct_0(A_162)=k2_struct_0(A_162) | ~l1_struct_0(A_162))), inference(resolution, [status(thm)], [c_16, c_773])).
% 7.35/2.69  tff(c_20, plain, (![A_15]: (~v1_subset_1(k2_struct_0(A_15), u1_struct_0(A_15)) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.35/2.69  tff(c_799, plain, (![A_163]: (u1_struct_0(A_163)=k2_struct_0(A_163) | ~l1_struct_0(A_163))), inference(resolution, [status(thm)], [c_794, c_20])).
% 7.35/2.69  tff(c_804, plain, (![A_164]: (u1_struct_0(A_164)=k2_struct_0(A_164) | ~l1_pre_topc(A_164))), inference(resolution, [status(thm)], [c_18, c_799])).
% 7.35/2.69  tff(c_808, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_804])).
% 7.35/2.69  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.35/2.69  tff(c_810, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_50])).
% 7.35/2.69  tff(c_66, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.35/2.69  tff(c_81, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 7.35/2.69  tff(c_60, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.35/2.69  tff(c_84, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_81, c_60])).
% 7.35/2.69  tff(c_103, plain, (![B_53, A_54]: (v1_subset_1(B_53, A_54) | B_53=A_54 | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.35/2.69  tff(c_109, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_103])).
% 7.35/2.69  tff(c_116, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_81, c_109])).
% 7.35/2.69  tff(c_130, plain, (~v1_subset_1(k2_struct_0('#skF_3'), '#skF_4') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_20])).
% 7.35/2.69  tff(c_134, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_130])).
% 7.35/2.69  tff(c_137, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_134])).
% 7.35/2.69  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_137])).
% 7.35/2.69  tff(c_142, plain, (~v1_subset_1(k2_struct_0('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_130])).
% 7.35/2.69  tff(c_143, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_130])).
% 7.35/2.69  tff(c_127, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1('#skF_4')) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_16])).
% 7.35/2.69  tff(c_149, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_127])).
% 7.35/2.69  tff(c_30, plain, (![B_22, A_21]: (v1_subset_1(B_22, A_21) | B_22=A_21 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.35/2.69  tff(c_152, plain, (v1_subset_1(k2_struct_0('#skF_3'), '#skF_4') | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_149, c_30])).
% 7.35/2.69  tff(c_155, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_142, c_152])).
% 7.35/2.69  tff(c_22, plain, (![A_16]: (k2_pre_topc(A_16, k2_struct_0(A_16))=k2_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.35/2.69  tff(c_165, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_155, c_22])).
% 7.35/2.69  tff(c_174, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_155, c_165])).
% 7.35/2.69  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.35/2.69  tff(c_68, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 7.35/2.69  tff(c_332, plain, (![B_86, A_87]: (v1_tops_1(B_86, A_87) | k2_pre_topc(A_87, B_86)!=u1_struct_0(A_87) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.35/2.69  tff(c_335, plain, (![B_86]: (v1_tops_1(B_86, '#skF_3') | k2_pre_topc('#skF_3', B_86)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_86, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_332])).
% 7.35/2.69  tff(c_347, plain, (![B_88]: (v1_tops_1(B_88, '#skF_3') | k2_pre_topc('#skF_3', B_88)!='#skF_4' | ~m1_subset_1(B_88, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_116, c_335])).
% 7.35/2.69  tff(c_351, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_68, c_347])).
% 7.35/2.69  tff(c_354, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_351])).
% 7.35/2.69  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.35/2.69  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.35/2.69  tff(c_54, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.35/2.69  tff(c_365, plain, (![B_90, A_91]: (v2_tex_2(B_90, A_91) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~v1_tdlat_3(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.35/2.69  tff(c_368, plain, (![B_90]: (v2_tex_2(B_90, '#skF_3') | ~m1_subset_1(B_90, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_365])).
% 7.35/2.69  tff(c_377, plain, (![B_90]: (v2_tex_2(B_90, '#skF_3') | ~m1_subset_1(B_90, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_368])).
% 7.35/2.69  tff(c_381, plain, (![B_92]: (v2_tex_2(B_92, '#skF_3') | ~m1_subset_1(B_92, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_377])).
% 7.35/2.69  tff(c_386, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_381])).
% 7.35/2.69  tff(c_711, plain, (![B_142, A_143]: (v3_tex_2(B_142, A_143) | ~v2_tex_2(B_142, A_143) | ~v1_tops_1(B_142, A_143) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.35/2.69  tff(c_717, plain, (![B_142]: (v3_tex_2(B_142, '#skF_3') | ~v2_tex_2(B_142, '#skF_3') | ~v1_tops_1(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_711])).
% 7.35/2.69  tff(c_727, plain, (![B_142]: (v3_tex_2(B_142, '#skF_3') | ~v2_tex_2(B_142, '#skF_3') | ~v1_tops_1(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_717])).
% 7.35/2.69  tff(c_731, plain, (![B_144]: (v3_tex_2(B_144, '#skF_3') | ~v2_tex_2(B_144, '#skF_3') | ~v1_tops_1(B_144, '#skF_3') | ~m1_subset_1(B_144, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_727])).
% 7.35/2.69  tff(c_738, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_731])).
% 7.35/2.69  tff(c_742, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_386, c_738])).
% 7.35/2.69  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_742])).
% 7.35/2.69  tff(c_745, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 7.35/2.69  tff(c_822, plain, (![B_165, A_166]: (v2_tex_2(B_165, A_166) | ~v3_tex_2(B_165, A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.35/2.69  tff(c_842, plain, (![A_167]: (v2_tex_2(u1_struct_0(A_167), A_167) | ~v3_tex_2(u1_struct_0(A_167), A_167) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_68, c_822])).
% 7.35/2.69  tff(c_845, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_808, c_842])).
% 7.35/2.69  tff(c_847, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_808, c_845])).
% 7.35/2.69  tff(c_848, plain, (~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_847])).
% 7.35/2.69  tff(c_885, plain, (![A_175, B_176]: (k2_pre_topc(A_175, B_176)=u1_struct_0(A_175) | ~v1_tops_1(B_176, A_175) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.35/2.69  tff(c_888, plain, (![B_176]: (k2_pre_topc('#skF_3', B_176)=u1_struct_0('#skF_3') | ~v1_tops_1(B_176, '#skF_3') | ~m1_subset_1(B_176, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_885])).
% 7.35/2.69  tff(c_919, plain, (![B_180]: (k2_pre_topc('#skF_3', B_180)=k2_struct_0('#skF_3') | ~v1_tops_1(B_180, '#skF_3') | ~m1_subset_1(B_180, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_808, c_888])).
% 7.35/2.69  tff(c_928, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_68, c_919])).
% 7.35/2.69  tff(c_930, plain, (~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_928])).
% 7.35/2.69  tff(c_937, plain, (![B_182, A_183]: (v1_tops_1(B_182, A_183) | k2_pre_topc(A_183, B_182)!=u1_struct_0(A_183) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.35/2.69  tff(c_953, plain, (![A_185]: (v1_tops_1(u1_struct_0(A_185), A_185) | k2_pre_topc(A_185, u1_struct_0(A_185))!=u1_struct_0(A_185) | ~l1_pre_topc(A_185))), inference(resolution, [status(thm)], [c_68, c_937])).
% 7.35/2.69  tff(c_959, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_808, c_953])).
% 7.35/2.69  tff(c_962, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_808, c_808, c_959])).
% 7.35/2.69  tff(c_963, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_930, c_962])).
% 7.35/2.69  tff(c_966, plain, (~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_963])).
% 7.35/2.69  tff(c_970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_966])).
% 7.35/2.69  tff(c_972, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_928])).
% 7.35/2.69  tff(c_1108, plain, (![B_211, A_212]: (v2_tex_2(B_211, A_212) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212) | ~v1_tdlat_3(A_212) | ~v2_pre_topc(A_212) | v2_struct_0(A_212))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.35/2.69  tff(c_1111, plain, (![B_211]: (v2_tex_2(B_211, '#skF_3') | ~m1_subset_1(B_211, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_1108])).
% 7.35/2.69  tff(c_1120, plain, (![B_211]: (v2_tex_2(B_211, '#skF_3') | ~m1_subset_1(B_211, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1111])).
% 7.35/2.69  tff(c_1124, plain, (![B_213]: (v2_tex_2(B_213, '#skF_3') | ~m1_subset_1(B_213, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_1120])).
% 7.35/2.69  tff(c_1134, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_68, c_1124])).
% 7.35/2.69  tff(c_1715, plain, (![B_287, A_288]: (v3_tex_2(B_287, A_288) | ~v2_tex_2(B_287, A_288) | ~v1_tops_1(B_287, A_288) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.35/2.69  tff(c_1721, plain, (![B_287]: (v3_tex_2(B_287, '#skF_3') | ~v2_tex_2(B_287, '#skF_3') | ~v1_tops_1(B_287, '#skF_3') | ~m1_subset_1(B_287, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_1715])).
% 7.35/2.69  tff(c_1731, plain, (![B_287]: (v3_tex_2(B_287, '#skF_3') | ~v2_tex_2(B_287, '#skF_3') | ~v1_tops_1(B_287, '#skF_3') | ~m1_subset_1(B_287, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1721])).
% 7.35/2.69  tff(c_1768, plain, (![B_290]: (v3_tex_2(B_290, '#skF_3') | ~v2_tex_2(B_290, '#skF_3') | ~v1_tops_1(B_290, '#skF_3') | ~m1_subset_1(B_290, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_1731])).
% 7.35/2.69  tff(c_1775, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_68, c_1768])).
% 7.35/2.69  tff(c_1781, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_972, c_1134, c_1775])).
% 7.35/2.69  tff(c_1783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_848, c_1781])).
% 7.35/2.69  tff(c_1784, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_847])).
% 7.35/2.69  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.35/2.69  tff(c_790, plain, (![C_159, A_160, B_161]: (r2_hidden(C_159, A_160) | ~r2_hidden(C_159, B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.35/2.69  tff(c_1811, plain, (![A_295, B_296, A_297]: (r2_hidden('#skF_1'(A_295, B_296), A_297) | ~m1_subset_1(A_295, k1_zfmisc_1(A_297)) | r1_tarski(A_295, B_296))), inference(resolution, [status(thm)], [c_6, c_790])).
% 7.35/2.69  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.35/2.69  tff(c_1823, plain, (![A_298, A_299]: (~m1_subset_1(A_298, k1_zfmisc_1(A_299)) | r1_tarski(A_298, A_299))), inference(resolution, [status(thm)], [c_1811, c_4])).
% 7.35/2.69  tff(c_1833, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_810, c_1823])).
% 7.35/2.69  tff(c_6780, plain, (![C_852, B_853, A_854]: (C_852=B_853 | ~r1_tarski(B_853, C_852) | ~v2_tex_2(C_852, A_854) | ~m1_subset_1(C_852, k1_zfmisc_1(u1_struct_0(A_854))) | ~v3_tex_2(B_853, A_854) | ~m1_subset_1(B_853, k1_zfmisc_1(u1_struct_0(A_854))) | ~l1_pre_topc(A_854))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.35/2.69  tff(c_6806, plain, (![A_854]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_854) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_854))) | ~v3_tex_2('#skF_4', A_854) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_854))) | ~l1_pre_topc(A_854))), inference(resolution, [status(thm)], [c_1833, c_6780])).
% 7.35/2.69  tff(c_7320, plain, (![A_919]: (~v2_tex_2(k2_struct_0('#skF_3'), A_919) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_919))) | ~v3_tex_2('#skF_4', A_919) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_919))) | ~l1_pre_topc(A_919))), inference(splitLeft, [status(thm)], [c_6806])).
% 7.35/2.69  tff(c_7323, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_808, c_7320])).
% 7.35/2.69  tff(c_7330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_810, c_808, c_745, c_68, c_1784, c_7323])).
% 7.35/2.69  tff(c_7331, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_6806])).
% 7.35/2.69  tff(c_746, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 7.35/2.69  tff(c_809, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_746])).
% 7.35/2.69  tff(c_7374, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7331, c_809])).
% 7.35/2.69  tff(c_7383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_7374])).
% 7.35/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.35/2.69  
% 7.35/2.69  Inference rules
% 7.35/2.69  ----------------------
% 7.35/2.69  #Ref     : 0
% 7.35/2.69  #Sup     : 1632
% 7.35/2.69  #Fact    : 0
% 7.35/2.69  #Define  : 0
% 7.35/2.69  #Split   : 20
% 7.35/2.69  #Chain   : 0
% 7.35/2.69  #Close   : 0
% 7.35/2.69  
% 7.35/2.69  Ordering : KBO
% 7.35/2.69  
% 7.35/2.69  Simplification rules
% 7.35/2.69  ----------------------
% 7.35/2.69  #Subsume      : 628
% 7.35/2.69  #Demod        : 1168
% 7.35/2.69  #Tautology    : 274
% 7.35/2.69  #SimpNegUnit  : 48
% 7.35/2.69  #BackRed      : 177
% 7.35/2.69  
% 7.35/2.69  #Partial instantiations: 0
% 7.35/2.69  #Strategies tried      : 1
% 7.35/2.69  
% 7.35/2.69  Timing (in seconds)
% 7.35/2.69  ----------------------
% 7.35/2.70  Preprocessing        : 0.31
% 7.35/2.70  Parsing              : 0.16
% 7.35/2.70  CNF conversion       : 0.03
% 7.35/2.70  Main loop            : 1.51
% 7.35/2.70  Inferencing          : 0.47
% 7.35/2.70  Reduction            : 0.44
% 7.35/2.70  Demodulation         : 0.30
% 7.35/2.70  BG Simplification    : 0.05
% 7.35/2.70  Subsumption          : 0.45
% 7.35/2.70  Abstraction          : 0.06
% 7.35/2.70  MUC search           : 0.00
% 7.35/2.70  Cooper               : 0.00
% 7.35/2.70  Total                : 1.87
% 7.35/2.70  Index Insertion      : 0.00
% 7.35/2.70  Index Deletion       : 0.00
% 7.35/2.70  Index Matching       : 0.00
% 7.35/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------

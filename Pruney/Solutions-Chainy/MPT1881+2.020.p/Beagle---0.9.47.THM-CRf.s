%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:08 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :  209 (1555 expanded)
%              Number of leaves         :   41 ( 542 expanded)
%              Depth                    :   15
%              Number of atoms          :  497 (4030 expanded)
%              Number of equality atoms :   82 ( 606 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_46,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_168,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_80,axiom,(
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

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_150,axiom,(
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

tff(f_120,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_12] : ~ v1_subset_1(k2_subset_1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

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

tff(c_913,plain,(
    ! [B_174,A_175] :
      ( v1_subset_1(B_174,A_175)
      | B_174 = A_175
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_946,plain,(
    ! [A_182] :
      ( v1_subset_1(k2_struct_0(A_182),u1_struct_0(A_182))
      | u1_struct_0(A_182) = k2_struct_0(A_182)
      | ~ l1_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_16,c_913])).

tff(c_20,plain,(
    ! [A_15] :
      ( ~ v1_subset_1(k2_struct_0(A_15),u1_struct_0(A_15))
      | ~ l1_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_951,plain,(
    ! [A_183] :
      ( u1_struct_0(A_183) = k2_struct_0(A_183)
      | ~ l1_struct_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_946,c_20])).

tff(c_956,plain,(
    ! [A_184] :
      ( u1_struct_0(A_184) = k2_struct_0(A_184)
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_18,c_951])).

tff(c_960,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_956])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_978,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_54])).

tff(c_70,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_85,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_87,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_64])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_99,plain,(
    ! [B_56,A_57] :
      ( v1_subset_1(B_56,A_57)
      | B_56 = A_57
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_105,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_99])).

tff(c_112,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_105])).

tff(c_126,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_3'),'#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_20])).

tff(c_130,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_133,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_130])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_133])).

tff(c_138,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_139,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_123,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1('#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_16])).

tff(c_145,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_123])).

tff(c_34,plain,(
    ! [B_25,A_24] :
      ( v1_subset_1(B_25,A_24)
      | B_25 = A_24
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_148,plain,
    ( v1_subset_1(k2_struct_0('#skF_3'),'#skF_4')
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_145,c_34])).

tff(c_151,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_148])).

tff(c_22,plain,(
    ! [A_16] :
      ( v4_pre_topc(k2_struct_0(A_16),A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_161,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_22])).

tff(c_170,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_161])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_289,plain,(
    ! [A_81,B_82] :
      ( k2_pre_topc(A_81,B_82) = B_82
      | ~ v4_pre_topc(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_292,plain,(
    ! [B_82] :
      ( k2_pre_topc('#skF_3',B_82) = B_82
      | ~ v4_pre_topc(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_289])).

tff(c_304,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_3',B_83) = B_83
      | ~ v4_pre_topc(B_83,'#skF_3')
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_292])).

tff(c_308,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_304])).

tff(c_311,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_308])).

tff(c_322,plain,(
    ! [B_85,A_86] :
      ( v1_tops_1(B_85,A_86)
      | k2_pre_topc(A_86,B_85) != u1_struct_0(A_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_325,plain,(
    ! [B_85] :
      ( v1_tops_1(B_85,'#skF_3')
      | k2_pre_topc('#skF_3',B_85) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_85,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_322])).

tff(c_337,plain,(
    ! [B_87] :
      ( v1_tops_1(B_87,'#skF_3')
      | k2_pre_topc('#skF_3',B_87) != '#skF_4'
      | ~ m1_subset_1(B_87,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_112,c_325])).

tff(c_341,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_337])).

tff(c_344,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_341])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_58,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_457,plain,(
    ! [B_101,A_102] :
      ( v2_tex_2(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v1_tdlat_3(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_460,plain,(
    ! [B_101] :
      ( v2_tex_2(B_101,'#skF_3')
      | ~ m1_subset_1(B_101,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_457])).

tff(c_469,plain,(
    ! [B_101] :
      ( v2_tex_2(B_101,'#skF_3')
      | ~ m1_subset_1(B_101,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_460])).

tff(c_473,plain,(
    ! [B_103] :
      ( v2_tex_2(B_103,'#skF_3')
      | ~ m1_subset_1(B_103,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_469])).

tff(c_478,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_473])).

tff(c_828,plain,(
    ! [B_157,A_158] :
      ( v3_tex_2(B_157,A_158)
      | ~ v2_tex_2(B_157,A_158)
      | ~ v1_tops_1(B_157,A_158)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_834,plain,(
    ! [B_157] :
      ( v3_tex_2(B_157,'#skF_3')
      | ~ v2_tex_2(B_157,'#skF_3')
      | ~ v1_tops_1(B_157,'#skF_3')
      | ~ m1_subset_1(B_157,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_828])).

tff(c_844,plain,(
    ! [B_157] :
      ( v3_tex_2(B_157,'#skF_3')
      | ~ v2_tex_2(B_157,'#skF_3')
      | ~ v1_tops_1(B_157,'#skF_3')
      | ~ m1_subset_1(B_157,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_834])).

tff(c_878,plain,(
    ! [B_161] :
      ( v3_tex_2(B_161,'#skF_3')
      | ~ v2_tex_2(B_161,'#skF_3')
      | ~ v1_tops_1(B_161,'#skF_3')
      | ~ m1_subset_1(B_161,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_844])).

tff(c_885,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_878])).

tff(c_889,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_478,c_885])).

tff(c_891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_889])).

tff(c_892,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_961,plain,(
    ! [B_185,A_186] :
      ( v2_tex_2(B_185,A_186)
      | ~ v3_tex_2(B_185,A_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1000,plain,(
    ! [A_187] :
      ( v2_tex_2(u1_struct_0(A_187),A_187)
      | ~ v3_tex_2(u1_struct_0(A_187),A_187)
      | ~ l1_pre_topc(A_187) ) ),
    inference(resolution,[status(thm)],[c_72,c_961])).

tff(c_1003,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_1000])).

tff(c_1005,plain,
    ( v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_960,c_1003])).

tff(c_1006,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1005])).

tff(c_1031,plain,(
    ! [A_192,B_193] :
      ( k2_pre_topc(A_192,B_193) = B_193
      | ~ v4_pre_topc(B_193,A_192)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1034,plain,(
    ! [B_193] :
      ( k2_pre_topc('#skF_3',B_193) = B_193
      | ~ v4_pre_topc(B_193,'#skF_3')
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_1031])).

tff(c_1065,plain,(
    ! [B_197] :
      ( k2_pre_topc('#skF_3',B_197) = B_197
      | ~ v4_pre_topc(B_197,'#skF_3')
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1034])).

tff(c_1074,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1065])).

tff(c_1076,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1074])).

tff(c_1079,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1076])).

tff(c_1083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1079])).

tff(c_1084,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1074])).

tff(c_1086,plain,(
    ! [B_198,A_199] :
      ( v1_tops_1(B_198,A_199)
      | k2_pre_topc(A_199,B_198) != u1_struct_0(A_199)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1089,plain,(
    ! [B_198] :
      ( v1_tops_1(B_198,'#skF_3')
      | k2_pre_topc('#skF_3',B_198) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_1086])).

tff(c_1112,plain,(
    ! [B_202] :
      ( v1_tops_1(B_202,'#skF_3')
      | k2_pre_topc('#skF_3',B_202) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_202,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_960,c_1089])).

tff(c_1119,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1112])).

tff(c_1123,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1119])).

tff(c_1351,plain,(
    ! [B_239,A_240] :
      ( v2_tex_2(B_239,A_240)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240)
      | ~ v1_tdlat_3(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1354,plain,(
    ! [B_239] :
      ( v2_tex_2(B_239,'#skF_3')
      | ~ m1_subset_1(B_239,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_1351])).

tff(c_1363,plain,(
    ! [B_239] :
      ( v2_tex_2(B_239,'#skF_3')
      | ~ m1_subset_1(B_239,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1354])).

tff(c_1367,plain,(
    ! [B_241] :
      ( v2_tex_2(B_241,'#skF_3')
      | ~ m1_subset_1(B_241,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1363])).

tff(c_1377,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1367])).

tff(c_2031,plain,(
    ! [B_312,A_313] :
      ( v3_tex_2(B_312,A_313)
      | ~ v2_tex_2(B_312,A_313)
      | ~ v1_tops_1(B_312,A_313)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2037,plain,(
    ! [B_312] :
      ( v3_tex_2(B_312,'#skF_3')
      | ~ v2_tex_2(B_312,'#skF_3')
      | ~ v1_tops_1(B_312,'#skF_3')
      | ~ m1_subset_1(B_312,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_2031])).

tff(c_2047,plain,(
    ! [B_312] :
      ( v3_tex_2(B_312,'#skF_3')
      | ~ v2_tex_2(B_312,'#skF_3')
      | ~ v1_tops_1(B_312,'#skF_3')
      | ~ m1_subset_1(B_312,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_2037])).

tff(c_2051,plain,(
    ! [B_314] :
      ( v3_tex_2(B_314,'#skF_3')
      | ~ v2_tex_2(B_314,'#skF_3')
      | ~ v1_tops_1(B_314,'#skF_3')
      | ~ m1_subset_1(B_314,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2047])).

tff(c_2061,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2051])).

tff(c_2068,plain,(
    v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1377,c_2061])).

tff(c_2070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1006,c_2068])).

tff(c_2071,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1005])).

tff(c_2125,plain,(
    ! [A_323,B_324] :
      ( k2_pre_topc(A_323,B_324) = B_324
      | ~ v4_pre_topc(B_324,A_323)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2128,plain,(
    ! [B_324] :
      ( k2_pre_topc('#skF_3',B_324) = B_324
      | ~ v4_pre_topc(B_324,'#skF_3')
      | ~ m1_subset_1(B_324,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_2125])).

tff(c_2156,plain,(
    ! [B_326] :
      ( k2_pre_topc('#skF_3',B_326) = B_326
      | ~ v4_pre_topc(B_326,'#skF_3')
      | ~ m1_subset_1(B_326,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2128])).

tff(c_2164,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_978,c_2156])).

tff(c_2170,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2164])).

tff(c_2173,plain,(
    ! [B_327,A_328] :
      ( v1_tops_1(B_327,A_328)
      | k2_pre_topc(A_328,B_327) != u1_struct_0(A_328)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2176,plain,(
    ! [B_327] :
      ( v1_tops_1(B_327,'#skF_3')
      | k2_pre_topc('#skF_3',B_327) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_327,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_2173])).

tff(c_2194,plain,(
    ! [B_330] :
      ( v1_tops_1(B_330,'#skF_3')
      | k2_pre_topc('#skF_3',B_330) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_330,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_960,c_2176])).

tff(c_2202,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_978,c_2194])).

tff(c_2206,plain,(
    k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2202])).

tff(c_2250,plain,(
    ! [A_338,B_339] :
      ( k2_pre_topc(A_338,B_339) = u1_struct_0(A_338)
      | ~ v1_tops_1(B_339,A_338)
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ l1_pre_topc(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2253,plain,(
    ! [B_339] :
      ( k2_pre_topc('#skF_3',B_339) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_339,'#skF_3')
      | ~ m1_subset_1(B_339,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_2250])).

tff(c_2291,plain,(
    ! [B_344] :
      ( k2_pre_topc('#skF_3',B_344) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_344,'#skF_3')
      | ~ m1_subset_1(B_344,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_960,c_2253])).

tff(c_2294,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_978,c_2291])).

tff(c_2301,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2206,c_2294])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_930,plain,(
    ! [C_176,A_177,B_178] :
      ( r2_hidden(C_176,A_177)
      | ~ r2_hidden(C_176,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2094,plain,(
    ! [A_317,B_318,A_319] :
      ( r2_hidden('#skF_1'(A_317,B_318),A_319)
      | ~ m1_subset_1(A_317,k1_zfmisc_1(A_319))
      | r1_tarski(A_317,B_318) ) ),
    inference(resolution,[status(thm)],[c_6,c_930])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2106,plain,(
    ! [A_320,A_321] :
      ( ~ m1_subset_1(A_320,k1_zfmisc_1(A_321))
      | r1_tarski(A_320,A_321) ) ),
    inference(resolution,[status(thm)],[c_2094,c_4])).

tff(c_2116,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_978,c_2106])).

tff(c_4734,plain,(
    ! [C_612,B_613,A_614] :
      ( C_612 = B_613
      | ~ r1_tarski(B_613,C_612)
      | ~ v2_tex_2(C_612,A_614)
      | ~ m1_subset_1(C_612,k1_zfmisc_1(u1_struct_0(A_614)))
      | ~ v3_tex_2(B_613,A_614)
      | ~ m1_subset_1(B_613,k1_zfmisc_1(u1_struct_0(A_614)))
      | ~ l1_pre_topc(A_614) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4760,plain,(
    ! [A_614] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_614)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_614)))
      | ~ v3_tex_2('#skF_4',A_614)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_614)))
      | ~ l1_pre_topc(A_614) ) ),
    inference(resolution,[status(thm)],[c_2116,c_4734])).

tff(c_5123,plain,(
    ! [A_653] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_653)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_653)))
      | ~ v3_tex_2('#skF_4',A_653)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_653)))
      | ~ l1_pre_topc(A_653) ) ),
    inference(splitLeft,[status(thm)],[c_4760])).

tff(c_5126,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_5123])).

tff(c_5133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_978,c_960,c_892,c_72,c_2071,c_5126])).

tff(c_5134,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4760])).

tff(c_2140,plain,(
    ! [A_325] :
      ( k2_pre_topc(A_325,u1_struct_0(A_325)) = u1_struct_0(A_325)
      | ~ v4_pre_topc(u1_struct_0(A_325),A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(resolution,[status(thm)],[c_72,c_2125])).

tff(c_2143,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_2140])).

tff(c_2145,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_960,c_960,c_2143])).

tff(c_2146,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2145])).

tff(c_2149,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2146])).

tff(c_2153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_2149])).

tff(c_2154,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2145])).

tff(c_2188,plain,(
    ! [A_329] :
      ( v1_tops_1(u1_struct_0(A_329),A_329)
      | k2_pre_topc(A_329,u1_struct_0(A_329)) != u1_struct_0(A_329)
      | ~ l1_pre_topc(A_329) ) ),
    inference(resolution,[status(thm)],[c_72,c_2173])).

tff(c_2191,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_2188])).

tff(c_2193,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2154,c_960,c_960,c_2191])).

tff(c_5182,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5134,c_2193])).

tff(c_5194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2301,c_5182])).

tff(c_5196,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2202])).

tff(c_5330,plain,(
    ! [B_671,A_672] :
      ( v4_pre_topc(B_671,A_672)
      | k2_pre_topc(A_672,B_671) != B_671
      | ~ v2_pre_topc(A_672)
      | ~ m1_subset_1(B_671,k1_zfmisc_1(u1_struct_0(A_672)))
      | ~ l1_pre_topc(A_672) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5333,plain,(
    ! [B_671] :
      ( v4_pre_topc(B_671,'#skF_3')
      | k2_pre_topc('#skF_3',B_671) != B_671
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(B_671,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_5330])).

tff(c_5345,plain,(
    ! [B_673] :
      ( v4_pre_topc(B_673,'#skF_3')
      | k2_pre_topc('#skF_3',B_673) != B_673
      | ~ m1_subset_1(B_673,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_5333])).

tff(c_5348,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_978,c_5345])).

tff(c_5354,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5196,c_5348])).

tff(c_5355,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2170,c_5354])).

tff(c_6136,plain,(
    ! [C_772,B_773,A_774] :
      ( C_772 = B_773
      | ~ r1_tarski(B_773,C_772)
      | ~ v2_tex_2(C_772,A_774)
      | ~ m1_subset_1(C_772,k1_zfmisc_1(u1_struct_0(A_774)))
      | ~ v3_tex_2(B_773,A_774)
      | ~ m1_subset_1(B_773,k1_zfmisc_1(u1_struct_0(A_774)))
      | ~ l1_pre_topc(A_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6152,plain,(
    ! [A_774] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_774)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_774)))
      | ~ v3_tex_2('#skF_4',A_774)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_774)))
      | ~ l1_pre_topc(A_774) ) ),
    inference(resolution,[status(thm)],[c_2116,c_6136])).

tff(c_6637,plain,(
    ! [A_824] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_824)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_824)))
      | ~ v3_tex_2('#skF_4',A_824)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_824)))
      | ~ l1_pre_topc(A_824) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5355,c_6152])).

tff(c_6640,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_6637])).

tff(c_6647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_978,c_960,c_892,c_72,c_2071,c_6640])).

tff(c_6648,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2164])).

tff(c_6688,plain,(
    ! [A_827,B_828] :
      ( k2_pre_topc(A_827,B_828) = u1_struct_0(A_827)
      | ~ v1_tops_1(B_828,A_827)
      | ~ m1_subset_1(B_828,k1_zfmisc_1(u1_struct_0(A_827)))
      | ~ l1_pre_topc(A_827) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6691,plain,(
    ! [B_828] :
      ( k2_pre_topc('#skF_3',B_828) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_828,'#skF_3')
      | ~ m1_subset_1(B_828,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_6688])).

tff(c_6709,plain,(
    ! [B_830] :
      ( k2_pre_topc('#skF_3',B_830) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_830,'#skF_3')
      | ~ m1_subset_1(B_830,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_960,c_6691])).

tff(c_6712,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_978,c_6709])).

tff(c_6718,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6648,c_6712])).

tff(c_6721,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6718])).

tff(c_6749,plain,(
    ! [B_839,A_840] :
      ( v1_tops_1(B_839,A_840)
      | k2_pre_topc(A_840,B_839) != u1_struct_0(A_840)
      | ~ m1_subset_1(B_839,k1_zfmisc_1(u1_struct_0(A_840)))
      | ~ l1_pre_topc(A_840) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6752,plain,(
    ! [B_839] :
      ( v1_tops_1(B_839,'#skF_3')
      | k2_pre_topc('#skF_3',B_839) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_839,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_6749])).

tff(c_6809,plain,(
    ! [B_845] :
      ( v1_tops_1(B_845,'#skF_3')
      | k2_pre_topc('#skF_3',B_845) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_845,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_960,c_6752])).

tff(c_6812,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_978,c_6809])).

tff(c_6818,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6648,c_6812])).

tff(c_6819,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_6721,c_6818])).

tff(c_7703,plain,(
    ! [C_954,B_955,A_956] :
      ( C_954 = B_955
      | ~ r1_tarski(B_955,C_954)
      | ~ v2_tex_2(C_954,A_956)
      | ~ m1_subset_1(C_954,k1_zfmisc_1(u1_struct_0(A_956)))
      | ~ v3_tex_2(B_955,A_956)
      | ~ m1_subset_1(B_955,k1_zfmisc_1(u1_struct_0(A_956)))
      | ~ l1_pre_topc(A_956) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7719,plain,(
    ! [A_956] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_956)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_956)))
      | ~ v3_tex_2('#skF_4',A_956)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_956)))
      | ~ l1_pre_topc(A_956) ) ),
    inference(resolution,[status(thm)],[c_2116,c_7703])).

tff(c_8263,plain,(
    ! [A_1023] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_1023)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_1023)))
      | ~ v3_tex_2('#skF_4',A_1023)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_1023)))
      | ~ l1_pre_topc(A_1023) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6819,c_7719])).

tff(c_8266,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_8263])).

tff(c_8273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_978,c_960,c_892,c_72,c_2071,c_8266])).

tff(c_8274,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6718])).

tff(c_895,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_64])).

tff(c_977,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_895])).

tff(c_8285,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8274,c_977])).

tff(c_8294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_8285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.58/2.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/2.77  
% 7.72/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/2.77  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.72/2.77  
% 7.72/2.77  %Foreground sorts:
% 7.72/2.77  
% 7.72/2.77  
% 7.72/2.77  %Background operators:
% 7.72/2.77  
% 7.72/2.77  
% 7.72/2.77  %Foreground operators:
% 7.72/2.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.72/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.72/2.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.72/2.77  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.72/2.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.72/2.77  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.72/2.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.72/2.77  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.72/2.77  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.72/2.77  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.72/2.77  tff('#skF_3', type, '#skF_3': $i).
% 7.72/2.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.72/2.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.72/2.77  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.72/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.72/2.77  tff('#skF_4', type, '#skF_4': $i).
% 7.72/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.72/2.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.72/2.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.72/2.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.72/2.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.72/2.77  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.72/2.77  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.72/2.77  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.72/2.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.72/2.77  
% 7.72/2.80  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.72/2.80  tff(f_46, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 7.72/2.80  tff(f_168, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 7.72/2.80  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.72/2.80  tff(f_50, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 7.72/2.80  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 7.72/2.80  tff(f_59, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 7.72/2.80  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 7.72/2.80  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.72/2.80  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.72/2.80  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 7.72/2.80  tff(f_134, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 7.72/2.80  tff(f_150, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 7.72/2.80  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 7.72/2.80  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.72/2.80  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.72/2.80  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.72/2.80  tff(c_14, plain, (![A_12]: (~v1_subset_1(k2_subset_1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.72/2.80  tff(c_71, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 7.72/2.80  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.72/2.80  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.72/2.80  tff(c_16, plain, (![A_13]: (m1_subset_1(k2_struct_0(A_13), k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.72/2.80  tff(c_913, plain, (![B_174, A_175]: (v1_subset_1(B_174, A_175) | B_174=A_175 | ~m1_subset_1(B_174, k1_zfmisc_1(A_175)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.72/2.80  tff(c_946, plain, (![A_182]: (v1_subset_1(k2_struct_0(A_182), u1_struct_0(A_182)) | u1_struct_0(A_182)=k2_struct_0(A_182) | ~l1_struct_0(A_182))), inference(resolution, [status(thm)], [c_16, c_913])).
% 7.72/2.80  tff(c_20, plain, (![A_15]: (~v1_subset_1(k2_struct_0(A_15), u1_struct_0(A_15)) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.72/2.80  tff(c_951, plain, (![A_183]: (u1_struct_0(A_183)=k2_struct_0(A_183) | ~l1_struct_0(A_183))), inference(resolution, [status(thm)], [c_946, c_20])).
% 7.72/2.80  tff(c_956, plain, (![A_184]: (u1_struct_0(A_184)=k2_struct_0(A_184) | ~l1_pre_topc(A_184))), inference(resolution, [status(thm)], [c_18, c_951])).
% 7.72/2.80  tff(c_960, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_956])).
% 7.72/2.80  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.72/2.80  tff(c_978, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_960, c_54])).
% 7.72/2.80  tff(c_70, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.72/2.80  tff(c_85, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 7.72/2.80  tff(c_64, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.72/2.80  tff(c_87, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_85, c_64])).
% 7.72/2.80  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.72/2.80  tff(c_99, plain, (![B_56, A_57]: (v1_subset_1(B_56, A_57) | B_56=A_57 | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.72/2.80  tff(c_105, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_54, c_99])).
% 7.72/2.80  tff(c_112, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_85, c_105])).
% 7.72/2.80  tff(c_126, plain, (~v1_subset_1(k2_struct_0('#skF_3'), '#skF_4') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_20])).
% 7.72/2.80  tff(c_130, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_126])).
% 7.72/2.80  tff(c_133, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_130])).
% 7.72/2.80  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_133])).
% 7.72/2.80  tff(c_138, plain, (~v1_subset_1(k2_struct_0('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_126])).
% 7.72/2.80  tff(c_139, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_126])).
% 7.72/2.80  tff(c_123, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1('#skF_4')) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_16])).
% 7.72/2.80  tff(c_145, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_123])).
% 7.72/2.80  tff(c_34, plain, (![B_25, A_24]: (v1_subset_1(B_25, A_24) | B_25=A_24 | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.72/2.80  tff(c_148, plain, (v1_subset_1(k2_struct_0('#skF_3'), '#skF_4') | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_145, c_34])).
% 7.72/2.80  tff(c_151, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_138, c_148])).
% 7.72/2.80  tff(c_22, plain, (![A_16]: (v4_pre_topc(k2_struct_0(A_16), A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.72/2.80  tff(c_161, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_151, c_22])).
% 7.72/2.80  tff(c_170, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_161])).
% 7.72/2.80  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.72/2.80  tff(c_72, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 7.72/2.80  tff(c_289, plain, (![A_81, B_82]: (k2_pre_topc(A_81, B_82)=B_82 | ~v4_pre_topc(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.72/2.80  tff(c_292, plain, (![B_82]: (k2_pre_topc('#skF_3', B_82)=B_82 | ~v4_pre_topc(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_289])).
% 7.72/2.80  tff(c_304, plain, (![B_83]: (k2_pre_topc('#skF_3', B_83)=B_83 | ~v4_pre_topc(B_83, '#skF_3') | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_292])).
% 7.72/2.80  tff(c_308, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_304])).
% 7.72/2.80  tff(c_311, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_308])).
% 7.72/2.80  tff(c_322, plain, (![B_85, A_86]: (v1_tops_1(B_85, A_86) | k2_pre_topc(A_86, B_85)!=u1_struct_0(A_86) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.72/2.80  tff(c_325, plain, (![B_85]: (v1_tops_1(B_85, '#skF_3') | k2_pre_topc('#skF_3', B_85)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_85, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_322])).
% 7.72/2.80  tff(c_337, plain, (![B_87]: (v1_tops_1(B_87, '#skF_3') | k2_pre_topc('#skF_3', B_87)!='#skF_4' | ~m1_subset_1(B_87, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_112, c_325])).
% 7.72/2.80  tff(c_341, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_72, c_337])).
% 7.72/2.80  tff(c_344, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_341])).
% 7.72/2.80  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.72/2.80  tff(c_58, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.72/2.80  tff(c_457, plain, (![B_101, A_102]: (v2_tex_2(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v1_tdlat_3(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.72/2.80  tff(c_460, plain, (![B_101]: (v2_tex_2(B_101, '#skF_3') | ~m1_subset_1(B_101, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_457])).
% 7.72/2.80  tff(c_469, plain, (![B_101]: (v2_tex_2(B_101, '#skF_3') | ~m1_subset_1(B_101, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_460])).
% 7.72/2.80  tff(c_473, plain, (![B_103]: (v2_tex_2(B_103, '#skF_3') | ~m1_subset_1(B_103, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_469])).
% 7.72/2.80  tff(c_478, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_473])).
% 7.72/2.80  tff(c_828, plain, (![B_157, A_158]: (v3_tex_2(B_157, A_158) | ~v2_tex_2(B_157, A_158) | ~v1_tops_1(B_157, A_158) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.72/2.80  tff(c_834, plain, (![B_157]: (v3_tex_2(B_157, '#skF_3') | ~v2_tex_2(B_157, '#skF_3') | ~v1_tops_1(B_157, '#skF_3') | ~m1_subset_1(B_157, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_828])).
% 7.72/2.80  tff(c_844, plain, (![B_157]: (v3_tex_2(B_157, '#skF_3') | ~v2_tex_2(B_157, '#skF_3') | ~v1_tops_1(B_157, '#skF_3') | ~m1_subset_1(B_157, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_834])).
% 7.72/2.80  tff(c_878, plain, (![B_161]: (v3_tex_2(B_161, '#skF_3') | ~v2_tex_2(B_161, '#skF_3') | ~v1_tops_1(B_161, '#skF_3') | ~m1_subset_1(B_161, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_844])).
% 7.72/2.80  tff(c_885, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_878])).
% 7.72/2.80  tff(c_889, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_478, c_885])).
% 7.72/2.80  tff(c_891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_889])).
% 7.72/2.80  tff(c_892, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_70])).
% 7.72/2.80  tff(c_961, plain, (![B_185, A_186]: (v2_tex_2(B_185, A_186) | ~v3_tex_2(B_185, A_186) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.72/2.80  tff(c_1000, plain, (![A_187]: (v2_tex_2(u1_struct_0(A_187), A_187) | ~v3_tex_2(u1_struct_0(A_187), A_187) | ~l1_pre_topc(A_187))), inference(resolution, [status(thm)], [c_72, c_961])).
% 7.72/2.80  tff(c_1003, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_960, c_1000])).
% 7.72/2.80  tff(c_1005, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_960, c_1003])).
% 7.72/2.80  tff(c_1006, plain, (~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1005])).
% 7.72/2.80  tff(c_1031, plain, (![A_192, B_193]: (k2_pre_topc(A_192, B_193)=B_193 | ~v4_pre_topc(B_193, A_192) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.72/2.80  tff(c_1034, plain, (![B_193]: (k2_pre_topc('#skF_3', B_193)=B_193 | ~v4_pre_topc(B_193, '#skF_3') | ~m1_subset_1(B_193, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_1031])).
% 7.72/2.80  tff(c_1065, plain, (![B_197]: (k2_pre_topc('#skF_3', B_197)=B_197 | ~v4_pre_topc(B_197, '#skF_3') | ~m1_subset_1(B_197, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1034])).
% 7.72/2.80  tff(c_1074, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_72, c_1065])).
% 7.72/2.80  tff(c_1076, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1074])).
% 7.72/2.80  tff(c_1079, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_1076])).
% 7.72/2.80  tff(c_1083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1079])).
% 7.72/2.80  tff(c_1084, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1074])).
% 7.72/2.80  tff(c_1086, plain, (![B_198, A_199]: (v1_tops_1(B_198, A_199) | k2_pre_topc(A_199, B_198)!=u1_struct_0(A_199) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.72/2.80  tff(c_1089, plain, (![B_198]: (v1_tops_1(B_198, '#skF_3') | k2_pre_topc('#skF_3', B_198)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_198, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_1086])).
% 7.72/2.80  tff(c_1112, plain, (![B_202]: (v1_tops_1(B_202, '#skF_3') | k2_pre_topc('#skF_3', B_202)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_202, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_960, c_1089])).
% 7.72/2.80  tff(c_1119, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1112])).
% 7.72/2.80  tff(c_1123, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1119])).
% 7.72/2.80  tff(c_1351, plain, (![B_239, A_240]: (v2_tex_2(B_239, A_240) | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240) | ~v1_tdlat_3(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.72/2.80  tff(c_1354, plain, (![B_239]: (v2_tex_2(B_239, '#skF_3') | ~m1_subset_1(B_239, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_1351])).
% 7.72/2.80  tff(c_1363, plain, (![B_239]: (v2_tex_2(B_239, '#skF_3') | ~m1_subset_1(B_239, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_1354])).
% 7.72/2.80  tff(c_1367, plain, (![B_241]: (v2_tex_2(B_241, '#skF_3') | ~m1_subset_1(B_241, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_1363])).
% 7.72/2.80  tff(c_1377, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_72, c_1367])).
% 7.72/2.80  tff(c_2031, plain, (![B_312, A_313]: (v3_tex_2(B_312, A_313) | ~v2_tex_2(B_312, A_313) | ~v1_tops_1(B_312, A_313) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_313))) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.72/2.80  tff(c_2037, plain, (![B_312]: (v3_tex_2(B_312, '#skF_3') | ~v2_tex_2(B_312, '#skF_3') | ~v1_tops_1(B_312, '#skF_3') | ~m1_subset_1(B_312, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_2031])).
% 7.72/2.80  tff(c_2047, plain, (![B_312]: (v3_tex_2(B_312, '#skF_3') | ~v2_tex_2(B_312, '#skF_3') | ~v1_tops_1(B_312, '#skF_3') | ~m1_subset_1(B_312, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_2037])).
% 7.72/2.80  tff(c_2051, plain, (![B_314]: (v3_tex_2(B_314, '#skF_3') | ~v2_tex_2(B_314, '#skF_3') | ~v1_tops_1(B_314, '#skF_3') | ~m1_subset_1(B_314, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_2047])).
% 7.72/2.80  tff(c_2061, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_72, c_2051])).
% 7.72/2.80  tff(c_2068, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1377, c_2061])).
% 7.72/2.80  tff(c_2070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1006, c_2068])).
% 7.72/2.80  tff(c_2071, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1005])).
% 7.72/2.80  tff(c_2125, plain, (![A_323, B_324]: (k2_pre_topc(A_323, B_324)=B_324 | ~v4_pre_topc(B_324, A_323) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0(A_323))) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.72/2.80  tff(c_2128, plain, (![B_324]: (k2_pre_topc('#skF_3', B_324)=B_324 | ~v4_pre_topc(B_324, '#skF_3') | ~m1_subset_1(B_324, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_2125])).
% 7.72/2.80  tff(c_2156, plain, (![B_326]: (k2_pre_topc('#skF_3', B_326)=B_326 | ~v4_pre_topc(B_326, '#skF_3') | ~m1_subset_1(B_326, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2128])).
% 7.72/2.80  tff(c_2164, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_978, c_2156])).
% 7.72/2.80  tff(c_2170, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_2164])).
% 7.72/2.80  tff(c_2173, plain, (![B_327, A_328]: (v1_tops_1(B_327, A_328) | k2_pre_topc(A_328, B_327)!=u1_struct_0(A_328) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.72/2.80  tff(c_2176, plain, (![B_327]: (v1_tops_1(B_327, '#skF_3') | k2_pre_topc('#skF_3', B_327)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_327, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_2173])).
% 7.72/2.80  tff(c_2194, plain, (![B_330]: (v1_tops_1(B_330, '#skF_3') | k2_pre_topc('#skF_3', B_330)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_330, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_960, c_2176])).
% 7.72/2.80  tff(c_2202, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_978, c_2194])).
% 7.72/2.80  tff(c_2206, plain, (k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_2202])).
% 7.72/2.80  tff(c_2250, plain, (![A_338, B_339]: (k2_pre_topc(A_338, B_339)=u1_struct_0(A_338) | ~v1_tops_1(B_339, A_338) | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0(A_338))) | ~l1_pre_topc(A_338))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.72/2.80  tff(c_2253, plain, (![B_339]: (k2_pre_topc('#skF_3', B_339)=u1_struct_0('#skF_3') | ~v1_tops_1(B_339, '#skF_3') | ~m1_subset_1(B_339, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_2250])).
% 7.72/2.80  tff(c_2291, plain, (![B_344]: (k2_pre_topc('#skF_3', B_344)=k2_struct_0('#skF_3') | ~v1_tops_1(B_344, '#skF_3') | ~m1_subset_1(B_344, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_960, c_2253])).
% 7.72/2.80  tff(c_2294, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_978, c_2291])).
% 7.72/2.80  tff(c_2301, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2206, c_2294])).
% 7.72/2.80  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.72/2.80  tff(c_930, plain, (![C_176, A_177, B_178]: (r2_hidden(C_176, A_177) | ~r2_hidden(C_176, B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.72/2.80  tff(c_2094, plain, (![A_317, B_318, A_319]: (r2_hidden('#skF_1'(A_317, B_318), A_319) | ~m1_subset_1(A_317, k1_zfmisc_1(A_319)) | r1_tarski(A_317, B_318))), inference(resolution, [status(thm)], [c_6, c_930])).
% 7.72/2.80  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.72/2.80  tff(c_2106, plain, (![A_320, A_321]: (~m1_subset_1(A_320, k1_zfmisc_1(A_321)) | r1_tarski(A_320, A_321))), inference(resolution, [status(thm)], [c_2094, c_4])).
% 7.72/2.80  tff(c_2116, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_978, c_2106])).
% 7.72/2.80  tff(c_4734, plain, (![C_612, B_613, A_614]: (C_612=B_613 | ~r1_tarski(B_613, C_612) | ~v2_tex_2(C_612, A_614) | ~m1_subset_1(C_612, k1_zfmisc_1(u1_struct_0(A_614))) | ~v3_tex_2(B_613, A_614) | ~m1_subset_1(B_613, k1_zfmisc_1(u1_struct_0(A_614))) | ~l1_pre_topc(A_614))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.72/2.80  tff(c_4760, plain, (![A_614]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_614) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_614))) | ~v3_tex_2('#skF_4', A_614) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_614))) | ~l1_pre_topc(A_614))), inference(resolution, [status(thm)], [c_2116, c_4734])).
% 7.72/2.80  tff(c_5123, plain, (![A_653]: (~v2_tex_2(k2_struct_0('#skF_3'), A_653) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_653))) | ~v3_tex_2('#skF_4', A_653) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_653))) | ~l1_pre_topc(A_653))), inference(splitLeft, [status(thm)], [c_4760])).
% 7.72/2.80  tff(c_5126, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_960, c_5123])).
% 7.72/2.80  tff(c_5133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_978, c_960, c_892, c_72, c_2071, c_5126])).
% 7.72/2.80  tff(c_5134, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_4760])).
% 7.72/2.80  tff(c_2140, plain, (![A_325]: (k2_pre_topc(A_325, u1_struct_0(A_325))=u1_struct_0(A_325) | ~v4_pre_topc(u1_struct_0(A_325), A_325) | ~l1_pre_topc(A_325))), inference(resolution, [status(thm)], [c_72, c_2125])).
% 7.72/2.80  tff(c_2143, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_960, c_2140])).
% 7.72/2.80  tff(c_2145, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_960, c_960, c_2143])).
% 7.72/2.80  tff(c_2146, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2145])).
% 7.72/2.80  tff(c_2149, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_2146])).
% 7.72/2.80  tff(c_2153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_2149])).
% 7.72/2.80  tff(c_2154, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_2145])).
% 7.72/2.80  tff(c_2188, plain, (![A_329]: (v1_tops_1(u1_struct_0(A_329), A_329) | k2_pre_topc(A_329, u1_struct_0(A_329))!=u1_struct_0(A_329) | ~l1_pre_topc(A_329))), inference(resolution, [status(thm)], [c_72, c_2173])).
% 7.72/2.80  tff(c_2191, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_960, c_2188])).
% 7.72/2.80  tff(c_2193, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2154, c_960, c_960, c_2191])).
% 7.72/2.80  tff(c_5182, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5134, c_2193])).
% 7.72/2.80  tff(c_5194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2301, c_5182])).
% 7.72/2.80  tff(c_5196, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_2202])).
% 7.72/2.80  tff(c_5330, plain, (![B_671, A_672]: (v4_pre_topc(B_671, A_672) | k2_pre_topc(A_672, B_671)!=B_671 | ~v2_pre_topc(A_672) | ~m1_subset_1(B_671, k1_zfmisc_1(u1_struct_0(A_672))) | ~l1_pre_topc(A_672))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.72/2.80  tff(c_5333, plain, (![B_671]: (v4_pre_topc(B_671, '#skF_3') | k2_pre_topc('#skF_3', B_671)!=B_671 | ~v2_pre_topc('#skF_3') | ~m1_subset_1(B_671, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_5330])).
% 7.72/2.80  tff(c_5345, plain, (![B_673]: (v4_pre_topc(B_673, '#skF_3') | k2_pre_topc('#skF_3', B_673)!=B_673 | ~m1_subset_1(B_673, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_5333])).
% 7.72/2.80  tff(c_5348, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_978, c_5345])).
% 7.72/2.80  tff(c_5354, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5196, c_5348])).
% 7.72/2.80  tff(c_5355, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2170, c_5354])).
% 7.72/2.80  tff(c_6136, plain, (![C_772, B_773, A_774]: (C_772=B_773 | ~r1_tarski(B_773, C_772) | ~v2_tex_2(C_772, A_774) | ~m1_subset_1(C_772, k1_zfmisc_1(u1_struct_0(A_774))) | ~v3_tex_2(B_773, A_774) | ~m1_subset_1(B_773, k1_zfmisc_1(u1_struct_0(A_774))) | ~l1_pre_topc(A_774))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.72/2.80  tff(c_6152, plain, (![A_774]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_774) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_774))) | ~v3_tex_2('#skF_4', A_774) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_774))) | ~l1_pre_topc(A_774))), inference(resolution, [status(thm)], [c_2116, c_6136])).
% 7.72/2.80  tff(c_6637, plain, (![A_824]: (~v2_tex_2(k2_struct_0('#skF_3'), A_824) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_824))) | ~v3_tex_2('#skF_4', A_824) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_824))) | ~l1_pre_topc(A_824))), inference(negUnitSimplification, [status(thm)], [c_5355, c_6152])).
% 7.72/2.80  tff(c_6640, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_960, c_6637])).
% 7.72/2.80  tff(c_6647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_978, c_960, c_892, c_72, c_2071, c_6640])).
% 7.72/2.80  tff(c_6648, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2164])).
% 7.72/2.80  tff(c_6688, plain, (![A_827, B_828]: (k2_pre_topc(A_827, B_828)=u1_struct_0(A_827) | ~v1_tops_1(B_828, A_827) | ~m1_subset_1(B_828, k1_zfmisc_1(u1_struct_0(A_827))) | ~l1_pre_topc(A_827))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.72/2.80  tff(c_6691, plain, (![B_828]: (k2_pre_topc('#skF_3', B_828)=u1_struct_0('#skF_3') | ~v1_tops_1(B_828, '#skF_3') | ~m1_subset_1(B_828, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_6688])).
% 7.72/2.80  tff(c_6709, plain, (![B_830]: (k2_pre_topc('#skF_3', B_830)=k2_struct_0('#skF_3') | ~v1_tops_1(B_830, '#skF_3') | ~m1_subset_1(B_830, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_960, c_6691])).
% 7.72/2.80  tff(c_6712, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_978, c_6709])).
% 7.72/2.80  tff(c_6718, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6648, c_6712])).
% 7.72/2.80  tff(c_6721, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_6718])).
% 7.72/2.80  tff(c_6749, plain, (![B_839, A_840]: (v1_tops_1(B_839, A_840) | k2_pre_topc(A_840, B_839)!=u1_struct_0(A_840) | ~m1_subset_1(B_839, k1_zfmisc_1(u1_struct_0(A_840))) | ~l1_pre_topc(A_840))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.72/2.80  tff(c_6752, plain, (![B_839]: (v1_tops_1(B_839, '#skF_3') | k2_pre_topc('#skF_3', B_839)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_839, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_6749])).
% 7.72/2.80  tff(c_6809, plain, (![B_845]: (v1_tops_1(B_845, '#skF_3') | k2_pre_topc('#skF_3', B_845)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_845, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_960, c_6752])).
% 7.72/2.80  tff(c_6812, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_978, c_6809])).
% 7.72/2.80  tff(c_6818, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6648, c_6812])).
% 7.72/2.80  tff(c_6819, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_6721, c_6818])).
% 7.72/2.80  tff(c_7703, plain, (![C_954, B_955, A_956]: (C_954=B_955 | ~r1_tarski(B_955, C_954) | ~v2_tex_2(C_954, A_956) | ~m1_subset_1(C_954, k1_zfmisc_1(u1_struct_0(A_956))) | ~v3_tex_2(B_955, A_956) | ~m1_subset_1(B_955, k1_zfmisc_1(u1_struct_0(A_956))) | ~l1_pre_topc(A_956))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.72/2.80  tff(c_7719, plain, (![A_956]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_956) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_956))) | ~v3_tex_2('#skF_4', A_956) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_956))) | ~l1_pre_topc(A_956))), inference(resolution, [status(thm)], [c_2116, c_7703])).
% 7.72/2.80  tff(c_8263, plain, (![A_1023]: (~v2_tex_2(k2_struct_0('#skF_3'), A_1023) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_1023))) | ~v3_tex_2('#skF_4', A_1023) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_1023))) | ~l1_pre_topc(A_1023))), inference(negUnitSimplification, [status(thm)], [c_6819, c_7719])).
% 7.72/2.80  tff(c_8266, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_960, c_8263])).
% 7.72/2.80  tff(c_8273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_978, c_960, c_892, c_72, c_2071, c_8266])).
% 7.72/2.80  tff(c_8274, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_6718])).
% 7.72/2.80  tff(c_895, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_892, c_64])).
% 7.72/2.80  tff(c_977, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_960, c_895])).
% 7.72/2.80  tff(c_8285, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8274, c_977])).
% 7.72/2.80  tff(c_8294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_8285])).
% 7.72/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/2.80  
% 7.72/2.80  Inference rules
% 7.72/2.80  ----------------------
% 7.72/2.80  #Ref     : 0
% 7.72/2.80  #Sup     : 1857
% 7.72/2.80  #Fact    : 0
% 7.72/2.80  #Define  : 0
% 7.72/2.80  #Split   : 23
% 7.72/2.80  #Chain   : 0
% 7.72/2.80  #Close   : 0
% 7.72/2.80  
% 7.72/2.80  Ordering : KBO
% 7.72/2.80  
% 7.72/2.80  Simplification rules
% 7.72/2.80  ----------------------
% 7.72/2.80  #Subsume      : 675
% 7.72/2.80  #Demod        : 1260
% 7.72/2.80  #Tautology    : 301
% 7.72/2.80  #SimpNegUnit  : 53
% 7.72/2.80  #BackRed      : 126
% 7.72/2.80  
% 7.72/2.80  #Partial instantiations: 0
% 7.72/2.80  #Strategies tried      : 1
% 7.72/2.80  
% 7.72/2.80  Timing (in seconds)
% 7.72/2.80  ----------------------
% 7.72/2.80  Preprocessing        : 0.34
% 7.72/2.80  Parsing              : 0.18
% 7.72/2.80  CNF conversion       : 0.02
% 7.72/2.80  Main loop            : 1.66
% 7.72/2.80  Inferencing          : 0.53
% 7.72/2.80  Reduction            : 0.45
% 7.72/2.80  Demodulation         : 0.30
% 7.72/2.80  BG Simplification    : 0.05
% 7.72/2.80  Subsumption          : 0.51
% 7.72/2.80  Abstraction          : 0.07
% 7.72/2.80  MUC search           : 0.00
% 7.72/2.80  Cooper               : 0.00
% 7.72/2.80  Total                : 2.06
% 7.72/2.80  Index Insertion      : 0.00
% 7.72/2.80  Index Deletion       : 0.00
% 7.72/2.80  Index Matching       : 0.00
% 7.72/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:09 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 812 expanded)
%              Number of leaves         :   40 ( 280 expanded)
%              Depth                    :   14
%              Number of atoms          :  377 (2351 expanded)
%              Number of equality atoms :   60 ( 297 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_190,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_tops_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_172,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_156,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_4,plain,(
    ! [A_4] : ~ v1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1463,plain,(
    ! [B_194,A_195] :
      ( v1_subset_1(B_194,A_195)
      | B_194 = A_195
      | ~ m1_subset_1(B_194,k1_zfmisc_1(A_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1475,plain,(
    ! [A_4] :
      ( v1_subset_1('#skF_1'(A_4),A_4)
      | '#skF_1'(A_4) = A_4 ) ),
    inference(resolution,[status(thm)],[c_6,c_1463])).

tff(c_1482,plain,(
    ! [A_4] : '#skF_1'(A_4) = A_4 ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_1475])).

tff(c_1485,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1482,c_4])).

tff(c_1484,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1482,c_6])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_58,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1608,plain,(
    ! [A_214,B_215] :
      ( k2_pre_topc(A_214,B_215) = u1_struct_0(A_214)
      | ~ v1_tops_1(B_215,A_214)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1625,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1608])).

tff(c_1632,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1625])).

tff(c_1634,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1632])).

tff(c_1536,plain,(
    ! [B_206,A_207] :
      ( v3_pre_topc(B_206,A_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ v1_tdlat_3(A_207)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1553,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1536])).

tff(c_1560,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_1553])).

tff(c_70,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_75,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_88,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_64])).

tff(c_14,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_131,plain,(
    ! [B_70,A_71] :
      ( v1_subset_1(B_70,A_71)
      | B_70 = A_71
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_140,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_54,c_131])).

tff(c_148,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_140])).

tff(c_100,plain,(
    ! [A_63] :
      ( m1_subset_1(k2_struct_0(A_63),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_63] :
      ( r1_tarski(k2_struct_0(A_63),u1_struct_0(A_63))
      | ~ l1_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_175,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),'#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_104])).

tff(c_196,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_199,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_196])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_199])).

tff(c_205,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_12,plain,(
    ! [A_8] :
      ( m1_subset_1(k2_struct_0(A_8),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1('#skF_5'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_12])).

tff(c_208,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_178])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( v1_subset_1(B_26,A_25)
      | B_26 = A_25
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_215,plain,
    ( v1_subset_1(k2_struct_0('#skF_4'),'#skF_5')
    | k2_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_208,c_30])).

tff(c_218,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_20,plain,(
    ! [A_13] :
      ( v1_tops_1(k2_struct_0(A_13),A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_232,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_20])).

tff(c_240,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_232])).

tff(c_143,plain,(
    ! [A_4] :
      ( v1_subset_1('#skF_1'(A_4),A_4)
      | '#skF_1'(A_4) = A_4 ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_151,plain,(
    ! [A_4] : '#skF_1'(A_4) = A_4 ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_143])).

tff(c_153,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_6])).

tff(c_680,plain,(
    ! [B_115,A_116] :
      ( v2_tex_2(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v1_tdlat_3(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_690,plain,(
    ! [B_115] :
      ( v2_tex_2(B_115,'#skF_4')
      | ~ m1_subset_1(B_115,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_680])).

tff(c_701,plain,(
    ! [B_115] :
      ( v2_tex_2(B_115,'#skF_4')
      | ~ m1_subset_1(B_115,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_690])).

tff(c_705,plain,(
    ! [B_117] :
      ( v2_tex_2(B_117,'#skF_4')
      | ~ m1_subset_1(B_117,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_701])).

tff(c_714,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_153,c_705])).

tff(c_826,plain,(
    ! [B_131,A_132] :
      ( v3_tex_2(B_131,A_132)
      | ~ v2_tex_2(B_131,A_132)
      | ~ v1_tops_1(B_131,A_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_836,plain,(
    ! [B_131] :
      ( v3_tex_2(B_131,'#skF_4')
      | ~ v2_tex_2(B_131,'#skF_4')
      | ~ v1_tops_1(B_131,'#skF_4')
      | ~ m1_subset_1(B_131,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_826])).

tff(c_847,plain,(
    ! [B_131] :
      ( v3_tex_2(B_131,'#skF_4')
      | ~ v2_tex_2(B_131,'#skF_4')
      | ~ v1_tops_1(B_131,'#skF_4')
      | ~ m1_subset_1(B_131,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_836])).

tff(c_851,plain,(
    ! [B_133] :
      ( v3_tex_2(B_133,'#skF_4')
      | ~ v2_tex_2(B_133,'#skF_4')
      | ~ v1_tops_1(B_133,'#skF_4')
      | ~ m1_subset_1(B_133,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_847])).

tff(c_855,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_153,c_851])).

tff(c_862,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_714,c_855])).

tff(c_864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_862])).

tff(c_866,plain,(
    k2_struct_0('#skF_4') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_958,plain,(
    ! [A_145,B_146] :
      ( k2_pre_topc(A_145,B_146) = k2_struct_0(A_145)
      | ~ v1_tops_1(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_968,plain,(
    ! [B_146] :
      ( k2_pre_topc('#skF_4',B_146) = k2_struct_0('#skF_4')
      | ~ v1_tops_1(B_146,'#skF_4')
      | ~ m1_subset_1(B_146,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_958])).

tff(c_989,plain,(
    ! [B_148] :
      ( k2_pre_topc('#skF_4',B_148) = k2_struct_0('#skF_4')
      | ~ v1_tops_1(B_148,'#skF_4')
      | ~ m1_subset_1(B_148,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_968])).

tff(c_1001,plain,
    ( k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) = k2_struct_0('#skF_4')
    | ~ v1_tops_1(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_208,c_989])).

tff(c_1004,plain,(
    ~ v1_tops_1(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_1007,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1004])).

tff(c_1011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1007])).

tff(c_1013,plain,(
    v1_tops_1(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_1012,plain,(
    k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) = k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_1325,plain,(
    ! [A_172,B_173] :
      ( k2_pre_topc(A_172,B_173) = u1_struct_0(A_172)
      | ~ v1_tops_1(B_173,A_172)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1335,plain,(
    ! [B_173] :
      ( k2_pre_topc('#skF_4',B_173) = u1_struct_0('#skF_4')
      | ~ v1_tops_1(B_173,'#skF_4')
      | ~ m1_subset_1(B_173,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_1325])).

tff(c_1390,plain,(
    ! [B_178] :
      ( k2_pre_topc('#skF_4',B_178) = '#skF_5'
      | ~ v1_tops_1(B_178,'#skF_4')
      | ~ m1_subset_1(B_178,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_148,c_1335])).

tff(c_1393,plain,
    ( k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) = '#skF_5'
    | ~ v1_tops_1(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_208,c_1390])).

tff(c_1404,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1013,c_1012,c_1393])).

tff(c_1406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_1404])).

tff(c_1407,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1728,plain,(
    ! [A_227,B_228] :
      ( k2_pre_topc(A_227,B_228) = k2_struct_0(A_227)
      | ~ v1_tops_1(B_228,A_227)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1784,plain,(
    ! [A_232] :
      ( k2_pre_topc(A_232,k2_struct_0(A_232)) = k2_struct_0(A_232)
      | ~ v1_tops_1(k2_struct_0(A_232),A_232)
      | ~ l1_pre_topc(A_232)
      | ~ l1_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_12,c_1728])).

tff(c_1789,plain,(
    ! [A_233] :
      ( k2_pre_topc(A_233,k2_struct_0(A_233)) = k2_struct_0(A_233)
      | ~ l1_struct_0(A_233)
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_20,c_1784])).

tff(c_1662,plain,(
    ! [A_220] :
      ( k2_pre_topc(A_220,k2_struct_0(A_220)) = u1_struct_0(A_220)
      | ~ v1_tops_1(k2_struct_0(A_220),A_220)
      | ~ l1_pre_topc(A_220)
      | ~ l1_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_12,c_1608])).

tff(c_1666,plain,(
    ! [A_13] :
      ( k2_pre_topc(A_13,k2_struct_0(A_13)) = u1_struct_0(A_13)
      | ~ l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_1662])).

tff(c_1804,plain,(
    ! [A_234] :
      ( u1_struct_0(A_234) = k2_struct_0(A_234)
      | ~ l1_struct_0(A_234)
      | ~ l1_pre_topc(A_234)
      | ~ l1_struct_0(A_234)
      | ~ l1_pre_topc(A_234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1789,c_1666])).

tff(c_1834,plain,(
    ! [A_237] :
      ( u1_struct_0(A_237) = k2_struct_0(A_237)
      | ~ l1_struct_0(A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(resolution,[status(thm)],[c_14,c_1804])).

tff(c_1839,plain,(
    ! [A_238] :
      ( u1_struct_0(A_238) = k2_struct_0(A_238)
      | ~ l1_pre_topc(A_238) ) ),
    inference(resolution,[status(thm)],[c_14,c_1834])).

tff(c_1843,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1839])).

tff(c_1847,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_54])).

tff(c_2157,plain,(
    ! [B_251,A_252] :
      ( v1_tops_1(B_251,A_252)
      | ~ v3_tex_2(B_251,A_252)
      | ~ v3_pre_topc(B_251,A_252)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2160,plain,(
    ! [B_251] :
      ( v1_tops_1(B_251,'#skF_4')
      | ~ v3_tex_2(B_251,'#skF_4')
      | ~ v3_pre_topc(B_251,'#skF_4')
      | ~ m1_subset_1(B_251,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1843,c_2157])).

tff(c_2176,plain,(
    ! [B_251] :
      ( v1_tops_1(B_251,'#skF_4')
      | ~ v3_tex_2(B_251,'#skF_4')
      | ~ v3_pre_topc(B_251,'#skF_4')
      | ~ m1_subset_1(B_251,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_2160])).

tff(c_2218,plain,(
    ! [B_255] :
      ( v1_tops_1(B_255,'#skF_4')
      | ~ v3_tex_2(B_255,'#skF_4')
      | ~ v3_pre_topc(B_255,'#skF_4')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2176])).

tff(c_2221,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1847,c_2218])).

tff(c_2232,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1407,c_2221])).

tff(c_2234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1634,c_2232])).

tff(c_2235,plain,(
    k2_pre_topc('#skF_4','#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1632])).

tff(c_1583,plain,(
    ! [B_212,A_213] :
      ( v1_tops_1(B_212,A_213)
      | k2_pre_topc(A_213,B_212) != k2_struct_0(A_213)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1600,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != k2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1583])).

tff(c_1607,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1600])).

tff(c_1633,plain,(
    k2_pre_topc('#skF_4','#skF_5') != k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1607])).

tff(c_2237,plain,(
    u1_struct_0('#skF_4') != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2235,c_1633])).

tff(c_2236,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1632])).

tff(c_2248,plain,(
    ! [A_258,B_259] :
      ( k2_pre_topc(A_258,B_259) = k2_struct_0(A_258)
      | ~ v1_tops_1(B_259,A_258)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2265,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = k2_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2248])).

tff(c_2272,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2236,c_2235,c_2265])).

tff(c_2274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2237,c_2272])).

tff(c_2275,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1607])).

tff(c_2276,plain,(
    k2_pre_topc('#skF_4','#skF_5') = k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1607])).

tff(c_2282,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2275,c_2276,c_1632])).

tff(c_2575,plain,(
    ! [B_277,A_278] :
      ( v2_tex_2(B_277,A_278)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278)
      | ~ v1_tdlat_3(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2578,plain,(
    ! [B_277] :
      ( v2_tex_2(B_277,'#skF_4')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2282,c_2575])).

tff(c_2594,plain,(
    ! [B_277] :
      ( v2_tex_2(B_277,'#skF_4')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_2578])).

tff(c_2600,plain,(
    ! [B_279] :
      ( v2_tex_2(B_279,'#skF_4')
      | ~ m1_subset_1(B_279,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2594])).

tff(c_2613,plain,(
    v2_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1484,c_2600])).

tff(c_1410,plain,(
    ! [A_180,B_181] :
      ( r1_tarski(A_180,B_181)
      | ~ m1_subset_1(A_180,k1_zfmisc_1(B_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1417,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_1410])).

tff(c_2283,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2282,c_1417])).

tff(c_1440,plain,(
    ! [A_189,B_190,C_191] :
      ( k9_subset_1(A_189,B_190,B_190) = B_190
      | ~ m1_subset_1(C_191,k1_zfmisc_1(A_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1452,plain,(
    ! [A_4,B_190] : k9_subset_1(A_4,B_190,B_190) = B_190 ),
    inference(resolution,[status(thm)],[c_6,c_1440])).

tff(c_2285,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2282,c_54])).

tff(c_3222,plain,(
    ! [A_330,B_331,C_332] :
      ( k9_subset_1(u1_struct_0(A_330),B_331,k2_pre_topc(A_330,C_332)) = C_332
      | ~ r1_tarski(C_332,B_331)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(u1_struct_0(A_330)))
      | ~ v2_tex_2(B_331,A_330)
      | ~ m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0(A_330)))
      | ~ l1_pre_topc(A_330)
      | ~ v2_pre_topc(A_330)
      | v2_struct_0(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3226,plain,(
    ! [B_331,C_332] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_331,k2_pre_topc('#skF_4',C_332)) = C_332
      | ~ r1_tarski(C_332,B_331)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v2_tex_2(B_331,'#skF_4')
      | ~ m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2282,c_3222])).

tff(c_3239,plain,(
    ! [B_331,C_332] :
      ( k9_subset_1(k2_struct_0('#skF_4'),B_331,k2_pre_topc('#skF_4',C_332)) = C_332
      | ~ r1_tarski(C_332,B_331)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v2_tex_2(B_331,'#skF_4')
      | ~ m1_subset_1(B_331,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_2282,c_2282,c_3226])).

tff(c_3307,plain,(
    ! [B_338,C_339] :
      ( k9_subset_1(k2_struct_0('#skF_4'),B_338,k2_pre_topc('#skF_4',C_339)) = C_339
      | ~ r1_tarski(C_339,B_338)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v2_tex_2(B_338,'#skF_4')
      | ~ m1_subset_1(B_338,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3239])).

tff(c_3309,plain,(
    ! [B_338] :
      ( k9_subset_1(k2_struct_0('#skF_4'),B_338,k2_pre_topc('#skF_4','#skF_5')) = '#skF_5'
      | ~ r1_tarski('#skF_5',B_338)
      | ~ v2_tex_2(B_338,'#skF_4')
      | ~ m1_subset_1(B_338,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2285,c_3307])).

tff(c_3321,plain,(
    ! [B_340] :
      ( k9_subset_1(k2_struct_0('#skF_4'),B_340,k2_struct_0('#skF_4')) = '#skF_5'
      | ~ r1_tarski('#skF_5',B_340)
      | ~ v2_tex_2(B_340,'#skF_4')
      | ~ m1_subset_1(B_340,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2276,c_3309])).

tff(c_3328,plain,
    ( k9_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_struct_0('#skF_4'))
    | ~ v2_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1484,c_3321])).

tff(c_3338,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2613,c_2283,c_1452,c_3328])).

tff(c_1408,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2284,plain,(
    v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2282,c_1408])).

tff(c_3360,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3338,c_2284])).

tff(c_3370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1485,c_3360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.86  
% 4.66/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.86  %$ v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 4.66/1.86  
% 4.66/1.86  %Foreground sorts:
% 4.66/1.86  
% 4.66/1.86  
% 4.66/1.86  %Background operators:
% 4.66/1.86  
% 4.66/1.86  
% 4.66/1.86  %Foreground operators:
% 4.66/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.66/1.86  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.66/1.86  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.66/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.86  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.66/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.66/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.66/1.86  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.66/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.66/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.66/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.66/1.86  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.66/1.86  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.66/1.86  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.66/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.66/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.66/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.66/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.66/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.66/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.66/1.86  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.66/1.86  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.66/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.66/1.86  
% 4.66/1.89  tff(f_35, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 4.66/1.89  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.66/1.89  tff(f_190, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 4.66/1.89  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.66/1.89  tff(f_107, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 4.66/1.89  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.66/1.89  tff(f_43, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.66/1.89  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.66/1.89  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => v1_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_tops_1)).
% 4.66/1.89  tff(f_140, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 4.66/1.89  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 4.66/1.89  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.66/1.89  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 4.66/1.89  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 4.66/1.89  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 4.66/1.89  tff(c_4, plain, (![A_4]: (~v1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.66/1.89  tff(c_6, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.66/1.89  tff(c_1463, plain, (![B_194, A_195]: (v1_subset_1(B_194, A_195) | B_194=A_195 | ~m1_subset_1(B_194, k1_zfmisc_1(A_195)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.89  tff(c_1475, plain, (![A_4]: (v1_subset_1('#skF_1'(A_4), A_4) | '#skF_1'(A_4)=A_4)), inference(resolution, [status(thm)], [c_6, c_1463])).
% 4.66/1.89  tff(c_1482, plain, (![A_4]: ('#skF_1'(A_4)=A_4)), inference(negUnitSimplification, [status(thm)], [c_4, c_1475])).
% 4.66/1.89  tff(c_1485, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_1482, c_4])).
% 4.66/1.89  tff(c_1484, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_1482, c_6])).
% 4.66/1.89  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.66/1.89  tff(c_60, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.66/1.89  tff(c_58, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.66/1.89  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.66/1.89  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.66/1.89  tff(c_1608, plain, (![A_214, B_215]: (k2_pre_topc(A_214, B_215)=u1_struct_0(A_214) | ~v1_tops_1(B_215, A_214) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.66/1.89  tff(c_1625, plain, (k2_pre_topc('#skF_4', '#skF_5')=u1_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1608])).
% 4.66/1.89  tff(c_1632, plain, (k2_pre_topc('#skF_4', '#skF_5')=u1_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1625])).
% 4.66/1.89  tff(c_1634, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1632])).
% 4.66/1.89  tff(c_1536, plain, (![B_206, A_207]: (v3_pre_topc(B_206, A_207) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_207))) | ~v1_tdlat_3(A_207) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.66/1.89  tff(c_1553, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1536])).
% 4.66/1.89  tff(c_1560, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_1553])).
% 4.66/1.89  tff(c_70, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.66/1.89  tff(c_75, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_70])).
% 4.66/1.89  tff(c_64, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.66/1.89  tff(c_88, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_75, c_64])).
% 4.66/1.89  tff(c_14, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.66/1.89  tff(c_131, plain, (![B_70, A_71]: (v1_subset_1(B_70, A_71) | B_70=A_71 | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.89  tff(c_140, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_54, c_131])).
% 4.66/1.89  tff(c_148, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_75, c_140])).
% 4.66/1.89  tff(c_100, plain, (![A_63]: (m1_subset_1(k2_struct_0(A_63), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.66/1.89  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.89  tff(c_104, plain, (![A_63]: (r1_tarski(k2_struct_0(A_63), u1_struct_0(A_63)) | ~l1_struct_0(A_63))), inference(resolution, [status(thm)], [c_100, c_8])).
% 4.66/1.89  tff(c_175, plain, (r1_tarski(k2_struct_0('#skF_4'), '#skF_5') | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_148, c_104])).
% 4.66/1.89  tff(c_196, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_175])).
% 4.66/1.89  tff(c_199, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_196])).
% 4.66/1.89  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_199])).
% 4.66/1.89  tff(c_205, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_175])).
% 4.66/1.89  tff(c_12, plain, (![A_8]: (m1_subset_1(k2_struct_0(A_8), k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.66/1.89  tff(c_178, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1('#skF_5')) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_148, c_12])).
% 4.66/1.89  tff(c_208, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_178])).
% 4.66/1.89  tff(c_30, plain, (![B_26, A_25]: (v1_subset_1(B_26, A_25) | B_26=A_25 | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.89  tff(c_215, plain, (v1_subset_1(k2_struct_0('#skF_4'), '#skF_5') | k2_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_208, c_30])).
% 4.66/1.89  tff(c_218, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(splitLeft, [status(thm)], [c_215])).
% 4.66/1.89  tff(c_20, plain, (![A_13]: (v1_tops_1(k2_struct_0(A_13), A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.66/1.89  tff(c_232, plain, (v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_218, c_20])).
% 4.66/1.89  tff(c_240, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_232])).
% 4.66/1.89  tff(c_143, plain, (![A_4]: (v1_subset_1('#skF_1'(A_4), A_4) | '#skF_1'(A_4)=A_4)), inference(resolution, [status(thm)], [c_6, c_131])).
% 4.66/1.89  tff(c_151, plain, (![A_4]: ('#skF_1'(A_4)=A_4)), inference(negUnitSimplification, [status(thm)], [c_4, c_143])).
% 4.66/1.89  tff(c_153, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_6])).
% 4.66/1.89  tff(c_680, plain, (![B_115, A_116]: (v2_tex_2(B_115, A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v1_tdlat_3(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.66/1.89  tff(c_690, plain, (![B_115]: (v2_tex_2(B_115, '#skF_4') | ~m1_subset_1(B_115, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_680])).
% 4.66/1.89  tff(c_701, plain, (![B_115]: (v2_tex_2(B_115, '#skF_4') | ~m1_subset_1(B_115, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_690])).
% 4.66/1.89  tff(c_705, plain, (![B_117]: (v2_tex_2(B_117, '#skF_4') | ~m1_subset_1(B_117, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_701])).
% 4.66/1.89  tff(c_714, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_153, c_705])).
% 4.66/1.89  tff(c_826, plain, (![B_131, A_132]: (v3_tex_2(B_131, A_132) | ~v2_tex_2(B_131, A_132) | ~v1_tops_1(B_131, A_132) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.66/1.89  tff(c_836, plain, (![B_131]: (v3_tex_2(B_131, '#skF_4') | ~v2_tex_2(B_131, '#skF_4') | ~v1_tops_1(B_131, '#skF_4') | ~m1_subset_1(B_131, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_826])).
% 4.66/1.89  tff(c_847, plain, (![B_131]: (v3_tex_2(B_131, '#skF_4') | ~v2_tex_2(B_131, '#skF_4') | ~v1_tops_1(B_131, '#skF_4') | ~m1_subset_1(B_131, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_836])).
% 4.66/1.89  tff(c_851, plain, (![B_133]: (v3_tex_2(B_133, '#skF_4') | ~v2_tex_2(B_133, '#skF_4') | ~v1_tops_1(B_133, '#skF_4') | ~m1_subset_1(B_133, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_847])).
% 4.66/1.89  tff(c_855, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_153, c_851])).
% 4.66/1.89  tff(c_862, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_714, c_855])).
% 4.66/1.89  tff(c_864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_862])).
% 4.66/1.89  tff(c_866, plain, (k2_struct_0('#skF_4')!='#skF_5'), inference(splitRight, [status(thm)], [c_215])).
% 4.66/1.89  tff(c_958, plain, (![A_145, B_146]: (k2_pre_topc(A_145, B_146)=k2_struct_0(A_145) | ~v1_tops_1(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.89  tff(c_968, plain, (![B_146]: (k2_pre_topc('#skF_4', B_146)=k2_struct_0('#skF_4') | ~v1_tops_1(B_146, '#skF_4') | ~m1_subset_1(B_146, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_958])).
% 4.66/1.89  tff(c_989, plain, (![B_148]: (k2_pre_topc('#skF_4', B_148)=k2_struct_0('#skF_4') | ~v1_tops_1(B_148, '#skF_4') | ~m1_subset_1(B_148, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_968])).
% 4.66/1.89  tff(c_1001, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))=k2_struct_0('#skF_4') | ~v1_tops_1(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_208, c_989])).
% 4.66/1.89  tff(c_1004, plain, (~v1_tops_1(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1001])).
% 4.66/1.89  tff(c_1007, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_1004])).
% 4.66/1.89  tff(c_1011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1007])).
% 4.66/1.89  tff(c_1013, plain, (v1_tops_1(k2_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_1001])).
% 4.66/1.89  tff(c_1012, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1001])).
% 4.66/1.89  tff(c_1325, plain, (![A_172, B_173]: (k2_pre_topc(A_172, B_173)=u1_struct_0(A_172) | ~v1_tops_1(B_173, A_172) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.66/1.89  tff(c_1335, plain, (![B_173]: (k2_pre_topc('#skF_4', B_173)=u1_struct_0('#skF_4') | ~v1_tops_1(B_173, '#skF_4') | ~m1_subset_1(B_173, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_1325])).
% 4.66/1.89  tff(c_1390, plain, (![B_178]: (k2_pre_topc('#skF_4', B_178)='#skF_5' | ~v1_tops_1(B_178, '#skF_4') | ~m1_subset_1(B_178, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_148, c_1335])).
% 4.66/1.89  tff(c_1393, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))='#skF_5' | ~v1_tops_1(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_208, c_1390])).
% 4.66/1.89  tff(c_1404, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1013, c_1012, c_1393])).
% 4.66/1.89  tff(c_1406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_866, c_1404])).
% 4.66/1.89  tff(c_1407, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_70])).
% 4.66/1.89  tff(c_1728, plain, (![A_227, B_228]: (k2_pre_topc(A_227, B_228)=k2_struct_0(A_227) | ~v1_tops_1(B_228, A_227) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.89  tff(c_1784, plain, (![A_232]: (k2_pre_topc(A_232, k2_struct_0(A_232))=k2_struct_0(A_232) | ~v1_tops_1(k2_struct_0(A_232), A_232) | ~l1_pre_topc(A_232) | ~l1_struct_0(A_232))), inference(resolution, [status(thm)], [c_12, c_1728])).
% 4.66/1.89  tff(c_1789, plain, (![A_233]: (k2_pre_topc(A_233, k2_struct_0(A_233))=k2_struct_0(A_233) | ~l1_struct_0(A_233) | ~l1_pre_topc(A_233))), inference(resolution, [status(thm)], [c_20, c_1784])).
% 4.66/1.89  tff(c_1662, plain, (![A_220]: (k2_pre_topc(A_220, k2_struct_0(A_220))=u1_struct_0(A_220) | ~v1_tops_1(k2_struct_0(A_220), A_220) | ~l1_pre_topc(A_220) | ~l1_struct_0(A_220))), inference(resolution, [status(thm)], [c_12, c_1608])).
% 4.66/1.89  tff(c_1666, plain, (![A_13]: (k2_pre_topc(A_13, k2_struct_0(A_13))=u1_struct_0(A_13) | ~l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_20, c_1662])).
% 4.66/1.89  tff(c_1804, plain, (![A_234]: (u1_struct_0(A_234)=k2_struct_0(A_234) | ~l1_struct_0(A_234) | ~l1_pre_topc(A_234) | ~l1_struct_0(A_234) | ~l1_pre_topc(A_234))), inference(superposition, [status(thm), theory('equality')], [c_1789, c_1666])).
% 4.66/1.89  tff(c_1834, plain, (![A_237]: (u1_struct_0(A_237)=k2_struct_0(A_237) | ~l1_struct_0(A_237) | ~l1_pre_topc(A_237))), inference(resolution, [status(thm)], [c_14, c_1804])).
% 4.66/1.89  tff(c_1839, plain, (![A_238]: (u1_struct_0(A_238)=k2_struct_0(A_238) | ~l1_pre_topc(A_238))), inference(resolution, [status(thm)], [c_14, c_1834])).
% 4.66/1.89  tff(c_1843, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1839])).
% 4.66/1.89  tff(c_1847, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_54])).
% 4.66/1.89  tff(c_2157, plain, (![B_251, A_252]: (v1_tops_1(B_251, A_252) | ~v3_tex_2(B_251, A_252) | ~v3_pre_topc(B_251, A_252) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.66/1.89  tff(c_2160, plain, (![B_251]: (v1_tops_1(B_251, '#skF_4') | ~v3_tex_2(B_251, '#skF_4') | ~v3_pre_topc(B_251, '#skF_4') | ~m1_subset_1(B_251, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1843, c_2157])).
% 4.66/1.89  tff(c_2176, plain, (![B_251]: (v1_tops_1(B_251, '#skF_4') | ~v3_tex_2(B_251, '#skF_4') | ~v3_pre_topc(B_251, '#skF_4') | ~m1_subset_1(B_251, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_2160])).
% 4.66/1.89  tff(c_2218, plain, (![B_255]: (v1_tops_1(B_255, '#skF_4') | ~v3_tex_2(B_255, '#skF_4') | ~v3_pre_topc(B_255, '#skF_4') | ~m1_subset_1(B_255, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_2176])).
% 4.66/1.89  tff(c_2221, plain, (v1_tops_1('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1847, c_2218])).
% 4.66/1.89  tff(c_2232, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_1407, c_2221])).
% 4.66/1.89  tff(c_2234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1634, c_2232])).
% 4.66/1.89  tff(c_2235, plain, (k2_pre_topc('#skF_4', '#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1632])).
% 4.66/1.89  tff(c_1583, plain, (![B_212, A_213]: (v1_tops_1(B_212, A_213) | k2_pre_topc(A_213, B_212)!=k2_struct_0(A_213) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.89  tff(c_1600, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!=k2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1583])).
% 4.66/1.89  tff(c_1607, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1600])).
% 4.66/1.89  tff(c_1633, plain, (k2_pre_topc('#skF_4', '#skF_5')!=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1607])).
% 4.66/1.89  tff(c_2237, plain, (u1_struct_0('#skF_4')!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2235, c_1633])).
% 4.66/1.89  tff(c_2236, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1632])).
% 4.66/1.89  tff(c_2248, plain, (![A_258, B_259]: (k2_pre_topc(A_258, B_259)=k2_struct_0(A_258) | ~v1_tops_1(B_259, A_258) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.89  tff(c_2265, plain, (k2_pre_topc('#skF_4', '#skF_5')=k2_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2248])).
% 4.66/1.89  tff(c_2272, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2236, c_2235, c_2265])).
% 4.66/1.89  tff(c_2274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2237, c_2272])).
% 4.66/1.89  tff(c_2275, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1607])).
% 4.66/1.89  tff(c_2276, plain, (k2_pre_topc('#skF_4', '#skF_5')=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1607])).
% 4.66/1.89  tff(c_2282, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2275, c_2276, c_1632])).
% 4.66/1.89  tff(c_2575, plain, (![B_277, A_278]: (v2_tex_2(B_277, A_278) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278) | ~v1_tdlat_3(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.66/1.89  tff(c_2578, plain, (![B_277]: (v2_tex_2(B_277, '#skF_4') | ~m1_subset_1(B_277, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2282, c_2575])).
% 4.66/1.89  tff(c_2594, plain, (![B_277]: (v2_tex_2(B_277, '#skF_4') | ~m1_subset_1(B_277, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_2578])).
% 4.66/1.89  tff(c_2600, plain, (![B_279]: (v2_tex_2(B_279, '#skF_4') | ~m1_subset_1(B_279, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_2594])).
% 4.66/1.89  tff(c_2613, plain, (v2_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1484, c_2600])).
% 4.66/1.89  tff(c_1410, plain, (![A_180, B_181]: (r1_tarski(A_180, B_181) | ~m1_subset_1(A_180, k1_zfmisc_1(B_181)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.89  tff(c_1417, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_1410])).
% 4.66/1.89  tff(c_2283, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2282, c_1417])).
% 4.66/1.89  tff(c_1440, plain, (![A_189, B_190, C_191]: (k9_subset_1(A_189, B_190, B_190)=B_190 | ~m1_subset_1(C_191, k1_zfmisc_1(A_189)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.66/1.89  tff(c_1452, plain, (![A_4, B_190]: (k9_subset_1(A_4, B_190, B_190)=B_190)), inference(resolution, [status(thm)], [c_6, c_1440])).
% 4.66/1.89  tff(c_2285, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2282, c_54])).
% 4.66/1.89  tff(c_3222, plain, (![A_330, B_331, C_332]: (k9_subset_1(u1_struct_0(A_330), B_331, k2_pre_topc(A_330, C_332))=C_332 | ~r1_tarski(C_332, B_331) | ~m1_subset_1(C_332, k1_zfmisc_1(u1_struct_0(A_330))) | ~v2_tex_2(B_331, A_330) | ~m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0(A_330))) | ~l1_pre_topc(A_330) | ~v2_pre_topc(A_330) | v2_struct_0(A_330))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.66/1.89  tff(c_3226, plain, (![B_331, C_332]: (k9_subset_1(u1_struct_0('#skF_4'), B_331, k2_pre_topc('#skF_4', C_332))=C_332 | ~r1_tarski(C_332, B_331) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v2_tex_2(B_331, '#skF_4') | ~m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2282, c_3222])).
% 4.66/1.89  tff(c_3239, plain, (![B_331, C_332]: (k9_subset_1(k2_struct_0('#skF_4'), B_331, k2_pre_topc('#skF_4', C_332))=C_332 | ~r1_tarski(C_332, B_331) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v2_tex_2(B_331, '#skF_4') | ~m1_subset_1(B_331, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_2282, c_2282, c_3226])).
% 4.66/1.89  tff(c_3307, plain, (![B_338, C_339]: (k9_subset_1(k2_struct_0('#skF_4'), B_338, k2_pre_topc('#skF_4', C_339))=C_339 | ~r1_tarski(C_339, B_338) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v2_tex_2(B_338, '#skF_4') | ~m1_subset_1(B_338, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_3239])).
% 4.66/1.89  tff(c_3309, plain, (![B_338]: (k9_subset_1(k2_struct_0('#skF_4'), B_338, k2_pre_topc('#skF_4', '#skF_5'))='#skF_5' | ~r1_tarski('#skF_5', B_338) | ~v2_tex_2(B_338, '#skF_4') | ~m1_subset_1(B_338, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2285, c_3307])).
% 4.66/1.89  tff(c_3321, plain, (![B_340]: (k9_subset_1(k2_struct_0('#skF_4'), B_340, k2_struct_0('#skF_4'))='#skF_5' | ~r1_tarski('#skF_5', B_340) | ~v2_tex_2(B_340, '#skF_4') | ~m1_subset_1(B_340, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2276, c_3309])).
% 4.66/1.89  tff(c_3328, plain, (k9_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))='#skF_5' | ~r1_tarski('#skF_5', k2_struct_0('#skF_4')) | ~v2_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1484, c_3321])).
% 4.66/1.89  tff(c_3338, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2613, c_2283, c_1452, c_3328])).
% 4.66/1.89  tff(c_1408, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_70])).
% 4.66/1.89  tff(c_2284, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2282, c_1408])).
% 4.66/1.89  tff(c_3360, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3338, c_2284])).
% 4.66/1.89  tff(c_3370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1485, c_3360])).
% 4.66/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.89  
% 4.66/1.89  Inference rules
% 4.66/1.89  ----------------------
% 4.66/1.89  #Ref     : 0
% 4.66/1.89  #Sup     : 624
% 4.66/1.89  #Fact    : 0
% 4.66/1.89  #Define  : 0
% 4.66/1.89  #Split   : 9
% 4.66/1.89  #Chain   : 0
% 4.66/1.89  #Close   : 0
% 4.66/1.89  
% 4.66/1.89  Ordering : KBO
% 4.66/1.89  
% 4.66/1.89  Simplification rules
% 4.66/1.89  ----------------------
% 4.66/1.89  #Subsume      : 130
% 4.66/1.89  #Demod        : 671
% 4.66/1.89  #Tautology    : 222
% 4.66/1.89  #SimpNegUnit  : 68
% 4.66/1.89  #BackRed      : 45
% 4.66/1.89  
% 4.66/1.89  #Partial instantiations: 0
% 4.66/1.89  #Strategies tried      : 1
% 4.66/1.89  
% 4.66/1.89  Timing (in seconds)
% 4.66/1.89  ----------------------
% 4.66/1.89  Preprocessing        : 0.36
% 4.66/1.89  Parsing              : 0.19
% 4.66/1.89  CNF conversion       : 0.03
% 4.66/1.89  Main loop            : 0.76
% 4.66/1.89  Inferencing          : 0.28
% 4.66/1.89  Reduction            : 0.25
% 4.66/1.89  Demodulation         : 0.15
% 4.66/1.89  BG Simplification    : 0.04
% 4.66/1.89  Subsumption          : 0.13
% 4.66/1.89  Abstraction          : 0.04
% 4.66/1.89  MUC search           : 0.00
% 4.66/1.89  Cooper               : 0.00
% 4.66/1.89  Total                : 1.17
% 4.66/1.89  Index Insertion      : 0.00
% 4.66/1.89  Index Deletion       : 0.00
% 4.66/1.89  Index Matching       : 0.00
% 4.66/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------

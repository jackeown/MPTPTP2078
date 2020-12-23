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
% DateTime   : Thu Dec  3 10:30:09 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 641 expanded)
%              Number of leaves         :   36 ( 227 expanded)
%              Depth                    :   14
%              Number of atoms          :  289 (1666 expanded)
%              Number of equality atoms :   32 ( 197 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_32,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_141,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_123,axiom,(
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

tff(f_93,axiom,(
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

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] : ~ v1_subset_1(k2_subset_1(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_3] : ~ v1_subset_1(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_14,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_6] :
      ( m1_subset_1(k2_struct_0(A_6),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_847,plain,(
    ! [B_124,A_125] :
      ( v1_subset_1(B_124,A_125)
      | B_124 = A_125
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_881,plain,(
    ! [A_128] :
      ( v1_subset_1(k2_struct_0(A_128),u1_struct_0(A_128))
      | u1_struct_0(A_128) = k2_struct_0(A_128)
      | ~ l1_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_12,c_847])).

tff(c_16,plain,(
    ! [A_8] :
      ( ~ v1_subset_1(k2_struct_0(A_8),u1_struct_0(A_8))
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_886,plain,(
    ! [A_129] :
      ( u1_struct_0(A_129) = k2_struct_0(A_129)
      | ~ l1_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_881,c_16])).

tff(c_891,plain,(
    ! [A_130] :
      ( u1_struct_0(A_130) = k2_struct_0(A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_14,c_886])).

tff(c_895,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_891])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_898,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_46])).

tff(c_56,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_77,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_80,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_62])).

tff(c_111,plain,(
    ! [B_47,A_48] :
      ( v1_subset_1(B_47,A_48)
      | B_47 = A_48
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_120,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_111])).

tff(c_128,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_120])).

tff(c_105,plain,(
    ! [A_45] :
      ( m1_subset_1(k2_struct_0(A_45),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_109,plain,(
    ! [A_45] :
      ( r1_tarski(k2_struct_0(A_45),u1_struct_0(A_45))
      | ~ l1_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_105,c_8])).

tff(c_141,plain,
    ( r1_tarski(k2_struct_0('#skF_2'),'#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_109])).

tff(c_151,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_154,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_151])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_154])).

tff(c_160,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_147,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_2'),'#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_16])).

tff(c_182,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_147])).

tff(c_144,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1('#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_12])).

tff(c_184,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_144])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( v1_subset_1(B_15,A_14)
      | B_15 = A_14
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_187,plain,
    ( v1_subset_1(k2_struct_0('#skF_2'),'#skF_3')
    | k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_184,c_26])).

tff(c_193,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_187])).

tff(c_18,plain,(
    ! [A_9] :
      ( k2_pre_topc(A_9,k2_struct_0(A_9)) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_210,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_18])).

tff(c_221,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_193,c_210])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_347,plain,(
    ! [B_66,A_67] :
      ( v1_tops_1(B_66,A_67)
      | k2_pre_topc(A_67,B_66) != u1_struct_0(A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_350,plain,(
    ! [B_66] :
      ( v1_tops_1(B_66,'#skF_2')
      | k2_pre_topc('#skF_2',B_66) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_347])).

tff(c_367,plain,(
    ! [B_68] :
      ( v1_tops_1(B_68,'#skF_2')
      | k2_pre_topc('#skF_2',B_68) != '#skF_3'
      | ~ m1_subset_1(B_68,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_128,c_350])).

tff(c_375,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_367])).

tff(c_379,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_375])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_398,plain,(
    ! [B_70,A_71] :
      ( v2_tex_2(B_70,A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v1_tdlat_3(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_401,plain,(
    ! [B_70] :
      ( v2_tex_2(B_70,'#skF_2')
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_398])).

tff(c_414,plain,(
    ! [B_70] :
      ( v2_tex_2(B_70,'#skF_2')
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_401])).

tff(c_419,plain,(
    ! [B_72] :
      ( v2_tex_2(B_72,'#skF_2')
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_414])).

tff(c_429,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_419])).

tff(c_767,plain,(
    ! [B_111,A_112] :
      ( v3_tex_2(B_111,A_112)
      | ~ v2_tex_2(B_111,A_112)
      | ~ v1_tops_1(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_773,plain,(
    ! [B_111] :
      ( v3_tex_2(B_111,'#skF_2')
      | ~ v2_tex_2(B_111,'#skF_2')
      | ~ v1_tops_1(B_111,'#skF_2')
      | ~ m1_subset_1(B_111,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_767])).

tff(c_787,plain,(
    ! [B_111] :
      ( v3_tex_2(B_111,'#skF_2')
      | ~ v2_tex_2(B_111,'#skF_2')
      | ~ v1_tops_1(B_111,'#skF_2')
      | ~ m1_subset_1(B_111,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_773])).

tff(c_792,plain,(
    ! [B_113] :
      ( v3_tex_2(B_113,'#skF_2')
      | ~ v2_tex_2(B_113,'#skF_2')
      | ~ v1_tops_1(B_113,'#skF_2')
      | ~ m1_subset_1(B_113,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_787])).

tff(c_803,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_792])).

tff(c_808,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_429,c_803])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_808])).

tff(c_812,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_914,plain,(
    ! [B_131,A_132] :
      ( v2_tex_2(B_131,A_132)
      | ~ v3_tex_2(B_131,A_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_917,plain,(
    ! [B_131] :
      ( v2_tex_2(B_131,'#skF_2')
      | ~ v3_tex_2(B_131,'#skF_2')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_914])).

tff(c_944,plain,(
    ! [B_133] :
      ( v2_tex_2(B_133,'#skF_2')
      | ~ v3_tex_2(B_133,'#skF_2')
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_917])).

tff(c_960,plain,
    ( v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_944])).

tff(c_961,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_960])).

tff(c_980,plain,(
    ! [B_136,A_137] :
      ( v1_tops_1(B_136,A_137)
      | k2_pre_topc(A_137,B_136) != u1_struct_0(A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_983,plain,(
    ! [B_136] :
      ( v1_tops_1(B_136,'#skF_2')
      | k2_pre_topc('#skF_2',B_136) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_980])).

tff(c_1016,plain,(
    ! [B_141] :
      ( v1_tops_1(B_141,'#skF_2')
      | k2_pre_topc('#skF_2',B_141) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_895,c_983])).

tff(c_1030,plain,
    ( v1_tops_1(k2_struct_0('#skF_2'),'#skF_2')
    | k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1016])).

tff(c_1032,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1030])).

tff(c_1035,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1032])).

tff(c_1039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1035])).

tff(c_1040,plain,(
    v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1030])).

tff(c_1140,plain,(
    ! [B_150,A_151] :
      ( v2_tex_2(B_150,A_151)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v1_tdlat_3(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1143,plain,(
    ! [B_150] :
      ( v2_tex_2(B_150,'#skF_2')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_1140])).

tff(c_1156,plain,(
    ! [B_150] :
      ( v2_tex_2(B_150,'#skF_2')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1143])).

tff(c_1161,plain,(
    ! [B_152] :
      ( v2_tex_2(B_152,'#skF_2')
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1156])).

tff(c_1176,plain,(
    v2_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1161])).

tff(c_1452,plain,(
    ! [B_185,A_186] :
      ( v3_tex_2(B_185,A_186)
      | ~ v2_tex_2(B_185,A_186)
      | ~ v1_tops_1(B_185,A_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1455,plain,(
    ! [B_185] :
      ( v3_tex_2(B_185,'#skF_2')
      | ~ v2_tex_2(B_185,'#skF_2')
      | ~ v1_tops_1(B_185,'#skF_2')
      | ~ m1_subset_1(B_185,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_1452])).

tff(c_1468,plain,(
    ! [B_185] :
      ( v3_tex_2(B_185,'#skF_2')
      | ~ v2_tex_2(B_185,'#skF_2')
      | ~ v1_tops_1(B_185,'#skF_2')
      | ~ m1_subset_1(B_185,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1455])).

tff(c_1473,plain,(
    ! [B_187] :
      ( v3_tex_2(B_187,'#skF_2')
      | ~ v2_tex_2(B_187,'#skF_2')
      | ~ v1_tops_1(B_187,'#skF_2')
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1468])).

tff(c_1484,plain,
    ( v3_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1473])).

tff(c_1491,plain,(
    v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1176,c_1484])).

tff(c_1493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_961,c_1491])).

tff(c_1494,plain,(
    v2_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_960])).

tff(c_816,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(A_115,B_116)
      | ~ m1_subset_1(A_115,k1_zfmisc_1(B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_823,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_816])).

tff(c_896,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_823])).

tff(c_2849,plain,(
    ! [C_313,B_314,A_315] :
      ( C_313 = B_314
      | ~ r1_tarski(B_314,C_313)
      | ~ v2_tex_2(C_313,A_315)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ v3_tex_2(B_314,A_315)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2859,plain,(
    ! [A_315] :
      ( k2_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(k2_struct_0('#skF_2'),A_315)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ v3_tex_2('#skF_3',A_315)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(resolution,[status(thm)],[c_896,c_2849])).

tff(c_2982,plain,(
    ! [A_327] :
      ( ~ v2_tex_2(k2_struct_0('#skF_2'),A_327)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ v3_tex_2('#skF_3',A_327)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ l1_pre_topc(A_327) ) ),
    inference(splitLeft,[status(thm)],[c_2859])).

tff(c_2985,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_2982])).

tff(c_2995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_898,c_895,c_812,c_64,c_1494,c_2985])).

tff(c_2996,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2859])).

tff(c_811,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_897,plain,(
    v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_811])).

tff(c_3021,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2996,c_897])).

tff(c_3029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_3021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:13:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.80  
% 4.62/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.80  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.62/1.80  
% 4.62/1.80  %Foreground sorts:
% 4.62/1.80  
% 4.62/1.80  
% 4.62/1.80  %Background operators:
% 4.62/1.80  
% 4.62/1.80  
% 4.62/1.80  %Foreground operators:
% 4.62/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.62/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.80  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.62/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.62/1.80  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.62/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.80  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.62/1.80  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.62/1.80  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.62/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.62/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.80  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.62/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.62/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.62/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.62/1.80  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.62/1.80  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.62/1.80  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.62/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.80  
% 4.83/1.82  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.83/1.82  tff(f_32, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.83/1.82  tff(f_141, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 4.83/1.82  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.83/1.82  tff(f_40, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.83/1.82  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.83/1.82  tff(f_49, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 4.83/1.82  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.83/1.82  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 4.83/1.82  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.83/1.82  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.83/1.82  tff(f_107, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 4.83/1.82  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.83/1.82  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.83/1.82  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.83/1.82  tff(c_6, plain, (![A_3]: (~v1_subset_1(k2_subset_1(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.83/1.82  tff(c_63, plain, (![A_3]: (~v1_subset_1(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 4.83/1.82  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.83/1.82  tff(c_14, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.83/1.82  tff(c_12, plain, (![A_6]: (m1_subset_1(k2_struct_0(A_6), k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.83/1.82  tff(c_847, plain, (![B_124, A_125]: (v1_subset_1(B_124, A_125) | B_124=A_125 | ~m1_subset_1(B_124, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.83/1.82  tff(c_881, plain, (![A_128]: (v1_subset_1(k2_struct_0(A_128), u1_struct_0(A_128)) | u1_struct_0(A_128)=k2_struct_0(A_128) | ~l1_struct_0(A_128))), inference(resolution, [status(thm)], [c_12, c_847])).
% 4.83/1.82  tff(c_16, plain, (![A_8]: (~v1_subset_1(k2_struct_0(A_8), u1_struct_0(A_8)) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.83/1.82  tff(c_886, plain, (![A_129]: (u1_struct_0(A_129)=k2_struct_0(A_129) | ~l1_struct_0(A_129))), inference(resolution, [status(thm)], [c_881, c_16])).
% 4.83/1.82  tff(c_891, plain, (![A_130]: (u1_struct_0(A_130)=k2_struct_0(A_130) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_14, c_886])).
% 4.83/1.82  tff(c_895, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_891])).
% 4.83/1.82  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.83/1.82  tff(c_898, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_46])).
% 4.83/1.82  tff(c_56, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.83/1.82  tff(c_77, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 4.83/1.82  tff(c_62, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.83/1.82  tff(c_80, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_77, c_62])).
% 4.83/1.82  tff(c_111, plain, (![B_47, A_48]: (v1_subset_1(B_47, A_48) | B_47=A_48 | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.83/1.82  tff(c_120, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_46, c_111])).
% 4.83/1.82  tff(c_128, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_80, c_120])).
% 4.83/1.82  tff(c_105, plain, (![A_45]: (m1_subset_1(k2_struct_0(A_45), k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.83/1.82  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.83/1.82  tff(c_109, plain, (![A_45]: (r1_tarski(k2_struct_0(A_45), u1_struct_0(A_45)) | ~l1_struct_0(A_45))), inference(resolution, [status(thm)], [c_105, c_8])).
% 4.83/1.82  tff(c_141, plain, (r1_tarski(k2_struct_0('#skF_2'), '#skF_3') | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_128, c_109])).
% 4.83/1.82  tff(c_151, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_141])).
% 4.83/1.82  tff(c_154, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_151])).
% 4.83/1.82  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_154])).
% 4.83/1.82  tff(c_160, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_141])).
% 4.83/1.82  tff(c_147, plain, (~v1_subset_1(k2_struct_0('#skF_2'), '#skF_3') | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_128, c_16])).
% 4.83/1.82  tff(c_182, plain, (~v1_subset_1(k2_struct_0('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_147])).
% 4.83/1.82  tff(c_144, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1('#skF_3')) | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_128, c_12])).
% 4.83/1.82  tff(c_184, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_144])).
% 4.83/1.82  tff(c_26, plain, (![B_15, A_14]: (v1_subset_1(B_15, A_14) | B_15=A_14 | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.83/1.82  tff(c_187, plain, (v1_subset_1(k2_struct_0('#skF_2'), '#skF_3') | k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_184, c_26])).
% 4.83/1.82  tff(c_193, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_182, c_187])).
% 4.83/1.82  tff(c_18, plain, (![A_9]: (k2_pre_topc(A_9, k2_struct_0(A_9))=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.83/1.82  tff(c_210, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_193, c_18])).
% 4.83/1.82  tff(c_221, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_193, c_210])).
% 4.83/1.82  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.83/1.82  tff(c_64, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.83/1.82  tff(c_347, plain, (![B_66, A_67]: (v1_tops_1(B_66, A_67) | k2_pre_topc(A_67, B_66)!=u1_struct_0(A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.83/1.82  tff(c_350, plain, (![B_66]: (v1_tops_1(B_66, '#skF_2') | k2_pre_topc('#skF_2', B_66)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_347])).
% 4.83/1.82  tff(c_367, plain, (![B_68]: (v1_tops_1(B_68, '#skF_2') | k2_pre_topc('#skF_2', B_68)!='#skF_3' | ~m1_subset_1(B_68, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_128, c_350])).
% 4.83/1.82  tff(c_375, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_64, c_367])).
% 4.83/1.82  tff(c_379, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_375])).
% 4.83/1.82  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.83/1.82  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.83/1.82  tff(c_50, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.83/1.82  tff(c_398, plain, (![B_70, A_71]: (v2_tex_2(B_70, A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v1_tdlat_3(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.83/1.82  tff(c_401, plain, (![B_70]: (v2_tex_2(B_70, '#skF_2') | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_398])).
% 4.83/1.82  tff(c_414, plain, (![B_70]: (v2_tex_2(B_70, '#skF_2') | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_401])).
% 4.83/1.82  tff(c_419, plain, (![B_72]: (v2_tex_2(B_72, '#skF_2') | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_414])).
% 4.83/1.82  tff(c_429, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_419])).
% 4.83/1.82  tff(c_767, plain, (![B_111, A_112]: (v3_tex_2(B_111, A_112) | ~v2_tex_2(B_111, A_112) | ~v1_tops_1(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.82  tff(c_773, plain, (![B_111]: (v3_tex_2(B_111, '#skF_2') | ~v2_tex_2(B_111, '#skF_2') | ~v1_tops_1(B_111, '#skF_2') | ~m1_subset_1(B_111, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_767])).
% 4.83/1.82  tff(c_787, plain, (![B_111]: (v3_tex_2(B_111, '#skF_2') | ~v2_tex_2(B_111, '#skF_2') | ~v1_tops_1(B_111, '#skF_2') | ~m1_subset_1(B_111, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_773])).
% 4.83/1.82  tff(c_792, plain, (![B_113]: (v3_tex_2(B_113, '#skF_2') | ~v2_tex_2(B_113, '#skF_2') | ~v1_tops_1(B_113, '#skF_2') | ~m1_subset_1(B_113, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_787])).
% 4.83/1.82  tff(c_803, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_792])).
% 4.83/1.82  tff(c_808, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_429, c_803])).
% 4.83/1.82  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_808])).
% 4.83/1.82  tff(c_812, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 4.83/1.82  tff(c_914, plain, (![B_131, A_132]: (v2_tex_2(B_131, A_132) | ~v3_tex_2(B_131, A_132) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.83/1.82  tff(c_917, plain, (![B_131]: (v2_tex_2(B_131, '#skF_2') | ~v3_tex_2(B_131, '#skF_2') | ~m1_subset_1(B_131, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_895, c_914])).
% 4.83/1.82  tff(c_944, plain, (![B_133]: (v2_tex_2(B_133, '#skF_2') | ~v3_tex_2(B_133, '#skF_2') | ~m1_subset_1(B_133, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_917])).
% 4.83/1.82  tff(c_960, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_64, c_944])).
% 4.83/1.82  tff(c_961, plain, (~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_960])).
% 4.83/1.82  tff(c_980, plain, (![B_136, A_137]: (v1_tops_1(B_136, A_137) | k2_pre_topc(A_137, B_136)!=u1_struct_0(A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.83/1.82  tff(c_983, plain, (![B_136]: (v1_tops_1(B_136, '#skF_2') | k2_pre_topc('#skF_2', B_136)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_895, c_980])).
% 4.83/1.82  tff(c_1016, plain, (![B_141]: (v1_tops_1(B_141, '#skF_2') | k2_pre_topc('#skF_2', B_141)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_895, c_983])).
% 4.83/1.82  tff(c_1030, plain, (v1_tops_1(k2_struct_0('#skF_2'), '#skF_2') | k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1016])).
% 4.83/1.82  tff(c_1032, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1030])).
% 4.83/1.82  tff(c_1035, plain, (~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1032])).
% 4.83/1.82  tff(c_1039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1035])).
% 4.83/1.82  tff(c_1040, plain, (v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_1030])).
% 4.83/1.82  tff(c_1140, plain, (![B_150, A_151]: (v2_tex_2(B_150, A_151) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v1_tdlat_3(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.83/1.82  tff(c_1143, plain, (![B_150]: (v2_tex_2(B_150, '#skF_2') | ~m1_subset_1(B_150, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_895, c_1140])).
% 4.83/1.82  tff(c_1156, plain, (![B_150]: (v2_tex_2(B_150, '#skF_2') | ~m1_subset_1(B_150, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_1143])).
% 4.83/1.82  tff(c_1161, plain, (![B_152]: (v2_tex_2(B_152, '#skF_2') | ~m1_subset_1(B_152, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1156])).
% 4.83/1.82  tff(c_1176, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_64, c_1161])).
% 4.83/1.82  tff(c_1452, plain, (![B_185, A_186]: (v3_tex_2(B_185, A_186) | ~v2_tex_2(B_185, A_186) | ~v1_tops_1(B_185, A_186) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.82  tff(c_1455, plain, (![B_185]: (v3_tex_2(B_185, '#skF_2') | ~v2_tex_2(B_185, '#skF_2') | ~v1_tops_1(B_185, '#skF_2') | ~m1_subset_1(B_185, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_895, c_1452])).
% 4.83/1.82  tff(c_1468, plain, (![B_185]: (v3_tex_2(B_185, '#skF_2') | ~v2_tex_2(B_185, '#skF_2') | ~v1_tops_1(B_185, '#skF_2') | ~m1_subset_1(B_185, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1455])).
% 4.83/1.82  tff(c_1473, plain, (![B_187]: (v3_tex_2(B_187, '#skF_2') | ~v2_tex_2(B_187, '#skF_2') | ~v1_tops_1(B_187, '#skF_2') | ~m1_subset_1(B_187, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1468])).
% 4.83/1.82  tff(c_1484, plain, (v3_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_64, c_1473])).
% 4.83/1.82  tff(c_1491, plain, (v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1176, c_1484])).
% 4.83/1.82  tff(c_1493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_961, c_1491])).
% 4.83/1.82  tff(c_1494, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_960])).
% 4.83/1.82  tff(c_816, plain, (![A_115, B_116]: (r1_tarski(A_115, B_116) | ~m1_subset_1(A_115, k1_zfmisc_1(B_116)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.83/1.82  tff(c_823, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_816])).
% 4.83/1.82  tff(c_896, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_823])).
% 4.83/1.82  tff(c_2849, plain, (![C_313, B_314, A_315]: (C_313=B_314 | ~r1_tarski(B_314, C_313) | ~v2_tex_2(C_313, A_315) | ~m1_subset_1(C_313, k1_zfmisc_1(u1_struct_0(A_315))) | ~v3_tex_2(B_314, A_315) | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.83/1.82  tff(c_2859, plain, (![A_315]: (k2_struct_0('#skF_2')='#skF_3' | ~v2_tex_2(k2_struct_0('#skF_2'), A_315) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_315))) | ~v3_tex_2('#skF_3', A_315) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315))), inference(resolution, [status(thm)], [c_896, c_2849])).
% 4.83/1.82  tff(c_2982, plain, (![A_327]: (~v2_tex_2(k2_struct_0('#skF_2'), A_327) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_327))) | ~v3_tex_2('#skF_3', A_327) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_327))) | ~l1_pre_topc(A_327))), inference(splitLeft, [status(thm)], [c_2859])).
% 4.83/1.82  tff(c_2985, plain, (~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_895, c_2982])).
% 4.83/1.82  tff(c_2995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_898, c_895, c_812, c_64, c_1494, c_2985])).
% 4.83/1.82  tff(c_2996, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2859])).
% 4.83/1.82  tff(c_811, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 4.83/1.82  tff(c_897, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_811])).
% 4.83/1.82  tff(c_3021, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2996, c_897])).
% 4.83/1.82  tff(c_3029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_3021])).
% 4.83/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.82  
% 4.83/1.82  Inference rules
% 4.83/1.82  ----------------------
% 4.83/1.82  #Ref     : 0
% 4.83/1.82  #Sup     : 557
% 4.83/1.82  #Fact    : 0
% 4.83/1.82  #Define  : 0
% 4.83/1.82  #Split   : 9
% 4.83/1.82  #Chain   : 0
% 4.83/1.82  #Close   : 0
% 4.83/1.82  
% 4.83/1.82  Ordering : KBO
% 4.83/1.82  
% 4.83/1.82  Simplification rules
% 4.83/1.82  ----------------------
% 4.83/1.82  #Subsume      : 126
% 4.83/1.82  #Demod        : 642
% 4.83/1.82  #Tautology    : 177
% 4.83/1.82  #SimpNegUnit  : 52
% 4.83/1.82  #BackRed      : 63
% 4.83/1.82  
% 4.83/1.82  #Partial instantiations: 0
% 4.83/1.82  #Strategies tried      : 1
% 4.83/1.82  
% 4.83/1.82  Timing (in seconds)
% 4.83/1.82  ----------------------
% 4.83/1.82  Preprocessing        : 0.32
% 4.83/1.82  Parsing              : 0.17
% 4.83/1.82  CNF conversion       : 0.02
% 4.83/1.82  Main loop            : 0.74
% 4.83/1.82  Inferencing          : 0.28
% 4.83/1.82  Reduction            : 0.24
% 4.83/1.82  Demodulation         : 0.15
% 4.83/1.82  BG Simplification    : 0.03
% 4.83/1.82  Subsumption          : 0.15
% 4.83/1.82  Abstraction          : 0.05
% 4.83/1.82  MUC search           : 0.00
% 4.83/1.82  Cooper               : 0.00
% 4.83/1.82  Total                : 1.11
% 4.83/1.82  Index Insertion      : 0.00
% 4.83/1.82  Index Deletion       : 0.00
% 4.83/1.82  Index Matching       : 0.00
% 4.83/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

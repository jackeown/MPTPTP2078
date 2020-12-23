%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:07 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  194 (1281 expanded)
%              Number of leaves         :   40 ( 454 expanded)
%              Depth                    :   14
%              Number of atoms          :  464 (3307 expanded)
%              Number of equality atoms :   77 ( 534 expanded)
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

tff(f_163,negated_conjecture,(
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
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_75,axiom,(
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

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_145,axiom,(
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

tff(f_115,axiom,(
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

tff(c_69,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_560,plain,(
    ! [A_140] :
      ( u1_struct_0(A_140) = k2_struct_0(A_140)
      | ~ l1_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_566,plain,(
    ! [A_142] :
      ( u1_struct_0(A_142) = k2_struct_0(A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_18,c_560])).

tff(c_570,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_566])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_572,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_52])).

tff(c_62,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_83,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_84,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_90,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_94,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_90])).

tff(c_68,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_100,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68])).

tff(c_101,plain,(
    ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_100])).

tff(c_95,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52])).

tff(c_115,plain,(
    ! [B_58,A_59] :
      ( v1_subset_1(B_58,A_59)
      | B_58 = A_59
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_118,plain,
    ( v1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_95,c_115])).

tff(c_124,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_118])).

tff(c_20,plain,(
    ! [A_15] :
      ( v4_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_20])).

tff(c_140,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_136])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_70,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_131,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_94])).

tff(c_203,plain,(
    ! [A_75,B_76] :
      ( k2_pre_topc(A_75,B_76) = B_76
      | ~ v4_pre_topc(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_206,plain,(
    ! [B_76] :
      ( k2_pre_topc('#skF_3',B_76) = B_76
      | ~ v4_pre_topc(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_203])).

tff(c_214,plain,(
    ! [B_77] :
      ( k2_pre_topc('#skF_3',B_77) = B_77
      | ~ v4_pre_topc(B_77,'#skF_3')
      | ~ m1_subset_1(B_77,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_206])).

tff(c_218,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_214])).

tff(c_221,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_218])).

tff(c_222,plain,(
    ! [B_78,A_79] :
      ( v1_tops_1(B_78,A_79)
      | k2_pre_topc(A_79,B_78) != u1_struct_0(A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_225,plain,(
    ! [B_78] :
      ( v1_tops_1(B_78,'#skF_3')
      | k2_pre_topc('#skF_3',B_78) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_78,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_222])).

tff(c_237,plain,(
    ! [B_80] :
      ( v1_tops_1(B_80,'#skF_3')
      | k2_pre_topc('#skF_3',B_80) != '#skF_4'
      | ~ m1_subset_1(B_80,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_131,c_225])).

tff(c_241,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_237])).

tff(c_244,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_241])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_290,plain,(
    ! [B_91,A_92] :
      ( v2_tex_2(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v1_tdlat_3(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_293,plain,(
    ! [B_91] :
      ( v2_tex_2(B_91,'#skF_3')
      | ~ m1_subset_1(B_91,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_290])).

tff(c_299,plain,(
    ! [B_91] :
      ( v2_tex_2(B_91,'#skF_3')
      | ~ m1_subset_1(B_91,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_293])).

tff(c_302,plain,(
    ! [B_93] :
      ( v2_tex_2(B_93,'#skF_3')
      | ~ m1_subset_1(B_93,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_299])).

tff(c_307,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_302])).

tff(c_534,plain,(
    ! [B_137,A_138] :
      ( v3_tex_2(B_137,A_138)
      | ~ v2_tex_2(B_137,A_138)
      | ~ v1_tops_1(B_137,A_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_537,plain,(
    ! [B_137] :
      ( v3_tex_2(B_137,'#skF_3')
      | ~ v2_tex_2(B_137,'#skF_3')
      | ~ v1_tops_1(B_137,'#skF_3')
      | ~ m1_subset_1(B_137,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_534])).

tff(c_543,plain,(
    ! [B_137] :
      ( v3_tex_2(B_137,'#skF_3')
      | ~ v2_tex_2(B_137,'#skF_3')
      | ~ v1_tops_1(B_137,'#skF_3')
      | ~ m1_subset_1(B_137,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_537])).

tff(c_546,plain,(
    ! [B_139] :
      ( v3_tex_2(B_139,'#skF_3')
      | ~ v2_tex_2(B_139,'#skF_3')
      | ~ v1_tops_1(B_139,'#skF_3')
      | ~ m1_subset_1(B_139,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_543])).

tff(c_550,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_546])).

tff(c_553,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_307,c_550])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_553])).

tff(c_557,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_631,plain,(
    ! [B_163,A_164] :
      ( v2_tex_2(B_163,A_164)
      | ~ v3_tex_2(B_163,A_164)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_652,plain,(
    ! [A_167] :
      ( v2_tex_2(u1_struct_0(A_167),A_167)
      | ~ v3_tex_2(u1_struct_0(A_167),A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_70,c_631])).

tff(c_655,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_652])).

tff(c_657,plain,
    ( v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_570,c_655])).

tff(c_658,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_671,plain,(
    ! [A_169,B_170] :
      ( k2_pre_topc(A_169,B_170) = B_170
      | ~ v4_pre_topc(B_170,A_169)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_682,plain,(
    ! [A_171] :
      ( k2_pre_topc(A_171,u1_struct_0(A_171)) = u1_struct_0(A_171)
      | ~ v4_pre_topc(u1_struct_0(A_171),A_171)
      | ~ l1_pre_topc(A_171) ) ),
    inference(resolution,[status(thm)],[c_70,c_671])).

tff(c_685,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_682])).

tff(c_687,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_570,c_570,c_685])).

tff(c_699,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_702,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_699])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_702])).

tff(c_707,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_688,plain,(
    ! [B_172,A_173] :
      ( v1_tops_1(B_172,A_173)
      | k2_pre_topc(A_173,B_172) != u1_struct_0(A_173)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_727,plain,(
    ! [A_175] :
      ( v1_tops_1(u1_struct_0(A_175),A_175)
      | k2_pre_topc(A_175,u1_struct_0(A_175)) != u1_struct_0(A_175)
      | ~ l1_pre_topc(A_175) ) ),
    inference(resolution,[status(thm)],[c_70,c_688])).

tff(c_730,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_727])).

tff(c_732,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_707,c_570,c_570,c_730])).

tff(c_889,plain,(
    ! [B_207,A_208] :
      ( v2_tex_2(B_207,A_208)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208)
      | ~ v1_tdlat_3(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_892,plain,(
    ! [B_207] :
      ( v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_889])).

tff(c_898,plain,(
    ! [B_207] :
      ( v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_892])).

tff(c_901,plain,(
    ! [B_209] :
      ( v2_tex_2(B_209,'#skF_3')
      | ~ m1_subset_1(B_209,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_898])).

tff(c_911,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_901])).

tff(c_1143,plain,(
    ! [B_251,A_252] :
      ( v3_tex_2(B_251,A_252)
      | ~ v2_tex_2(B_251,A_252)
      | ~ v1_tops_1(B_251,A_252)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1146,plain,(
    ! [B_251] :
      ( v3_tex_2(B_251,'#skF_3')
      | ~ v2_tex_2(B_251,'#skF_3')
      | ~ v1_tops_1(B_251,'#skF_3')
      | ~ m1_subset_1(B_251,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_1143])).

tff(c_1152,plain,(
    ! [B_251] :
      ( v3_tex_2(B_251,'#skF_3')
      | ~ v2_tex_2(B_251,'#skF_3')
      | ~ v1_tops_1(B_251,'#skF_3')
      | ~ m1_subset_1(B_251,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1146])).

tff(c_1176,plain,(
    ! [B_254] :
      ( v3_tex_2(B_254,'#skF_3')
      | ~ v2_tex_2(B_254,'#skF_3')
      | ~ v1_tops_1(B_254,'#skF_3')
      | ~ m1_subset_1(B_254,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1152])).

tff(c_1183,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1176])).

tff(c_1189,plain,(
    v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_911,c_1183])).

tff(c_1191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_1189])).

tff(c_1192,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_1207,plain,(
    ! [A_256,B_257] :
      ( k2_pre_topc(A_256,B_257) = B_257
      | ~ v4_pre_topc(B_257,A_256)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1210,plain,(
    ! [B_257] :
      ( k2_pre_topc('#skF_3',B_257) = B_257
      | ~ v4_pre_topc(B_257,'#skF_3')
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_1207])).

tff(c_1249,plain,(
    ! [B_261] :
      ( k2_pre_topc('#skF_3',B_261) = B_261
      | ~ v4_pre_topc(B_261,'#skF_3')
      | ~ m1_subset_1(B_261,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1210])).

tff(c_1257,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_572,c_1249])).

tff(c_1261,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1257])).

tff(c_1285,plain,(
    ! [A_269,B_270] :
      ( k2_pre_topc(A_269,B_270) = u1_struct_0(A_269)
      | ~ v1_tops_1(B_270,A_269)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1288,plain,(
    ! [B_270] :
      ( k2_pre_topc('#skF_3',B_270) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_270,'#skF_3')
      | ~ m1_subset_1(B_270,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_1285])).

tff(c_1302,plain,(
    ! [B_272] :
      ( k2_pre_topc('#skF_3',B_272) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_272,'#skF_3')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_570,c_1288])).

tff(c_1310,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_572,c_1302])).

tff(c_1313,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1310])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_603,plain,(
    ! [C_154,A_155,B_156] :
      ( r2_hidden(C_154,A_155)
      | ~ r2_hidden(C_154,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_619,plain,(
    ! [A_160,B_161,A_162] :
      ( r2_hidden('#skF_1'(A_160,B_161),A_162)
      | ~ m1_subset_1(A_160,k1_zfmisc_1(A_162))
      | r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_6,c_603])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_642,plain,(
    ! [A_165,A_166] :
      ( ~ m1_subset_1(A_165,k1_zfmisc_1(A_166))
      | r1_tarski(A_165,A_166) ) ),
    inference(resolution,[status(thm)],[c_619,c_4])).

tff(c_649,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_572,c_642])).

tff(c_2971,plain,(
    ! [C_481,B_482,A_483] :
      ( C_481 = B_482
      | ~ r1_tarski(B_482,C_481)
      | ~ v2_tex_2(C_481,A_483)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(u1_struct_0(A_483)))
      | ~ v3_tex_2(B_482,A_483)
      | ~ m1_subset_1(B_482,k1_zfmisc_1(u1_struct_0(A_483)))
      | ~ l1_pre_topc(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2997,plain,(
    ! [A_483] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_483)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_483)))
      | ~ v3_tex_2('#skF_4',A_483)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_483)))
      | ~ l1_pre_topc(A_483) ) ),
    inference(resolution,[status(thm)],[c_649,c_2971])).

tff(c_3251,plain,(
    ! [A_521] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_521)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ v3_tex_2('#skF_4',A_521)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ l1_pre_topc(A_521) ) ),
    inference(splitLeft,[status(thm)],[c_2997])).

tff(c_3254,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_3251])).

tff(c_3257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_572,c_570,c_557,c_70,c_1192,c_3254])).

tff(c_3258,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2997])).

tff(c_1218,plain,(
    ! [A_258] :
      ( k2_pre_topc(A_258,u1_struct_0(A_258)) = u1_struct_0(A_258)
      | ~ v4_pre_topc(u1_struct_0(A_258),A_258)
      | ~ l1_pre_topc(A_258) ) ),
    inference(resolution,[status(thm)],[c_70,c_1207])).

tff(c_1221,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_1218])).

tff(c_1223,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_570,c_570,c_1221])).

tff(c_1224,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_1238,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1224])).

tff(c_1242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1238])).

tff(c_1243,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_1314,plain,(
    ! [B_273,A_274] :
      ( v1_tops_1(B_273,A_274)
      | k2_pre_topc(A_274,B_273) != u1_struct_0(A_274)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ l1_pre_topc(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1325,plain,(
    ! [A_275] :
      ( v1_tops_1(u1_struct_0(A_275),A_275)
      | k2_pre_topc(A_275,u1_struct_0(A_275)) != u1_struct_0(A_275)
      | ~ l1_pre_topc(A_275) ) ),
    inference(resolution,[status(thm)],[c_70,c_1314])).

tff(c_1331,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_1325])).

tff(c_1334,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1243,c_570,c_570,c_1331])).

tff(c_3317,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3258,c_1334])).

tff(c_3332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1313,c_3317])).

tff(c_3333,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1310])).

tff(c_3441,plain,(
    ! [B_541,A_542] :
      ( v4_pre_topc(B_541,A_542)
      | k2_pre_topc(A_542,B_541) != B_541
      | ~ v2_pre_topc(A_542)
      | ~ m1_subset_1(B_541,k1_zfmisc_1(u1_struct_0(A_542)))
      | ~ l1_pre_topc(A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3444,plain,(
    ! [B_541] :
      ( v4_pre_topc(B_541,'#skF_3')
      | k2_pre_topc('#skF_3',B_541) != B_541
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(B_541,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_3441])).

tff(c_3452,plain,(
    ! [B_543] :
      ( v4_pre_topc(B_543,'#skF_3')
      | k2_pre_topc('#skF_3',B_543) != B_543
      | ~ m1_subset_1(B_543,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_3444])).

tff(c_3455,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_572,c_3452])).

tff(c_3461,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3333,c_3455])).

tff(c_3462,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1261,c_3461])).

tff(c_3952,plain,(
    ! [C_616,B_617,A_618] :
      ( C_616 = B_617
      | ~ r1_tarski(B_617,C_616)
      | ~ v2_tex_2(C_616,A_618)
      | ~ m1_subset_1(C_616,k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ v3_tex_2(B_617,A_618)
      | ~ m1_subset_1(B_617,k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ l1_pre_topc(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3964,plain,(
    ! [A_618] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_618)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ v3_tex_2('#skF_4',A_618)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ l1_pre_topc(A_618) ) ),
    inference(resolution,[status(thm)],[c_649,c_3952])).

tff(c_3977,plain,(
    ! [A_619] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_619)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_619)))
      | ~ v3_tex_2('#skF_4',A_619)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_619)))
      | ~ l1_pre_topc(A_619) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3462,c_3964])).

tff(c_3980,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_3977])).

tff(c_3983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_572,c_570,c_557,c_70,c_1192,c_3980])).

tff(c_3984,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1257])).

tff(c_3990,plain,(
    ! [A_620,B_621] :
      ( k2_pre_topc(A_620,B_621) = u1_struct_0(A_620)
      | ~ v1_tops_1(B_621,A_620)
      | ~ m1_subset_1(B_621,k1_zfmisc_1(u1_struct_0(A_620)))
      | ~ l1_pre_topc(A_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3993,plain,(
    ! [B_621] :
      ( k2_pre_topc('#skF_3',B_621) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_621,'#skF_3')
      | ~ m1_subset_1(B_621,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_3990])).

tff(c_4007,plain,(
    ! [B_623] :
      ( k2_pre_topc('#skF_3',B_623) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_623,'#skF_3')
      | ~ m1_subset_1(B_623,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_570,c_3993])).

tff(c_4010,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_572,c_4007])).

tff(c_4016,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3984,c_4010])).

tff(c_4019,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4016])).

tff(c_4027,plain,(
    ! [B_628,A_629] :
      ( v1_tops_1(B_628,A_629)
      | k2_pre_topc(A_629,B_628) != u1_struct_0(A_629)
      | ~ m1_subset_1(B_628,k1_zfmisc_1(u1_struct_0(A_629)))
      | ~ l1_pre_topc(A_629) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4030,plain,(
    ! [B_628] :
      ( v1_tops_1(B_628,'#skF_3')
      | k2_pre_topc('#skF_3',B_628) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_628,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_4027])).

tff(c_4060,plain,(
    ! [B_633] :
      ( v1_tops_1(B_633,'#skF_3')
      | k2_pre_topc('#skF_3',B_633) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_633,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_570,c_4030])).

tff(c_4063,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_572,c_4060])).

tff(c_4069,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3984,c_4063])).

tff(c_4070,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4019,c_4069])).

tff(c_4618,plain,(
    ! [C_718,B_719,A_720] :
      ( C_718 = B_719
      | ~ r1_tarski(B_719,C_718)
      | ~ v2_tex_2(C_718,A_720)
      | ~ m1_subset_1(C_718,k1_zfmisc_1(u1_struct_0(A_720)))
      | ~ v3_tex_2(B_719,A_720)
      | ~ m1_subset_1(B_719,k1_zfmisc_1(u1_struct_0(A_720)))
      | ~ l1_pre_topc(A_720) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4628,plain,(
    ! [A_720] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_720)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_720)))
      | ~ v3_tex_2('#skF_4',A_720)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_720)))
      | ~ l1_pre_topc(A_720) ) ),
    inference(resolution,[status(thm)],[c_649,c_4618])).

tff(c_4667,plain,(
    ! [A_723] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_723)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_723)))
      | ~ v3_tex_2('#skF_4',A_723)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_723)))
      | ~ l1_pre_topc(A_723) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4070,c_4628])).

tff(c_4670,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_4667])).

tff(c_4673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_572,c_570,c_557,c_70,c_1192,c_4670])).

tff(c_4674,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4016])).

tff(c_556,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_571,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_556])).

tff(c_4685,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4674,c_571])).

tff(c_4694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_4685])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:07:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.15/2.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.42  
% 7.15/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.42  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.15/2.42  
% 7.15/2.42  %Foreground sorts:
% 7.15/2.42  
% 7.15/2.42  
% 7.15/2.42  %Background operators:
% 7.15/2.42  
% 7.15/2.42  
% 7.15/2.42  %Foreground operators:
% 7.15/2.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.15/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.15/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.15/2.42  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.15/2.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.15/2.42  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.15/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.15/2.42  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.15/2.42  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.15/2.42  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.15/2.42  tff('#skF_3', type, '#skF_3': $i).
% 7.15/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.15/2.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.15/2.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.15/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.15/2.42  tff('#skF_4', type, '#skF_4': $i).
% 7.15/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.15/2.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.15/2.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.15/2.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.15/2.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.15/2.42  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.15/2.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.15/2.42  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.15/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.15/2.42  
% 7.15/2.45  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.15/2.45  tff(f_46, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 7.15/2.45  tff(f_163, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 7.15/2.45  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.15/2.45  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.15/2.45  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 7.15/2.45  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 7.15/2.45  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.15/2.45  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.15/2.45  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 7.15/2.45  tff(f_129, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 7.15/2.45  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 7.15/2.45  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 7.15/2.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.15/2.45  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.15/2.45  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.15/2.45  tff(c_14, plain, (![A_12]: (~v1_subset_1(k2_subset_1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.15/2.45  tff(c_69, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 7.15/2.45  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.15/2.45  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.15/2.45  tff(c_560, plain, (![A_140]: (u1_struct_0(A_140)=k2_struct_0(A_140) | ~l1_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.15/2.45  tff(c_566, plain, (![A_142]: (u1_struct_0(A_142)=k2_struct_0(A_142) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_18, c_560])).
% 7.15/2.45  tff(c_570, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_566])).
% 7.15/2.45  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.15/2.45  tff(c_572, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_570, c_52])).
% 7.15/2.45  tff(c_62, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.15/2.45  tff(c_83, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 7.15/2.45  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.15/2.45  tff(c_84, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.15/2.45  tff(c_90, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_18, c_84])).
% 7.15/2.45  tff(c_94, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_90])).
% 7.15/2.45  tff(c_68, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.15/2.45  tff(c_100, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_68])).
% 7.15/2.45  tff(c_101, plain, (~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_83, c_100])).
% 7.15/2.45  tff(c_95, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_52])).
% 7.15/2.45  tff(c_115, plain, (![B_58, A_59]: (v1_subset_1(B_58, A_59) | B_58=A_59 | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.15/2.45  tff(c_118, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_95, c_115])).
% 7.15/2.45  tff(c_124, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_101, c_118])).
% 7.15/2.45  tff(c_20, plain, (![A_15]: (v4_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.15/2.45  tff(c_136, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_20])).
% 7.15/2.45  tff(c_140, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_136])).
% 7.15/2.45  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.15/2.45  tff(c_70, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 7.15/2.45  tff(c_131, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_94])).
% 7.15/2.45  tff(c_203, plain, (![A_75, B_76]: (k2_pre_topc(A_75, B_76)=B_76 | ~v4_pre_topc(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.15/2.45  tff(c_206, plain, (![B_76]: (k2_pre_topc('#skF_3', B_76)=B_76 | ~v4_pre_topc(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_203])).
% 7.15/2.45  tff(c_214, plain, (![B_77]: (k2_pre_topc('#skF_3', B_77)=B_77 | ~v4_pre_topc(B_77, '#skF_3') | ~m1_subset_1(B_77, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_206])).
% 7.15/2.45  tff(c_218, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_214])).
% 7.15/2.45  tff(c_221, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_218])).
% 7.15/2.45  tff(c_222, plain, (![B_78, A_79]: (v1_tops_1(B_78, A_79) | k2_pre_topc(A_79, B_78)!=u1_struct_0(A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.15/2.45  tff(c_225, plain, (![B_78]: (v1_tops_1(B_78, '#skF_3') | k2_pre_topc('#skF_3', B_78)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_78, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_222])).
% 7.15/2.45  tff(c_237, plain, (![B_80]: (v1_tops_1(B_80, '#skF_3') | k2_pre_topc('#skF_3', B_80)!='#skF_4' | ~m1_subset_1(B_80, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_131, c_225])).
% 7.15/2.45  tff(c_241, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_70, c_237])).
% 7.15/2.45  tff(c_244, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_241])).
% 7.15/2.45  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.15/2.45  tff(c_56, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.15/2.45  tff(c_290, plain, (![B_91, A_92]: (v2_tex_2(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v1_tdlat_3(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.15/2.45  tff(c_293, plain, (![B_91]: (v2_tex_2(B_91, '#skF_3') | ~m1_subset_1(B_91, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_290])).
% 7.15/2.45  tff(c_299, plain, (![B_91]: (v2_tex_2(B_91, '#skF_3') | ~m1_subset_1(B_91, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_293])).
% 7.15/2.45  tff(c_302, plain, (![B_93]: (v2_tex_2(B_93, '#skF_3') | ~m1_subset_1(B_93, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_299])).
% 7.15/2.45  tff(c_307, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_302])).
% 7.15/2.45  tff(c_534, plain, (![B_137, A_138]: (v3_tex_2(B_137, A_138) | ~v2_tex_2(B_137, A_138) | ~v1_tops_1(B_137, A_138) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.15/2.45  tff(c_537, plain, (![B_137]: (v3_tex_2(B_137, '#skF_3') | ~v2_tex_2(B_137, '#skF_3') | ~v1_tops_1(B_137, '#skF_3') | ~m1_subset_1(B_137, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_534])).
% 7.15/2.45  tff(c_543, plain, (![B_137]: (v3_tex_2(B_137, '#skF_3') | ~v2_tex_2(B_137, '#skF_3') | ~v1_tops_1(B_137, '#skF_3') | ~m1_subset_1(B_137, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_537])).
% 7.15/2.45  tff(c_546, plain, (![B_139]: (v3_tex_2(B_139, '#skF_3') | ~v2_tex_2(B_139, '#skF_3') | ~v1_tops_1(B_139, '#skF_3') | ~m1_subset_1(B_139, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_543])).
% 7.15/2.45  tff(c_550, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_546])).
% 7.15/2.45  tff(c_553, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_307, c_550])).
% 7.15/2.45  tff(c_555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_553])).
% 7.15/2.45  tff(c_557, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 7.15/2.45  tff(c_631, plain, (![B_163, A_164]: (v2_tex_2(B_163, A_164) | ~v3_tex_2(B_163, A_164) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.15/2.45  tff(c_652, plain, (![A_167]: (v2_tex_2(u1_struct_0(A_167), A_167) | ~v3_tex_2(u1_struct_0(A_167), A_167) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_70, c_631])).
% 7.15/2.45  tff(c_655, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_652])).
% 7.15/2.45  tff(c_657, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_570, c_655])).
% 7.15/2.45  tff(c_658, plain, (~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_657])).
% 7.15/2.45  tff(c_671, plain, (![A_169, B_170]: (k2_pre_topc(A_169, B_170)=B_170 | ~v4_pre_topc(B_170, A_169) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.15/2.45  tff(c_682, plain, (![A_171]: (k2_pre_topc(A_171, u1_struct_0(A_171))=u1_struct_0(A_171) | ~v4_pre_topc(u1_struct_0(A_171), A_171) | ~l1_pre_topc(A_171))), inference(resolution, [status(thm)], [c_70, c_671])).
% 7.15/2.45  tff(c_685, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_682])).
% 7.15/2.45  tff(c_687, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_570, c_570, c_685])).
% 7.15/2.45  tff(c_699, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_687])).
% 7.15/2.45  tff(c_702, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_699])).
% 7.15/2.45  tff(c_706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_702])).
% 7.15/2.45  tff(c_707, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_687])).
% 7.15/2.45  tff(c_688, plain, (![B_172, A_173]: (v1_tops_1(B_172, A_173) | k2_pre_topc(A_173, B_172)!=u1_struct_0(A_173) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.15/2.45  tff(c_727, plain, (![A_175]: (v1_tops_1(u1_struct_0(A_175), A_175) | k2_pre_topc(A_175, u1_struct_0(A_175))!=u1_struct_0(A_175) | ~l1_pre_topc(A_175))), inference(resolution, [status(thm)], [c_70, c_688])).
% 7.15/2.45  tff(c_730, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_727])).
% 7.15/2.45  tff(c_732, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_707, c_570, c_570, c_730])).
% 7.15/2.45  tff(c_889, plain, (![B_207, A_208]: (v2_tex_2(B_207, A_208) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208) | ~v1_tdlat_3(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.15/2.45  tff(c_892, plain, (![B_207]: (v2_tex_2(B_207, '#skF_3') | ~m1_subset_1(B_207, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_570, c_889])).
% 7.15/2.45  tff(c_898, plain, (![B_207]: (v2_tex_2(B_207, '#skF_3') | ~m1_subset_1(B_207, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_892])).
% 7.15/2.45  tff(c_901, plain, (![B_209]: (v2_tex_2(B_209, '#skF_3') | ~m1_subset_1(B_209, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_898])).
% 7.15/2.45  tff(c_911, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_70, c_901])).
% 7.15/2.45  tff(c_1143, plain, (![B_251, A_252]: (v3_tex_2(B_251, A_252) | ~v2_tex_2(B_251, A_252) | ~v1_tops_1(B_251, A_252) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.15/2.45  tff(c_1146, plain, (![B_251]: (v3_tex_2(B_251, '#skF_3') | ~v2_tex_2(B_251, '#skF_3') | ~v1_tops_1(B_251, '#skF_3') | ~m1_subset_1(B_251, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_570, c_1143])).
% 7.15/2.45  tff(c_1152, plain, (![B_251]: (v3_tex_2(B_251, '#skF_3') | ~v2_tex_2(B_251, '#skF_3') | ~v1_tops_1(B_251, '#skF_3') | ~m1_subset_1(B_251, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1146])).
% 7.15/2.45  tff(c_1176, plain, (![B_254]: (v3_tex_2(B_254, '#skF_3') | ~v2_tex_2(B_254, '#skF_3') | ~v1_tops_1(B_254, '#skF_3') | ~m1_subset_1(B_254, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_1152])).
% 7.15/2.45  tff(c_1183, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_70, c_1176])).
% 7.15/2.45  tff(c_1189, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_732, c_911, c_1183])).
% 7.15/2.45  tff(c_1191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_658, c_1189])).
% 7.15/2.45  tff(c_1192, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_657])).
% 7.15/2.45  tff(c_1207, plain, (![A_256, B_257]: (k2_pre_topc(A_256, B_257)=B_257 | ~v4_pre_topc(B_257, A_256) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.15/2.45  tff(c_1210, plain, (![B_257]: (k2_pre_topc('#skF_3', B_257)=B_257 | ~v4_pre_topc(B_257, '#skF_3') | ~m1_subset_1(B_257, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_570, c_1207])).
% 7.15/2.45  tff(c_1249, plain, (![B_261]: (k2_pre_topc('#skF_3', B_261)=B_261 | ~v4_pre_topc(B_261, '#skF_3') | ~m1_subset_1(B_261, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1210])).
% 7.15/2.45  tff(c_1257, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_572, c_1249])).
% 7.15/2.45  tff(c_1261, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1257])).
% 7.15/2.45  tff(c_1285, plain, (![A_269, B_270]: (k2_pre_topc(A_269, B_270)=u1_struct_0(A_269) | ~v1_tops_1(B_270, A_269) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.15/2.45  tff(c_1288, plain, (![B_270]: (k2_pre_topc('#skF_3', B_270)=u1_struct_0('#skF_3') | ~v1_tops_1(B_270, '#skF_3') | ~m1_subset_1(B_270, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_570, c_1285])).
% 7.15/2.45  tff(c_1302, plain, (![B_272]: (k2_pre_topc('#skF_3', B_272)=k2_struct_0('#skF_3') | ~v1_tops_1(B_272, '#skF_3') | ~m1_subset_1(B_272, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_570, c_1288])).
% 7.15/2.45  tff(c_1310, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_572, c_1302])).
% 7.15/2.45  tff(c_1313, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1310])).
% 7.15/2.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.15/2.45  tff(c_603, plain, (![C_154, A_155, B_156]: (r2_hidden(C_154, A_155) | ~r2_hidden(C_154, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.15/2.45  tff(c_619, plain, (![A_160, B_161, A_162]: (r2_hidden('#skF_1'(A_160, B_161), A_162) | ~m1_subset_1(A_160, k1_zfmisc_1(A_162)) | r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_6, c_603])).
% 7.15/2.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.15/2.45  tff(c_642, plain, (![A_165, A_166]: (~m1_subset_1(A_165, k1_zfmisc_1(A_166)) | r1_tarski(A_165, A_166))), inference(resolution, [status(thm)], [c_619, c_4])).
% 7.15/2.45  tff(c_649, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_572, c_642])).
% 7.15/2.45  tff(c_2971, plain, (![C_481, B_482, A_483]: (C_481=B_482 | ~r1_tarski(B_482, C_481) | ~v2_tex_2(C_481, A_483) | ~m1_subset_1(C_481, k1_zfmisc_1(u1_struct_0(A_483))) | ~v3_tex_2(B_482, A_483) | ~m1_subset_1(B_482, k1_zfmisc_1(u1_struct_0(A_483))) | ~l1_pre_topc(A_483))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.15/2.45  tff(c_2997, plain, (![A_483]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_483) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_483))) | ~v3_tex_2('#skF_4', A_483) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_483))) | ~l1_pre_topc(A_483))), inference(resolution, [status(thm)], [c_649, c_2971])).
% 7.15/2.45  tff(c_3251, plain, (![A_521]: (~v2_tex_2(k2_struct_0('#skF_3'), A_521) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_521))) | ~v3_tex_2('#skF_4', A_521) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_521))) | ~l1_pre_topc(A_521))), inference(splitLeft, [status(thm)], [c_2997])).
% 7.15/2.45  tff(c_3254, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_3251])).
% 7.15/2.45  tff(c_3257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_572, c_570, c_557, c_70, c_1192, c_3254])).
% 7.15/2.45  tff(c_3258, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2997])).
% 7.15/2.45  tff(c_1218, plain, (![A_258]: (k2_pre_topc(A_258, u1_struct_0(A_258))=u1_struct_0(A_258) | ~v4_pre_topc(u1_struct_0(A_258), A_258) | ~l1_pre_topc(A_258))), inference(resolution, [status(thm)], [c_70, c_1207])).
% 7.15/2.45  tff(c_1221, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_1218])).
% 7.15/2.45  tff(c_1223, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_570, c_570, c_1221])).
% 7.15/2.45  tff(c_1224, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1223])).
% 7.15/2.45  tff(c_1238, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1224])).
% 7.15/2.45  tff(c_1242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1238])).
% 7.15/2.45  tff(c_1243, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1223])).
% 7.15/2.45  tff(c_1314, plain, (![B_273, A_274]: (v1_tops_1(B_273, A_274) | k2_pre_topc(A_274, B_273)!=u1_struct_0(A_274) | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_274))) | ~l1_pre_topc(A_274))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.15/2.45  tff(c_1325, plain, (![A_275]: (v1_tops_1(u1_struct_0(A_275), A_275) | k2_pre_topc(A_275, u1_struct_0(A_275))!=u1_struct_0(A_275) | ~l1_pre_topc(A_275))), inference(resolution, [status(thm)], [c_70, c_1314])).
% 7.15/2.45  tff(c_1331, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_1325])).
% 7.15/2.45  tff(c_1334, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1243, c_570, c_570, c_1331])).
% 7.15/2.45  tff(c_3317, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3258, c_1334])).
% 7.15/2.45  tff(c_3332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1313, c_3317])).
% 7.15/2.45  tff(c_3333, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1310])).
% 7.15/2.45  tff(c_3441, plain, (![B_541, A_542]: (v4_pre_topc(B_541, A_542) | k2_pre_topc(A_542, B_541)!=B_541 | ~v2_pre_topc(A_542) | ~m1_subset_1(B_541, k1_zfmisc_1(u1_struct_0(A_542))) | ~l1_pre_topc(A_542))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.15/2.45  tff(c_3444, plain, (![B_541]: (v4_pre_topc(B_541, '#skF_3') | k2_pre_topc('#skF_3', B_541)!=B_541 | ~v2_pre_topc('#skF_3') | ~m1_subset_1(B_541, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_570, c_3441])).
% 7.15/2.45  tff(c_3452, plain, (![B_543]: (v4_pre_topc(B_543, '#skF_3') | k2_pre_topc('#skF_3', B_543)!=B_543 | ~m1_subset_1(B_543, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_3444])).
% 7.15/2.45  tff(c_3455, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_572, c_3452])).
% 7.15/2.45  tff(c_3461, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3333, c_3455])).
% 7.15/2.45  tff(c_3462, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1261, c_3461])).
% 7.15/2.45  tff(c_3952, plain, (![C_616, B_617, A_618]: (C_616=B_617 | ~r1_tarski(B_617, C_616) | ~v2_tex_2(C_616, A_618) | ~m1_subset_1(C_616, k1_zfmisc_1(u1_struct_0(A_618))) | ~v3_tex_2(B_617, A_618) | ~m1_subset_1(B_617, k1_zfmisc_1(u1_struct_0(A_618))) | ~l1_pre_topc(A_618))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.15/2.45  tff(c_3964, plain, (![A_618]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_618) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_618))) | ~v3_tex_2('#skF_4', A_618) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_618))) | ~l1_pre_topc(A_618))), inference(resolution, [status(thm)], [c_649, c_3952])).
% 7.15/2.45  tff(c_3977, plain, (![A_619]: (~v2_tex_2(k2_struct_0('#skF_3'), A_619) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_619))) | ~v3_tex_2('#skF_4', A_619) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_619))) | ~l1_pre_topc(A_619))), inference(negUnitSimplification, [status(thm)], [c_3462, c_3964])).
% 7.15/2.45  tff(c_3980, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_3977])).
% 7.15/2.45  tff(c_3983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_572, c_570, c_557, c_70, c_1192, c_3980])).
% 7.15/2.45  tff(c_3984, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1257])).
% 7.15/2.45  tff(c_3990, plain, (![A_620, B_621]: (k2_pre_topc(A_620, B_621)=u1_struct_0(A_620) | ~v1_tops_1(B_621, A_620) | ~m1_subset_1(B_621, k1_zfmisc_1(u1_struct_0(A_620))) | ~l1_pre_topc(A_620))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.15/2.45  tff(c_3993, plain, (![B_621]: (k2_pre_topc('#skF_3', B_621)=u1_struct_0('#skF_3') | ~v1_tops_1(B_621, '#skF_3') | ~m1_subset_1(B_621, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_570, c_3990])).
% 7.15/2.45  tff(c_4007, plain, (![B_623]: (k2_pre_topc('#skF_3', B_623)=k2_struct_0('#skF_3') | ~v1_tops_1(B_623, '#skF_3') | ~m1_subset_1(B_623, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_570, c_3993])).
% 7.15/2.45  tff(c_4010, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_572, c_4007])).
% 7.15/2.45  tff(c_4016, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3984, c_4010])).
% 7.15/2.45  tff(c_4019, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_4016])).
% 7.15/2.45  tff(c_4027, plain, (![B_628, A_629]: (v1_tops_1(B_628, A_629) | k2_pre_topc(A_629, B_628)!=u1_struct_0(A_629) | ~m1_subset_1(B_628, k1_zfmisc_1(u1_struct_0(A_629))) | ~l1_pre_topc(A_629))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.15/2.45  tff(c_4030, plain, (![B_628]: (v1_tops_1(B_628, '#skF_3') | k2_pre_topc('#skF_3', B_628)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_628, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_570, c_4027])).
% 7.15/2.45  tff(c_4060, plain, (![B_633]: (v1_tops_1(B_633, '#skF_3') | k2_pre_topc('#skF_3', B_633)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_633, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_570, c_4030])).
% 7.15/2.45  tff(c_4063, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_572, c_4060])).
% 7.15/2.45  tff(c_4069, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3984, c_4063])).
% 7.15/2.45  tff(c_4070, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4019, c_4069])).
% 7.15/2.45  tff(c_4618, plain, (![C_718, B_719, A_720]: (C_718=B_719 | ~r1_tarski(B_719, C_718) | ~v2_tex_2(C_718, A_720) | ~m1_subset_1(C_718, k1_zfmisc_1(u1_struct_0(A_720))) | ~v3_tex_2(B_719, A_720) | ~m1_subset_1(B_719, k1_zfmisc_1(u1_struct_0(A_720))) | ~l1_pre_topc(A_720))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.15/2.45  tff(c_4628, plain, (![A_720]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_720) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_720))) | ~v3_tex_2('#skF_4', A_720) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_720))) | ~l1_pre_topc(A_720))), inference(resolution, [status(thm)], [c_649, c_4618])).
% 7.15/2.45  tff(c_4667, plain, (![A_723]: (~v2_tex_2(k2_struct_0('#skF_3'), A_723) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_723))) | ~v3_tex_2('#skF_4', A_723) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_723))) | ~l1_pre_topc(A_723))), inference(negUnitSimplification, [status(thm)], [c_4070, c_4628])).
% 7.15/2.45  tff(c_4670, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_4667])).
% 7.15/2.45  tff(c_4673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_572, c_570, c_557, c_70, c_1192, c_4670])).
% 7.15/2.45  tff(c_4674, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_4016])).
% 7.15/2.45  tff(c_556, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 7.15/2.45  tff(c_571, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_570, c_556])).
% 7.15/2.45  tff(c_4685, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4674, c_571])).
% 7.15/2.45  tff(c_4694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_4685])).
% 7.15/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.45  
% 7.15/2.45  Inference rules
% 7.15/2.45  ----------------------
% 7.15/2.45  #Ref     : 0
% 7.15/2.45  #Sup     : 1022
% 7.15/2.45  #Fact    : 0
% 7.15/2.45  #Define  : 0
% 7.15/2.45  #Split   : 19
% 7.15/2.45  #Chain   : 0
% 7.15/2.45  #Close   : 0
% 7.15/2.45  
% 7.15/2.45  Ordering : KBO
% 7.15/2.45  
% 7.15/2.45  Simplification rules
% 7.15/2.45  ----------------------
% 7.15/2.45  #Subsume      : 364
% 7.15/2.45  #Demod        : 769
% 7.15/2.45  #Tautology    : 189
% 7.15/2.45  #SimpNegUnit  : 47
% 7.15/2.45  #BackRed      : 127
% 7.15/2.45  
% 7.15/2.45  #Partial instantiations: 0
% 7.15/2.45  #Strategies tried      : 1
% 7.15/2.45  
% 7.15/2.45  Timing (in seconds)
% 7.15/2.45  ----------------------
% 7.41/2.46  Preprocessing        : 0.35
% 7.41/2.46  Parsing              : 0.19
% 7.41/2.46  CNF conversion       : 0.03
% 7.41/2.46  Main loop            : 1.33
% 7.41/2.46  Inferencing          : 0.40
% 7.41/2.46  Reduction            : 0.37
% 7.41/2.46  Demodulation         : 0.23
% 7.41/2.46  BG Simplification    : 0.04
% 7.41/2.46  Subsumption          : 0.42
% 7.41/2.46  Abstraction          : 0.05
% 7.41/2.46  MUC search           : 0.00
% 7.41/2.46  Cooper               : 0.00
% 7.41/2.46  Total                : 1.74
% 7.41/2.46  Index Insertion      : 0.00
% 7.41/2.46  Index Deletion       : 0.00
% 7.41/2.46  Index Matching       : 0.00
% 7.41/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

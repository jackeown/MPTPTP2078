%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:29 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 309 expanded)
%              Number of leaves         :   33 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  193 (1175 expanded)
%              Number of equality atoms :   17 ( 116 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

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

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_123,axiom,(
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

tff(f_67,axiom,(
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

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_50,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_85,plain,(
    ! [A_43,B_44] :
      ( k2_pre_topc(A_43,B_44) = B_44
      | ~ v4_pre_topc(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_85])).

tff(c_99,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_94])).

tff(c_100,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_58,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_63,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_195,plain,(
    ! [B_64,A_65] :
      ( v4_pre_topc(B_64,A_65)
      | ~ v3_pre_topc(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ v3_tdlat_3(A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_204,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_195])).

tff(c_209,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_63,c_204])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_209])).

tff(c_212,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_220,plain,(
    ! [B_68,A_69] :
      ( v1_tops_1(B_68,A_69)
      | k2_pre_topc(A_69,B_68) != u1_struct_0(A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_229,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_220])).

tff(c_234,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_212,c_229])).

tff(c_250,plain,(
    u1_struct_0('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_235,plain,(
    ! [A_70,B_71] :
      ( k2_pre_topc(A_70,B_71) = u1_struct_0(A_70)
      | ~ v1_tops_1(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_244,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_235])).

tff(c_249,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_212,c_244])).

tff(c_251,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_249])).

tff(c_388,plain,(
    ! [B_98,A_99] :
      ( v1_tops_1(B_98,A_99)
      | ~ v3_tex_2(B_98,A_99)
      | ~ v3_pre_topc(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_397,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_388])).

tff(c_402,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_63,c_50,c_397])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_251,c_402])).

tff(c_406,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_48,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_408,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_48])).

tff(c_407,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_54])).

tff(c_70,plain,(
    ! [B_41,A_42] :
      ( v2_tex_2(B_41,A_42)
      | ~ v3_tex_2(B_41,A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_79,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_70])).

tff(c_84,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_79])).

tff(c_494,plain,(
    ! [A_107] :
      ( v1_tdlat_3(A_107)
      | ~ v2_tex_2(u1_struct_0(A_107),A_107)
      | ~ m1_subset_1(u1_struct_0(A_107),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_497,plain,
    ( v1_tdlat_3('#skF_4')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_494])).

tff(c_502,plain,
    ( v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_407,c_406,c_84,c_406,c_497])).

tff(c_503,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_502])).

tff(c_661,plain,(
    ! [B_135,A_136] :
      ( ~ v1_subset_1(B_135,u1_struct_0(A_136))
      | ~ v3_tex_2(B_135,A_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v1_tdlat_3(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_664,plain,(
    ! [B_135] :
      ( ~ v1_subset_1(B_135,u1_struct_0('#skF_4'))
      | ~ v3_tex_2(B_135,'#skF_4')
      | ~ m1_subset_1(B_135,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_661])).

tff(c_672,plain,(
    ! [B_135] :
      ( ~ v1_subset_1(B_135,'#skF_5')
      | ~ v3_tex_2(B_135,'#skF_4')
      | ~ m1_subset_1(B_135,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_503,c_56,c_406,c_664])).

tff(c_676,plain,(
    ! [B_137] :
      ( ~ v1_subset_1(B_137,'#skF_5')
      | ~ v3_tex_2(B_137,'#skF_4')
      | ~ m1_subset_1(B_137,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_672])).

tff(c_679,plain,
    ( ~ v1_subset_1('#skF_5','#skF_5')
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_407,c_676])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_408,c_679])).

tff(c_685,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_684,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_817,plain,(
    ! [B_165,A_166] :
      ( v3_pre_topc(B_165,A_166)
      | ~ v4_pre_topc(B_165,A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v3_tdlat_3(A_166)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_826,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_817])).

tff(c_831,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_684,c_826])).

tff(c_833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_831])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.48  
% 3.18/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.49  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 3.18/1.49  
% 3.18/1.49  %Foreground sorts:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Background operators:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Foreground operators:
% 3.18/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.18/1.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.18/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.49  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.18/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.18/1.49  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.18/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.49  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.18/1.49  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.18/1.49  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.18/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.49  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.18/1.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.49  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.18/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.18/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.18/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.18/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.49  
% 3.18/1.50  tff(f_162, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 3.18/1.50  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.18/1.50  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tdlat_3)).
% 3.18/1.50  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 3.18/1.50  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 3.18/1.50  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.18/1.50  tff(f_107, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 3.18/1.50  tff(f_140, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 3.18/1.50  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.18/1.50  tff(c_50, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.18/1.50  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.18/1.50  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.18/1.50  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.18/1.50  tff(c_85, plain, (![A_43, B_44]: (k2_pre_topc(A_43, B_44)=B_44 | ~v4_pre_topc(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.18/1.50  tff(c_94, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_85])).
% 3.18/1.50  tff(c_99, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_94])).
% 3.18/1.50  tff(c_100, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_99])).
% 3.18/1.50  tff(c_60, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.18/1.50  tff(c_58, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.18/1.50  tff(c_52, plain, (v4_pre_topc('#skF_5', '#skF_4') | v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.18/1.50  tff(c_63, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 3.18/1.50  tff(c_195, plain, (![B_64, A_65]: (v4_pre_topc(B_64, A_65) | ~v3_pre_topc(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~v3_tdlat_3(A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.18/1.50  tff(c_204, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_4') | ~v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_195])).
% 3.18/1.50  tff(c_209, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_63, c_204])).
% 3.18/1.50  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_209])).
% 3.18/1.50  tff(c_212, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_99])).
% 3.18/1.50  tff(c_220, plain, (![B_68, A_69]: (v1_tops_1(B_68, A_69) | k2_pre_topc(A_69, B_68)!=u1_struct_0(A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.50  tff(c_229, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_220])).
% 3.18/1.50  tff(c_234, plain, (v1_tops_1('#skF_5', '#skF_4') | u1_struct_0('#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_212, c_229])).
% 3.18/1.50  tff(c_250, plain, (u1_struct_0('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_234])).
% 3.18/1.50  tff(c_235, plain, (![A_70, B_71]: (k2_pre_topc(A_70, B_71)=u1_struct_0(A_70) | ~v1_tops_1(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.50  tff(c_244, plain, (k2_pre_topc('#skF_4', '#skF_5')=u1_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_235])).
% 3.18/1.50  tff(c_249, plain, (u1_struct_0('#skF_4')='#skF_5' | ~v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_212, c_244])).
% 3.18/1.50  tff(c_251, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_250, c_249])).
% 3.18/1.50  tff(c_388, plain, (![B_98, A_99]: (v1_tops_1(B_98, A_99) | ~v3_tex_2(B_98, A_99) | ~v3_pre_topc(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.50  tff(c_397, plain, (v1_tops_1('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_388])).
% 3.18/1.50  tff(c_402, plain, (v1_tops_1('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_63, c_50, c_397])).
% 3.18/1.50  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_251, c_402])).
% 3.18/1.50  tff(c_406, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_234])).
% 3.18/1.50  tff(c_48, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.18/1.50  tff(c_408, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_48])).
% 3.18/1.50  tff(c_407, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_54])).
% 3.18/1.50  tff(c_70, plain, (![B_41, A_42]: (v2_tex_2(B_41, A_42) | ~v3_tex_2(B_41, A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.18/1.50  tff(c_79, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_70])).
% 3.18/1.50  tff(c_84, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_79])).
% 3.18/1.50  tff(c_494, plain, (![A_107]: (v1_tdlat_3(A_107) | ~v2_tex_2(u1_struct_0(A_107), A_107) | ~m1_subset_1(u1_struct_0(A_107), k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.50  tff(c_497, plain, (v1_tdlat_3('#skF_4') | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_406, c_494])).
% 3.18/1.50  tff(c_502, plain, (v1_tdlat_3('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_407, c_406, c_84, c_406, c_497])).
% 3.18/1.50  tff(c_503, plain, (v1_tdlat_3('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_502])).
% 3.18/1.50  tff(c_661, plain, (![B_135, A_136]: (~v1_subset_1(B_135, u1_struct_0(A_136)) | ~v3_tex_2(B_135, A_136) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v1_tdlat_3(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.18/1.50  tff(c_664, plain, (![B_135]: (~v1_subset_1(B_135, u1_struct_0('#skF_4')) | ~v3_tex_2(B_135, '#skF_4') | ~m1_subset_1(B_135, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_661])).
% 3.18/1.50  tff(c_672, plain, (![B_135]: (~v1_subset_1(B_135, '#skF_5') | ~v3_tex_2(B_135, '#skF_4') | ~m1_subset_1(B_135, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_503, c_56, c_406, c_664])).
% 3.18/1.50  tff(c_676, plain, (![B_137]: (~v1_subset_1(B_137, '#skF_5') | ~v3_tex_2(B_137, '#skF_4') | ~m1_subset_1(B_137, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_672])).
% 3.18/1.50  tff(c_679, plain, (~v1_subset_1('#skF_5', '#skF_5') | ~v3_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_407, c_676])).
% 3.18/1.50  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_408, c_679])).
% 3.18/1.50  tff(c_685, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.18/1.50  tff(c_684, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.18/1.50  tff(c_817, plain, (![B_165, A_166]: (v3_pre_topc(B_165, A_166) | ~v4_pre_topc(B_165, A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~v3_tdlat_3(A_166) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.18/1.50  tff(c_826, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v4_pre_topc('#skF_5', '#skF_4') | ~v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_817])).
% 3.18/1.50  tff(c_831, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_684, c_826])).
% 3.18/1.50  tff(c_833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_831])).
% 3.18/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.50  
% 3.18/1.50  Inference rules
% 3.18/1.50  ----------------------
% 3.18/1.50  #Ref     : 0
% 3.18/1.50  #Sup     : 144
% 3.18/1.50  #Fact    : 0
% 3.18/1.50  #Define  : 0
% 3.18/1.50  #Split   : 5
% 3.18/1.50  #Chain   : 0
% 3.18/1.50  #Close   : 0
% 3.18/1.50  
% 3.18/1.50  Ordering : KBO
% 3.18/1.50  
% 3.18/1.50  Simplification rules
% 3.18/1.50  ----------------------
% 3.18/1.50  #Subsume      : 24
% 3.18/1.50  #Demod        : 148
% 3.18/1.50  #Tautology    : 50
% 3.18/1.50  #SimpNegUnit  : 14
% 3.18/1.50  #BackRed      : 2
% 3.18/1.50  
% 3.18/1.50  #Partial instantiations: 0
% 3.18/1.50  #Strategies tried      : 1
% 3.18/1.50  
% 3.18/1.50  Timing (in seconds)
% 3.18/1.50  ----------------------
% 3.18/1.50  Preprocessing        : 0.34
% 3.18/1.50  Parsing              : 0.18
% 3.18/1.50  CNF conversion       : 0.02
% 3.18/1.50  Main loop            : 0.37
% 3.18/1.50  Inferencing          : 0.15
% 3.18/1.50  Reduction            : 0.10
% 3.18/1.50  Demodulation         : 0.07
% 3.18/1.50  BG Simplification    : 0.02
% 3.18/1.51  Subsumption          : 0.06
% 3.18/1.51  Abstraction          : 0.02
% 3.18/1.51  MUC search           : 0.00
% 3.18/1.51  Cooper               : 0.00
% 3.36/1.51  Total                : 0.74
% 3.36/1.51  Index Insertion      : 0.00
% 3.36/1.51  Index Deletion       : 0.00
% 3.36/1.51  Index Matching       : 0.00
% 3.36/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

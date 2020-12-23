%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:28 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  159 (1477 expanded)
%              Number of leaves         :   43 ( 510 expanded)
%              Depth                    :   19
%              Number of atoms          :  388 (5696 expanded)
%              Number of equality atoms :   44 ( 628 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_200,negated_conjecture,(
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

tff(f_54,axiom,(
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

tff(f_113,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_161,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_178,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_89,axiom,(
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

tff(f_145,axiom,(
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

tff(f_126,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_72,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_78,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_76,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_242,plain,(
    ! [A_85,B_86] :
      ( k2_pre_topc(A_85,B_86) = B_86
      | ~ v4_pre_topc(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_261,plain,
    ( k2_pre_topc('#skF_6','#skF_7') = '#skF_7'
    | ~ v4_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_242])).

tff(c_273,plain,
    ( k2_pre_topc('#skF_6','#skF_7') = '#skF_7'
    | ~ v4_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_261])).

tff(c_275,plain,(
    ~ v4_pre_topc('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_82,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_80,plain,(
    v3_tdlat_3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_74,plain,
    ( v4_pre_topc('#skF_7','#skF_6')
    | v3_pre_topc('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_96,plain,(
    v3_pre_topc('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_572,plain,(
    ! [B_119,A_120] :
      ( v4_pre_topc(B_119,A_120)
      | ~ v3_pre_topc(B_119,A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ v3_tdlat_3(A_120)
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_591,plain,
    ( v4_pre_topc('#skF_7','#skF_6')
    | ~ v3_pre_topc('#skF_7','#skF_6')
    | ~ v3_tdlat_3('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_572])).

tff(c_603,plain,(
    v4_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_80,c_96,c_591])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_603])).

tff(c_606,plain,(
    k2_pre_topc('#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_654,plain,(
    ! [B_129,A_130] :
      ( v1_tops_1(B_129,A_130)
      | k2_pre_topc(A_130,B_129) != u1_struct_0(A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_673,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | k2_pre_topc('#skF_6','#skF_7') != u1_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_654])).

tff(c_685,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | u1_struct_0('#skF_6') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_606,c_673])).

tff(c_687,plain,(
    u1_struct_0('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_689,plain,(
    ! [A_132,B_133] :
      ( k2_pre_topc(A_132,B_133) = u1_struct_0(A_132)
      | ~ v1_tops_1(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_708,plain,
    ( k2_pre_topc('#skF_6','#skF_7') = u1_struct_0('#skF_6')
    | ~ v1_tops_1('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_689])).

tff(c_720,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ v1_tops_1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_606,c_708])).

tff(c_721,plain,(
    ~ v1_tops_1('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_687,c_720])).

tff(c_1399,plain,(
    ! [B_199,A_200] :
      ( v1_tops_1(B_199,A_200)
      | ~ v3_tex_2(B_199,A_200)
      | ~ v3_pre_topc(B_199,A_200)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1421,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | ~ v3_tex_2('#skF_7','#skF_6')
    | ~ v3_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_1399])).

tff(c_1434,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_96,c_72,c_1421])).

tff(c_1436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_721,c_1434])).

tff(c_1438,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_70,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1441,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_70])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_129,plain,(
    ! [A_70] :
      ( m1_subset_1('#skF_2'(A_70),k1_zfmisc_1(u1_struct_0(A_70)))
      | v1_tdlat_3(A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [A_70] :
      ( r1_tarski('#skF_2'(A_70),u1_struct_0(A_70))
      | v1_tdlat_3(A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_129,c_6])).

tff(c_1476,plain,
    ( r1_tarski('#skF_2'('#skF_6'),'#skF_7')
    | v1_tdlat_3('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_133])).

tff(c_1521,plain,
    ( r1_tarski('#skF_2'('#skF_6'),'#skF_7')
    | v1_tdlat_3('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_1476])).

tff(c_1537,plain,(
    v1_tdlat_3('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1521])).

tff(c_3013,plain,(
    ! [B_296,A_297] :
      ( ~ v1_subset_1(B_296,u1_struct_0(A_297))
      | ~ v3_tex_2(B_296,A_297)
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ l1_pre_topc(A_297)
      | ~ v1_tdlat_3(A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_3016,plain,(
    ! [B_296] :
      ( ~ v1_subset_1(B_296,u1_struct_0('#skF_6'))
      | ~ v3_tex_2(B_296,'#skF_6')
      | ~ m1_subset_1(B_296,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v1_tdlat_3('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_3013])).

tff(c_3038,plain,(
    ! [B_296] :
      ( ~ v1_subset_1(B_296,'#skF_7')
      | ~ v3_tex_2(B_296,'#skF_6')
      | ~ m1_subset_1(B_296,k1_zfmisc_1('#skF_7'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1537,c_78,c_1438,c_3016])).

tff(c_3046,plain,(
    ! [B_298] :
      ( ~ v1_subset_1(B_298,'#skF_7')
      | ~ v3_tex_2(B_298,'#skF_6')
      | ~ m1_subset_1(B_298,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3038])).

tff(c_3057,plain,
    ( ~ v1_subset_1('#skF_7','#skF_7')
    | ~ v3_tex_2('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_85,c_3046])).

tff(c_3063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1441,c_3057])).

tff(c_3065,plain,(
    ~ v1_tdlat_3('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1521])).

tff(c_38,plain,(
    ! [A_25] :
      ( m1_subset_1('#skF_2'(A_25),k1_zfmisc_1(u1_struct_0(A_25)))
      | v1_tdlat_3(A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1485,plain,
    ( m1_subset_1('#skF_2'('#skF_6'),k1_zfmisc_1('#skF_7'))
    | v1_tdlat_3('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_38])).

tff(c_1527,plain,
    ( m1_subset_1('#skF_2'('#skF_6'),k1_zfmisc_1('#skF_7'))
    | v1_tdlat_3('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_1485])).

tff(c_3066,plain,(
    m1_subset_1('#skF_2'('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_3065,c_1527])).

tff(c_14,plain,(
    ! [A_7,B_9] :
      ( k2_pre_topc(A_7,B_9) = B_9
      | ~ v4_pre_topc(B_9,A_7)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1458,plain,(
    ! [B_9] :
      ( k2_pre_topc('#skF_6',B_9) = B_9
      | ~ v4_pre_topc(B_9,'#skF_6')
      | ~ m1_subset_1(B_9,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_14])).

tff(c_3184,plain,(
    ! [B_308] :
      ( k2_pre_topc('#skF_6',B_308) = B_308
      | ~ v4_pre_topc(B_308,'#skF_6')
      | ~ m1_subset_1(B_308,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1458])).

tff(c_3200,plain,
    ( k2_pre_topc('#skF_6','#skF_2'('#skF_6')) = '#skF_2'('#skF_6')
    | ~ v4_pre_topc('#skF_2'('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3066,c_3184])).

tff(c_3205,plain,(
    ~ v4_pre_topc('#skF_2'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3200])).

tff(c_3206,plain,(
    ! [B_309,A_310] :
      ( v4_pre_topc(B_309,A_310)
      | k2_pre_topc(A_310,B_309) != B_309
      | ~ v2_pre_topc(A_310)
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3209,plain,(
    ! [B_309] :
      ( v4_pre_topc(B_309,'#skF_6')
      | k2_pre_topc('#skF_6',B_309) != B_309
      | ~ v2_pre_topc('#skF_6')
      | ~ m1_subset_1(B_309,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_3206])).

tff(c_3308,plain,(
    ! [B_313] :
      ( v4_pre_topc(B_313,'#skF_6')
      | k2_pre_topc('#skF_6',B_313) != B_313
      | ~ m1_subset_1(B_313,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_82,c_3209])).

tff(c_3314,plain,
    ( v4_pre_topc('#skF_2'('#skF_6'),'#skF_6')
    | k2_pre_topc('#skF_6','#skF_2'('#skF_6')) != '#skF_2'('#skF_6') ),
    inference(resolution,[status(thm)],[c_3066,c_3308])).

tff(c_3326,plain,(
    k2_pre_topc('#skF_6','#skF_2'('#skF_6')) != '#skF_2'('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_3205,c_3314])).

tff(c_3064,plain,(
    r1_tarski('#skF_2'('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1521])).

tff(c_165,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k2_pre_topc(A_75,B_76),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_173,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k2_pre_topc(A_75,B_76),u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_165,c_6])).

tff(c_1467,plain,(
    ! [B_76] :
      ( r1_tarski(k2_pre_topc('#skF_6',B_76),'#skF_7')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_173])).

tff(c_1515,plain,(
    ! [B_76] :
      ( r1_tarski(k2_pre_topc('#skF_6',B_76),'#skF_7')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1438,c_1467])).

tff(c_623,plain,(
    ! [A_122,B_123] :
      ( v4_pre_topc(k2_pre_topc(A_122,B_123),A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_641,plain,(
    ! [A_25] :
      ( v4_pre_topc(k2_pre_topc(A_25,'#skF_2'(A_25)),A_25)
      | v1_tdlat_3(A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_38,c_623])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k2_pre_topc(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1473,plain,(
    ! [B_6] :
      ( m1_subset_1(k2_pre_topc('#skF_6',B_6),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_10])).

tff(c_1519,plain,(
    ! [B_6] :
      ( m1_subset_1(k2_pre_topc('#skF_6',B_6),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_6,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1438,c_1473])).

tff(c_4128,plain,(
    ! [B_362] :
      ( k2_pre_topc('#skF_6',k2_pre_topc('#skF_6',B_362)) = k2_pre_topc('#skF_6',B_362)
      | ~ v4_pre_topc(k2_pre_topc('#skF_6',B_362),'#skF_6')
      | ~ m1_subset_1(B_362,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1519,c_3184])).

tff(c_4153,plain,
    ( k2_pre_topc('#skF_6',k2_pre_topc('#skF_6','#skF_2'('#skF_6'))) = k2_pre_topc('#skF_6','#skF_2'('#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_6'),k1_zfmisc_1('#skF_7'))
    | v1_tdlat_3('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_641,c_4128])).

tff(c_4175,plain,
    ( k2_pre_topc('#skF_6',k2_pre_topc('#skF_6','#skF_2'('#skF_6'))) = k2_pre_topc('#skF_6','#skF_2'('#skF_6'))
    | v1_tdlat_3('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_3066,c_4153])).

tff(c_4176,plain,(
    k2_pre_topc('#skF_6',k2_pre_topc('#skF_6','#skF_2'('#skF_6'))) = k2_pre_topc('#skF_6','#skF_2'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_3065,c_4175])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_644,plain,(
    ! [A_122,A_3] :
      ( v4_pre_topc(k2_pre_topc(A_122,A_3),A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | ~ r1_tarski(A_3,u1_struct_0(A_122)) ) ),
    inference(resolution,[status(thm)],[c_8,c_623])).

tff(c_4200,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_6','#skF_2'('#skF_6')),'#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | ~ r1_tarski(k2_pre_topc('#skF_6','#skF_2'('#skF_6')),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4176,c_644])).

tff(c_4228,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_6','#skF_2'('#skF_6')),'#skF_6')
    | ~ r1_tarski(k2_pre_topc('#skF_6','#skF_2'('#skF_6')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_82,c_78,c_4200])).

tff(c_4333,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_6','#skF_2'('#skF_6')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_4228])).

tff(c_4336,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1515,c_4333])).

tff(c_4340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3066,c_4336])).

tff(c_4342,plain,(
    r1_tarski(k2_pre_topc('#skF_6','#skF_2'('#skF_6')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4228])).

tff(c_134,plain,(
    ! [B_71,A_72] :
      ( v2_tex_2(B_71,A_72)
      | ~ v3_tex_2(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_150,plain,
    ( v2_tex_2('#skF_7','#skF_6')
    | ~ v3_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_134])).

tff(c_161,plain,(
    v2_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_150])).

tff(c_5974,plain,(
    ! [A_433,B_434,C_435] :
      ( k9_subset_1(u1_struct_0(A_433),B_434,k2_pre_topc(A_433,C_435)) = C_435
      | ~ r1_tarski(C_435,B_434)
      | ~ m1_subset_1(C_435,k1_zfmisc_1(u1_struct_0(A_433)))
      | ~ v2_tex_2(B_434,A_433)
      | ~ m1_subset_1(B_434,k1_zfmisc_1(u1_struct_0(A_433)))
      | ~ l1_pre_topc(A_433)
      | ~ v2_pre_topc(A_433)
      | v2_struct_0(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5980,plain,(
    ! [B_434,C_435] :
      ( k9_subset_1(u1_struct_0('#skF_6'),B_434,k2_pre_topc('#skF_6',C_435)) = C_435
      | ~ r1_tarski(C_435,B_434)
      | ~ m1_subset_1(C_435,k1_zfmisc_1('#skF_7'))
      | ~ v2_tex_2(B_434,'#skF_6')
      | ~ m1_subset_1(B_434,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_5974])).

tff(c_5998,plain,(
    ! [B_434,C_435] :
      ( k9_subset_1('#skF_7',B_434,k2_pre_topc('#skF_6',C_435)) = C_435
      | ~ r1_tarski(C_435,B_434)
      | ~ m1_subset_1(C_435,k1_zfmisc_1('#skF_7'))
      | ~ v2_tex_2(B_434,'#skF_6')
      | ~ m1_subset_1(B_434,k1_zfmisc_1('#skF_7'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_1438,c_1438,c_5980])).

tff(c_6009,plain,(
    ! [B_436,C_437] :
      ( k9_subset_1('#skF_7',B_436,k2_pre_topc('#skF_6',C_437)) = C_437
      | ~ r1_tarski(C_437,B_436)
      | ~ m1_subset_1(C_437,k1_zfmisc_1('#skF_7'))
      | ~ v2_tex_2(B_436,'#skF_6')
      | ~ m1_subset_1(B_436,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5998])).

tff(c_6937,plain,(
    ! [B_481,A_482] :
      ( k9_subset_1('#skF_7',B_481,k2_pre_topc('#skF_6',A_482)) = A_482
      | ~ r1_tarski(A_482,B_481)
      | ~ v2_tex_2(B_481,'#skF_6')
      | ~ m1_subset_1(B_481,k1_zfmisc_1('#skF_7'))
      | ~ r1_tarski(A_482,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8,c_6009])).

tff(c_6953,plain,(
    ! [A_482] :
      ( k9_subset_1('#skF_7','#skF_7',k2_pre_topc('#skF_6',A_482)) = A_482
      | ~ v2_tex_2('#skF_7','#skF_6')
      | ~ r1_tarski(A_482,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_85,c_6937])).

tff(c_6963,plain,(
    ! [A_483] :
      ( k9_subset_1('#skF_7','#skF_7',k2_pre_topc('#skF_6',A_483)) = A_483
      | ~ r1_tarski(A_483,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_6953])).

tff(c_6993,plain,
    ( k9_subset_1('#skF_7','#skF_7',k2_pre_topc('#skF_6','#skF_2'('#skF_6'))) = k2_pre_topc('#skF_6','#skF_2'('#skF_6'))
    | ~ r1_tarski(k2_pre_topc('#skF_6','#skF_2'('#skF_6')),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4176,c_6963])).

tff(c_7007,plain,(
    k9_subset_1('#skF_7','#skF_7',k2_pre_topc('#skF_6','#skF_2'('#skF_6'))) = k2_pre_topc('#skF_6','#skF_2'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4342,c_6993])).

tff(c_6962,plain,(
    ! [A_482] :
      ( k9_subset_1('#skF_7','#skF_7',k2_pre_topc('#skF_6',A_482)) = A_482
      | ~ r1_tarski(A_482,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_6953])).

tff(c_7013,plain,
    ( k2_pre_topc('#skF_6','#skF_2'('#skF_6')) = '#skF_2'('#skF_6')
    | ~ r1_tarski('#skF_2'('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_7007,c_6962])).

tff(c_7020,plain,(
    k2_pre_topc('#skF_6','#skF_2'('#skF_6')) = '#skF_2'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3064,c_7013])).

tff(c_7022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3326,c_7020])).

tff(c_7024,plain,(
    v4_pre_topc('#skF_2'('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3200])).

tff(c_7490,plain,(
    ! [B_510,A_511] :
      ( v3_pre_topc(B_510,A_511)
      | ~ v4_pre_topc(B_510,A_511)
      | ~ m1_subset_1(B_510,k1_zfmisc_1(u1_struct_0(A_511)))
      | ~ v3_tdlat_3(A_511)
      | ~ l1_pre_topc(A_511)
      | ~ v2_pre_topc(A_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_7493,plain,(
    ! [B_510] :
      ( v3_pre_topc(B_510,'#skF_6')
      | ~ v4_pre_topc(B_510,'#skF_6')
      | ~ m1_subset_1(B_510,k1_zfmisc_1('#skF_7'))
      | ~ v3_tdlat_3('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_7490])).

tff(c_7522,plain,(
    ! [B_512] :
      ( v3_pre_topc(B_512,'#skF_6')
      | ~ v4_pre_topc(B_512,'#skF_6')
      | ~ m1_subset_1(B_512,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_80,c_7493])).

tff(c_7528,plain,
    ( v3_pre_topc('#skF_2'('#skF_6'),'#skF_6')
    | ~ v4_pre_topc('#skF_2'('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3066,c_7522])).

tff(c_7540,plain,(
    v3_pre_topc('#skF_2'('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7024,c_7528])).

tff(c_36,plain,(
    ! [A_25] :
      ( ~ v3_pre_topc('#skF_2'(A_25),A_25)
      | v1_tdlat_3(A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7550,plain,
    ( v1_tdlat_3('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_7540,c_36])).

tff(c_7556,plain,(
    v1_tdlat_3('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_7550])).

tff(c_7558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3065,c_7556])).

tff(c_7560,plain,(
    ~ v3_pre_topc('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_7559,plain,(
    v4_pre_topc('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_8126,plain,(
    ! [B_582,A_583] :
      ( v3_pre_topc(B_582,A_583)
      | ~ v4_pre_topc(B_582,A_583)
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0(A_583)))
      | ~ v3_tdlat_3(A_583)
      | ~ l1_pre_topc(A_583)
      | ~ v2_pre_topc(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8145,plain,
    ( v3_pre_topc('#skF_7','#skF_6')
    | ~ v4_pre_topc('#skF_7','#skF_6')
    | ~ v3_tdlat_3('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_8126])).

tff(c_8157,plain,(
    v3_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_80,c_7559,c_8145])).

tff(c_8159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7560,c_8157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:16:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.61  
% 7.79/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.61  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_1 > #skF_5
% 7.79/2.61  
% 7.79/2.61  %Foreground sorts:
% 7.79/2.61  
% 7.79/2.61  
% 7.79/2.61  %Background operators:
% 7.79/2.61  
% 7.79/2.61  
% 7.79/2.61  %Foreground operators:
% 7.79/2.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.79/2.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.79/2.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.79/2.61  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.79/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.79/2.61  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.79/2.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.79/2.61  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.79/2.61  tff('#skF_7', type, '#skF_7': $i).
% 7.79/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.79/2.61  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.79/2.61  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.79/2.61  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.79/2.61  tff('#skF_6', type, '#skF_6': $i).
% 7.79/2.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.79/2.61  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 7.79/2.61  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.79/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.79/2.61  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.79/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.79/2.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.79/2.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.79/2.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.79/2.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.79/2.61  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.79/2.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.79/2.61  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.79/2.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.79/2.61  
% 7.79/2.63  tff(f_200, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 7.79/2.63  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.79/2.63  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tdlat_3)).
% 7.79/2.63  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 7.79/2.63  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 7.79/2.63  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.79/2.63  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.79/2.63  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 7.79/2.63  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.79/2.63  tff(f_178, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 7.79/2.63  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.79/2.63  tff(f_62, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 7.79/2.63  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 7.79/2.63  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 7.79/2.63  tff(f_126, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 7.79/2.63  tff(c_72, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.79/2.63  tff(c_84, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.79/2.63  tff(c_78, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.79/2.63  tff(c_76, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.79/2.63  tff(c_242, plain, (![A_85, B_86]: (k2_pre_topc(A_85, B_86)=B_86 | ~v4_pre_topc(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.79/2.63  tff(c_261, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7' | ~v4_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_76, c_242])).
% 7.79/2.63  tff(c_273, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7' | ~v4_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_261])).
% 7.79/2.63  tff(c_275, plain, (~v4_pre_topc('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_273])).
% 7.79/2.63  tff(c_82, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.79/2.63  tff(c_80, plain, (v3_tdlat_3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.79/2.63  tff(c_74, plain, (v4_pre_topc('#skF_7', '#skF_6') | v3_pre_topc('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.79/2.63  tff(c_96, plain, (v3_pre_topc('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_74])).
% 7.79/2.63  tff(c_572, plain, (![B_119, A_120]: (v4_pre_topc(B_119, A_120) | ~v3_pre_topc(B_119, A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~v3_tdlat_3(A_120) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.79/2.63  tff(c_591, plain, (v4_pre_topc('#skF_7', '#skF_6') | ~v3_pre_topc('#skF_7', '#skF_6') | ~v3_tdlat_3('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_76, c_572])).
% 7.79/2.63  tff(c_603, plain, (v4_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_80, c_96, c_591])).
% 7.79/2.63  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_603])).
% 7.79/2.63  tff(c_606, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_273])).
% 7.79/2.63  tff(c_654, plain, (![B_129, A_130]: (v1_tops_1(B_129, A_130) | k2_pre_topc(A_130, B_129)!=u1_struct_0(A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.79/2.63  tff(c_673, plain, (v1_tops_1('#skF_7', '#skF_6') | k2_pre_topc('#skF_6', '#skF_7')!=u1_struct_0('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_76, c_654])).
% 7.79/2.63  tff(c_685, plain, (v1_tops_1('#skF_7', '#skF_6') | u1_struct_0('#skF_6')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_606, c_673])).
% 7.79/2.63  tff(c_687, plain, (u1_struct_0('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_685])).
% 7.79/2.63  tff(c_689, plain, (![A_132, B_133]: (k2_pre_topc(A_132, B_133)=u1_struct_0(A_132) | ~v1_tops_1(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.79/2.63  tff(c_708, plain, (k2_pre_topc('#skF_6', '#skF_7')=u1_struct_0('#skF_6') | ~v1_tops_1('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_76, c_689])).
% 7.79/2.63  tff(c_720, plain, (u1_struct_0('#skF_6')='#skF_7' | ~v1_tops_1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_606, c_708])).
% 7.79/2.63  tff(c_721, plain, (~v1_tops_1('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_687, c_720])).
% 7.79/2.63  tff(c_1399, plain, (![B_199, A_200]: (v1_tops_1(B_199, A_200) | ~v3_tex_2(B_199, A_200) | ~v3_pre_topc(B_199, A_200) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.79/2.63  tff(c_1421, plain, (v1_tops_1('#skF_7', '#skF_6') | ~v3_tex_2('#skF_7', '#skF_6') | ~v3_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_76, c_1399])).
% 7.79/2.63  tff(c_1434, plain, (v1_tops_1('#skF_7', '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_96, c_72, c_1421])).
% 7.79/2.64  tff(c_1436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_721, c_1434])).
% 7.79/2.64  tff(c_1438, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_685])).
% 7.79/2.64  tff(c_70, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.79/2.64  tff(c_1441, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1438, c_70])).
% 7.79/2.64  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.79/2.64  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.79/2.64  tff(c_85, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 7.79/2.64  tff(c_129, plain, (![A_70]: (m1_subset_1('#skF_2'(A_70), k1_zfmisc_1(u1_struct_0(A_70))) | v1_tdlat_3(A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.79/2.64  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.79/2.64  tff(c_133, plain, (![A_70]: (r1_tarski('#skF_2'(A_70), u1_struct_0(A_70)) | v1_tdlat_3(A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(resolution, [status(thm)], [c_129, c_6])).
% 7.79/2.64  tff(c_1476, plain, (r1_tarski('#skF_2'('#skF_6'), '#skF_7') | v1_tdlat_3('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1438, c_133])).
% 7.79/2.64  tff(c_1521, plain, (r1_tarski('#skF_2'('#skF_6'), '#skF_7') | v1_tdlat_3('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_1476])).
% 7.79/2.64  tff(c_1537, plain, (v1_tdlat_3('#skF_6')), inference(splitLeft, [status(thm)], [c_1521])).
% 7.79/2.64  tff(c_3013, plain, (![B_296, A_297]: (~v1_subset_1(B_296, u1_struct_0(A_297)) | ~v3_tex_2(B_296, A_297) | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0(A_297))) | ~l1_pre_topc(A_297) | ~v1_tdlat_3(A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.79/2.64  tff(c_3016, plain, (![B_296]: (~v1_subset_1(B_296, u1_struct_0('#skF_6')) | ~v3_tex_2(B_296, '#skF_6') | ~m1_subset_1(B_296, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6') | ~v1_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1438, c_3013])).
% 7.79/2.64  tff(c_3038, plain, (![B_296]: (~v1_subset_1(B_296, '#skF_7') | ~v3_tex_2(B_296, '#skF_6') | ~m1_subset_1(B_296, k1_zfmisc_1('#skF_7')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1537, c_78, c_1438, c_3016])).
% 7.79/2.64  tff(c_3046, plain, (![B_298]: (~v1_subset_1(B_298, '#skF_7') | ~v3_tex_2(B_298, '#skF_6') | ~m1_subset_1(B_298, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_84, c_3038])).
% 7.79/2.64  tff(c_3057, plain, (~v1_subset_1('#skF_7', '#skF_7') | ~v3_tex_2('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_85, c_3046])).
% 7.79/2.64  tff(c_3063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1441, c_3057])).
% 7.79/2.64  tff(c_3065, plain, (~v1_tdlat_3('#skF_6')), inference(splitRight, [status(thm)], [c_1521])).
% 7.79/2.64  tff(c_38, plain, (![A_25]: (m1_subset_1('#skF_2'(A_25), k1_zfmisc_1(u1_struct_0(A_25))) | v1_tdlat_3(A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.79/2.64  tff(c_1485, plain, (m1_subset_1('#skF_2'('#skF_6'), k1_zfmisc_1('#skF_7')) | v1_tdlat_3('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1438, c_38])).
% 7.79/2.64  tff(c_1527, plain, (m1_subset_1('#skF_2'('#skF_6'), k1_zfmisc_1('#skF_7')) | v1_tdlat_3('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_1485])).
% 7.79/2.64  tff(c_3066, plain, (m1_subset_1('#skF_2'('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_3065, c_1527])).
% 7.79/2.64  tff(c_14, plain, (![A_7, B_9]: (k2_pre_topc(A_7, B_9)=B_9 | ~v4_pre_topc(B_9, A_7) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.79/2.64  tff(c_1458, plain, (![B_9]: (k2_pre_topc('#skF_6', B_9)=B_9 | ~v4_pre_topc(B_9, '#skF_6') | ~m1_subset_1(B_9, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1438, c_14])).
% 7.79/2.64  tff(c_3184, plain, (![B_308]: (k2_pre_topc('#skF_6', B_308)=B_308 | ~v4_pre_topc(B_308, '#skF_6') | ~m1_subset_1(B_308, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1458])).
% 7.79/2.64  tff(c_3200, plain, (k2_pre_topc('#skF_6', '#skF_2'('#skF_6'))='#skF_2'('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_3066, c_3184])).
% 7.79/2.64  tff(c_3205, plain, (~v4_pre_topc('#skF_2'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3200])).
% 7.79/2.64  tff(c_3206, plain, (![B_309, A_310]: (v4_pre_topc(B_309, A_310) | k2_pre_topc(A_310, B_309)!=B_309 | ~v2_pre_topc(A_310) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.79/2.64  tff(c_3209, plain, (![B_309]: (v4_pre_topc(B_309, '#skF_6') | k2_pre_topc('#skF_6', B_309)!=B_309 | ~v2_pre_topc('#skF_6') | ~m1_subset_1(B_309, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1438, c_3206])).
% 7.79/2.64  tff(c_3308, plain, (![B_313]: (v4_pre_topc(B_313, '#skF_6') | k2_pre_topc('#skF_6', B_313)!=B_313 | ~m1_subset_1(B_313, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_82, c_3209])).
% 7.79/2.64  tff(c_3314, plain, (v4_pre_topc('#skF_2'('#skF_6'), '#skF_6') | k2_pre_topc('#skF_6', '#skF_2'('#skF_6'))!='#skF_2'('#skF_6')), inference(resolution, [status(thm)], [c_3066, c_3308])).
% 7.79/2.64  tff(c_3326, plain, (k2_pre_topc('#skF_6', '#skF_2'('#skF_6'))!='#skF_2'('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_3205, c_3314])).
% 7.79/2.64  tff(c_3064, plain, (r1_tarski('#skF_2'('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_1521])).
% 7.79/2.64  tff(c_165, plain, (![A_75, B_76]: (m1_subset_1(k2_pre_topc(A_75, B_76), k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.79/2.64  tff(c_173, plain, (![A_75, B_76]: (r1_tarski(k2_pre_topc(A_75, B_76), u1_struct_0(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_165, c_6])).
% 7.79/2.64  tff(c_1467, plain, (![B_76]: (r1_tarski(k2_pre_topc('#skF_6', B_76), '#skF_7') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1438, c_173])).
% 7.79/2.64  tff(c_1515, plain, (![B_76]: (r1_tarski(k2_pre_topc('#skF_6', B_76), '#skF_7') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1438, c_1467])).
% 7.79/2.64  tff(c_623, plain, (![A_122, B_123]: (v4_pre_topc(k2_pre_topc(A_122, B_123), A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.79/2.64  tff(c_641, plain, (![A_25]: (v4_pre_topc(k2_pre_topc(A_25, '#skF_2'(A_25)), A_25) | v1_tdlat_3(A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(resolution, [status(thm)], [c_38, c_623])).
% 7.79/2.64  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k2_pre_topc(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.79/2.64  tff(c_1473, plain, (![B_6]: (m1_subset_1(k2_pre_topc('#skF_6', B_6), k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1438, c_10])).
% 7.79/2.64  tff(c_1519, plain, (![B_6]: (m1_subset_1(k2_pre_topc('#skF_6', B_6), k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_6, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1438, c_1473])).
% 7.79/2.64  tff(c_4128, plain, (![B_362]: (k2_pre_topc('#skF_6', k2_pre_topc('#skF_6', B_362))=k2_pre_topc('#skF_6', B_362) | ~v4_pre_topc(k2_pre_topc('#skF_6', B_362), '#skF_6') | ~m1_subset_1(B_362, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_1519, c_3184])).
% 7.79/2.64  tff(c_4153, plain, (k2_pre_topc('#skF_6', k2_pre_topc('#skF_6', '#skF_2'('#skF_6')))=k2_pre_topc('#skF_6', '#skF_2'('#skF_6')) | ~m1_subset_1('#skF_2'('#skF_6'), k1_zfmisc_1('#skF_7')) | v1_tdlat_3('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_641, c_4128])).
% 7.79/2.64  tff(c_4175, plain, (k2_pre_topc('#skF_6', k2_pre_topc('#skF_6', '#skF_2'('#skF_6')))=k2_pre_topc('#skF_6', '#skF_2'('#skF_6')) | v1_tdlat_3('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_3066, c_4153])).
% 7.79/2.64  tff(c_4176, plain, (k2_pre_topc('#skF_6', k2_pre_topc('#skF_6', '#skF_2'('#skF_6')))=k2_pre_topc('#skF_6', '#skF_2'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_3065, c_4175])).
% 7.79/2.64  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.79/2.64  tff(c_644, plain, (![A_122, A_3]: (v4_pre_topc(k2_pre_topc(A_122, A_3), A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | ~r1_tarski(A_3, u1_struct_0(A_122)))), inference(resolution, [status(thm)], [c_8, c_623])).
% 7.79/2.64  tff(c_4200, plain, (v4_pre_topc(k2_pre_topc('#skF_6', '#skF_2'('#skF_6')), '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | ~r1_tarski(k2_pre_topc('#skF_6', '#skF_2'('#skF_6')), u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4176, c_644])).
% 7.79/2.64  tff(c_4228, plain, (v4_pre_topc(k2_pre_topc('#skF_6', '#skF_2'('#skF_6')), '#skF_6') | ~r1_tarski(k2_pre_topc('#skF_6', '#skF_2'('#skF_6')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1438, c_82, c_78, c_4200])).
% 7.79/2.64  tff(c_4333, plain, (~r1_tarski(k2_pre_topc('#skF_6', '#skF_2'('#skF_6')), '#skF_7')), inference(splitLeft, [status(thm)], [c_4228])).
% 7.79/2.64  tff(c_4336, plain, (~m1_subset_1('#skF_2'('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_1515, c_4333])).
% 7.79/2.64  tff(c_4340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3066, c_4336])).
% 7.79/2.64  tff(c_4342, plain, (r1_tarski(k2_pre_topc('#skF_6', '#skF_2'('#skF_6')), '#skF_7')), inference(splitRight, [status(thm)], [c_4228])).
% 7.79/2.64  tff(c_134, plain, (![B_71, A_72]: (v2_tex_2(B_71, A_72) | ~v3_tex_2(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.79/2.64  tff(c_150, plain, (v2_tex_2('#skF_7', '#skF_6') | ~v3_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_76, c_134])).
% 7.79/2.64  tff(c_161, plain, (v2_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_150])).
% 7.79/2.64  tff(c_5974, plain, (![A_433, B_434, C_435]: (k9_subset_1(u1_struct_0(A_433), B_434, k2_pre_topc(A_433, C_435))=C_435 | ~r1_tarski(C_435, B_434) | ~m1_subset_1(C_435, k1_zfmisc_1(u1_struct_0(A_433))) | ~v2_tex_2(B_434, A_433) | ~m1_subset_1(B_434, k1_zfmisc_1(u1_struct_0(A_433))) | ~l1_pre_topc(A_433) | ~v2_pre_topc(A_433) | v2_struct_0(A_433))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.79/2.64  tff(c_5980, plain, (![B_434, C_435]: (k9_subset_1(u1_struct_0('#skF_6'), B_434, k2_pre_topc('#skF_6', C_435))=C_435 | ~r1_tarski(C_435, B_434) | ~m1_subset_1(C_435, k1_zfmisc_1('#skF_7')) | ~v2_tex_2(B_434, '#skF_6') | ~m1_subset_1(B_434, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1438, c_5974])).
% 7.79/2.64  tff(c_5998, plain, (![B_434, C_435]: (k9_subset_1('#skF_7', B_434, k2_pre_topc('#skF_6', C_435))=C_435 | ~r1_tarski(C_435, B_434) | ~m1_subset_1(C_435, k1_zfmisc_1('#skF_7')) | ~v2_tex_2(B_434, '#skF_6') | ~m1_subset_1(B_434, k1_zfmisc_1('#skF_7')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_1438, c_1438, c_5980])).
% 7.79/2.64  tff(c_6009, plain, (![B_436, C_437]: (k9_subset_1('#skF_7', B_436, k2_pre_topc('#skF_6', C_437))=C_437 | ~r1_tarski(C_437, B_436) | ~m1_subset_1(C_437, k1_zfmisc_1('#skF_7')) | ~v2_tex_2(B_436, '#skF_6') | ~m1_subset_1(B_436, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_84, c_5998])).
% 7.79/2.64  tff(c_6937, plain, (![B_481, A_482]: (k9_subset_1('#skF_7', B_481, k2_pre_topc('#skF_6', A_482))=A_482 | ~r1_tarski(A_482, B_481) | ~v2_tex_2(B_481, '#skF_6') | ~m1_subset_1(B_481, k1_zfmisc_1('#skF_7')) | ~r1_tarski(A_482, '#skF_7'))), inference(resolution, [status(thm)], [c_8, c_6009])).
% 7.79/2.64  tff(c_6953, plain, (![A_482]: (k9_subset_1('#skF_7', '#skF_7', k2_pre_topc('#skF_6', A_482))=A_482 | ~v2_tex_2('#skF_7', '#skF_6') | ~r1_tarski(A_482, '#skF_7'))), inference(resolution, [status(thm)], [c_85, c_6937])).
% 7.79/2.64  tff(c_6963, plain, (![A_483]: (k9_subset_1('#skF_7', '#skF_7', k2_pre_topc('#skF_6', A_483))=A_483 | ~r1_tarski(A_483, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_6953])).
% 7.79/2.64  tff(c_6993, plain, (k9_subset_1('#skF_7', '#skF_7', k2_pre_topc('#skF_6', '#skF_2'('#skF_6')))=k2_pre_topc('#skF_6', '#skF_2'('#skF_6')) | ~r1_tarski(k2_pre_topc('#skF_6', '#skF_2'('#skF_6')), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4176, c_6963])).
% 7.79/2.64  tff(c_7007, plain, (k9_subset_1('#skF_7', '#skF_7', k2_pre_topc('#skF_6', '#skF_2'('#skF_6')))=k2_pre_topc('#skF_6', '#skF_2'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4342, c_6993])).
% 7.79/2.64  tff(c_6962, plain, (![A_482]: (k9_subset_1('#skF_7', '#skF_7', k2_pre_topc('#skF_6', A_482))=A_482 | ~r1_tarski(A_482, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_6953])).
% 7.79/2.64  tff(c_7013, plain, (k2_pre_topc('#skF_6', '#skF_2'('#skF_6'))='#skF_2'('#skF_6') | ~r1_tarski('#skF_2'('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_7007, c_6962])).
% 7.79/2.64  tff(c_7020, plain, (k2_pre_topc('#skF_6', '#skF_2'('#skF_6'))='#skF_2'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3064, c_7013])).
% 7.79/2.64  tff(c_7022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3326, c_7020])).
% 7.79/2.64  tff(c_7024, plain, (v4_pre_topc('#skF_2'('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_3200])).
% 7.79/2.64  tff(c_7490, plain, (![B_510, A_511]: (v3_pre_topc(B_510, A_511) | ~v4_pre_topc(B_510, A_511) | ~m1_subset_1(B_510, k1_zfmisc_1(u1_struct_0(A_511))) | ~v3_tdlat_3(A_511) | ~l1_pre_topc(A_511) | ~v2_pre_topc(A_511))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.79/2.64  tff(c_7493, plain, (![B_510]: (v3_pre_topc(B_510, '#skF_6') | ~v4_pre_topc(B_510, '#skF_6') | ~m1_subset_1(B_510, k1_zfmisc_1('#skF_7')) | ~v3_tdlat_3('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1438, c_7490])).
% 7.79/2.64  tff(c_7522, plain, (![B_512]: (v3_pre_topc(B_512, '#skF_6') | ~v4_pre_topc(B_512, '#skF_6') | ~m1_subset_1(B_512, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_80, c_7493])).
% 7.79/2.64  tff(c_7528, plain, (v3_pre_topc('#skF_2'('#skF_6'), '#skF_6') | ~v4_pre_topc('#skF_2'('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_3066, c_7522])).
% 7.79/2.64  tff(c_7540, plain, (v3_pre_topc('#skF_2'('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7024, c_7528])).
% 7.79/2.64  tff(c_36, plain, (![A_25]: (~v3_pre_topc('#skF_2'(A_25), A_25) | v1_tdlat_3(A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.79/2.64  tff(c_7550, plain, (v1_tdlat_3('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_7540, c_36])).
% 7.79/2.64  tff(c_7556, plain, (v1_tdlat_3('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_7550])).
% 7.79/2.64  tff(c_7558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3065, c_7556])).
% 7.79/2.64  tff(c_7560, plain, (~v3_pre_topc('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 7.79/2.64  tff(c_7559, plain, (v4_pre_topc('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 7.79/2.64  tff(c_8126, plain, (![B_582, A_583]: (v3_pre_topc(B_582, A_583) | ~v4_pre_topc(B_582, A_583) | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0(A_583))) | ~v3_tdlat_3(A_583) | ~l1_pre_topc(A_583) | ~v2_pre_topc(A_583))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.79/2.64  tff(c_8145, plain, (v3_pre_topc('#skF_7', '#skF_6') | ~v4_pre_topc('#skF_7', '#skF_6') | ~v3_tdlat_3('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_76, c_8126])).
% 7.79/2.64  tff(c_8157, plain, (v3_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_80, c_7559, c_8145])).
% 7.79/2.64  tff(c_8159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7560, c_8157])).
% 7.79/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.64  
% 7.79/2.64  Inference rules
% 7.79/2.64  ----------------------
% 7.79/2.64  #Ref     : 0
% 7.79/2.64  #Sup     : 1648
% 7.79/2.64  #Fact    : 0
% 7.79/2.64  #Define  : 0
% 7.79/2.64  #Split   : 14
% 7.79/2.64  #Chain   : 0
% 7.79/2.64  #Close   : 0
% 7.79/2.64  
% 7.79/2.64  Ordering : KBO
% 7.79/2.64  
% 7.79/2.64  Simplification rules
% 7.79/2.64  ----------------------
% 7.79/2.64  #Subsume      : 443
% 7.79/2.64  #Demod        : 2212
% 7.79/2.64  #Tautology    : 483
% 7.79/2.64  #SimpNegUnit  : 79
% 7.79/2.64  #BackRed      : 3
% 7.79/2.64  
% 7.79/2.64  #Partial instantiations: 0
% 7.79/2.64  #Strategies tried      : 1
% 7.79/2.64  
% 7.79/2.64  Timing (in seconds)
% 7.79/2.64  ----------------------
% 7.79/2.64  Preprocessing        : 0.36
% 7.79/2.64  Parsing              : 0.19
% 7.79/2.64  CNF conversion       : 0.03
% 7.79/2.64  Main loop            : 1.42
% 7.79/2.64  Inferencing          : 0.52
% 7.79/2.64  Reduction            : 0.46
% 7.79/2.64  Demodulation         : 0.32
% 7.79/2.64  BG Simplification    : 0.05
% 7.79/2.64  Subsumption          : 0.28
% 7.79/2.64  Abstraction          : 0.07
% 7.79/2.64  MUC search           : 0.00
% 7.79/2.64  Cooper               : 0.00
% 7.79/2.64  Total                : 1.84
% 7.79/2.64  Index Insertion      : 0.00
% 7.79/2.64  Index Deletion       : 0.00
% 7.79/2.64  Index Matching       : 0.00
% 7.79/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------

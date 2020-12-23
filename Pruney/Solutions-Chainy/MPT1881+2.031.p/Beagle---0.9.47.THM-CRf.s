%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:10 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  197 (1120 expanded)
%              Number of leaves         :   45 ( 396 expanded)
%              Depth                    :   14
%              Number of atoms          :  465 (2864 expanded)
%              Number of equality atoms :   54 ( 449 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_188,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_170,axiom,(
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

tff(f_129,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_16] : ~ v1_subset_1(k2_subset_1(A_16),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_80,plain,(
    ! [A_16] : ~ v1_subset_1(A_16,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1227,plain,(
    ! [A_197] :
      ( u1_struct_0(A_197) = k2_struct_0(A_197)
      | ~ l1_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1235,plain,(
    ! [A_199] :
      ( u1_struct_0(A_199) = k2_struct_0(A_199)
      | ~ l1_pre_topc(A_199) ) ),
    inference(resolution,[status(thm)],[c_20,c_1227])).

tff(c_1239,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1235])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1241,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1239,c_62])).

tff(c_97,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_102,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_20,c_97])).

tff(c_106,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_102])).

tff(c_78,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_95,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_107,plain,(
    ~ v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_95])).

tff(c_72,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_113,plain,
    ( v1_subset_1('#skF_5',k2_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_72])).

tff(c_114,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_108,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_62])).

tff(c_115,plain,(
    ! [B_59,A_60] :
      ( v1_subset_1(B_59,A_60)
      | B_59 = A_60
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_118,plain,
    ( v1_subset_1('#skF_5',k2_struct_0('#skF_4'))
    | k2_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_108,c_115])).

tff(c_124,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_118])).

tff(c_131,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_106])).

tff(c_229,plain,(
    ! [A_79,B_80] :
      ( k2_pre_topc(A_79,B_80) = B_80
      | ~ v4_pre_topc(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_239,plain,(
    ! [B_80] :
      ( k2_pre_topc('#skF_4',B_80) = B_80
      | ~ v4_pre_topc(B_80,'#skF_4')
      | ~ m1_subset_1(B_80,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_229])).

tff(c_255,plain,(
    ! [B_82] :
      ( k2_pre_topc('#skF_4',B_82) = B_82
      | ~ v4_pre_topc(B_82,'#skF_4')
      | ~ m1_subset_1(B_82,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_239])).

tff(c_265,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_255])).

tff(c_266,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_66,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_197,plain,(
    ! [B_75,A_76] :
      ( v3_pre_topc(B_75,A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ v1_tdlat_3(A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_207,plain,(
    ! [B_75] :
      ( v3_pre_topc(B_75,'#skF_4')
      | ~ m1_subset_1(B_75,k1_zfmisc_1('#skF_5'))
      | ~ v1_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_197])).

tff(c_217,plain,(
    ! [B_77] :
      ( v3_pre_topc(B_77,'#skF_4')
      | ~ m1_subset_1(B_77,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_66,c_207])).

tff(c_226,plain,(
    ! [B_4] :
      ( v3_pre_topc(k3_subset_1('#skF_5',B_4),'#skF_4')
      | ~ m1_subset_1(B_4,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_217])).

tff(c_459,plain,(
    ! [B_108,A_109] :
      ( v4_pre_topc(B_108,A_109)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_109),B_108),A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_465,plain,(
    ! [B_108] :
      ( v4_pre_topc(B_108,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1('#skF_5',B_108),'#skF_4')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_459])).

tff(c_489,plain,(
    ! [B_112] :
      ( v4_pre_topc(B_112,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1('#skF_5',B_112),'#skF_4')
      | ~ m1_subset_1(B_112,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_131,c_465])).

tff(c_494,plain,(
    ! [B_113] :
      ( v4_pre_topc(B_113,'#skF_4')
      | ~ m1_subset_1(B_113,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_226,c_489])).

tff(c_502,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_494])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_502])).

tff(c_508,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_554,plain,(
    ! [B_120,A_121] :
      ( v1_tops_1(B_120,A_121)
      | k2_pre_topc(A_121,B_120) != k2_struct_0(A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_564,plain,(
    ! [B_120] :
      ( v1_tops_1(B_120,'#skF_4')
      | k2_pre_topc('#skF_4',B_120) != k2_struct_0('#skF_4')
      | ~ m1_subset_1(B_120,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_554])).

tff(c_574,plain,(
    ! [B_122] :
      ( v1_tops_1(B_122,'#skF_4')
      | k2_pre_topc('#skF_4',B_122) != '#skF_5'
      | ~ m1_subset_1(B_122,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_124,c_564])).

tff(c_582,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_79,c_574])).

tff(c_586,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_582])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_615,plain,(
    ! [B_128,A_129] :
      ( v2_tex_2(B_128,A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v1_tdlat_3(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_625,plain,(
    ! [B_128] :
      ( v2_tex_2(B_128,'#skF_4')
      | ~ m1_subset_1(B_128,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_615])).

tff(c_633,plain,(
    ! [B_128] :
      ( v2_tex_2(B_128,'#skF_4')
      | ~ m1_subset_1(B_128,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_625])).

tff(c_636,plain,(
    ! [B_130] :
      ( v2_tex_2(B_130,'#skF_4')
      | ~ m1_subset_1(B_130,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_633])).

tff(c_646,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_636])).

tff(c_1168,plain,(
    ! [B_194,A_195] :
      ( v3_tex_2(B_194,A_195)
      | ~ v2_tex_2(B_194,A_195)
      | ~ v1_tops_1(B_194,A_195)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1185,plain,(
    ! [B_194] :
      ( v3_tex_2(B_194,'#skF_4')
      | ~ v2_tex_2(B_194,'#skF_4')
      | ~ v1_tops_1(B_194,'#skF_4')
      | ~ m1_subset_1(B_194,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_1168])).

tff(c_1195,plain,(
    ! [B_194] :
      ( v3_tex_2(B_194,'#skF_4')
      | ~ v2_tex_2(B_194,'#skF_4')
      | ~ v1_tops_1(B_194,'#skF_4')
      | ~ m1_subset_1(B_194,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1185])).

tff(c_1198,plain,(
    ! [B_196] :
      ( v3_tex_2(B_196,'#skF_4')
      | ~ v2_tex_2(B_196,'#skF_4')
      | ~ v1_tops_1(B_196,'#skF_4')
      | ~ m1_subset_1(B_196,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1195])).

tff(c_1213,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_1198])).

tff(c_1219,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_646,c_1213])).

tff(c_1221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_1219])).

tff(c_1222,plain,(
    v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_1224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1222])).

tff(c_1225,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1276,plain,(
    ! [B_209,A_210] :
      ( v2_tex_2(B_209,A_210)
      | ~ v3_tex_2(B_209,A_210)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1296,plain,(
    ! [A_211] :
      ( v2_tex_2(u1_struct_0(A_211),A_211)
      | ~ v3_tex_2(u1_struct_0(A_211),A_211)
      | ~ l1_pre_topc(A_211) ) ),
    inference(resolution,[status(thm)],[c_79,c_1276])).

tff(c_1299,plain,
    ( v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v3_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_1296])).

tff(c_1301,plain,
    ( v2_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1239,c_1299])).

tff(c_1302,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1301])).

tff(c_1321,plain,(
    ! [A_215,B_216] :
      ( k2_pre_topc(A_215,B_216) = B_216
      | ~ v4_pre_topc(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1341,plain,(
    ! [A_217] :
      ( k2_pre_topc(A_217,u1_struct_0(A_217)) = u1_struct_0(A_217)
      | ~ v4_pre_topc(u1_struct_0(A_217),A_217)
      | ~ l1_pre_topc(A_217) ) ),
    inference(resolution,[status(thm)],[c_79,c_1321])).

tff(c_1344,plain,
    ( k2_pre_topc('#skF_4',u1_struct_0('#skF_4')) = u1_struct_0('#skF_4')
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_1341])).

tff(c_1346,plain,
    ( k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) = k2_struct_0('#skF_4')
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1239,c_1239,c_1344])).

tff(c_1347,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1346])).

tff(c_1348,plain,(
    ! [B_218,A_219] :
      ( v3_pre_topc(B_218,A_219)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ v1_tdlat_3(A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1358,plain,(
    ! [B_218] :
      ( v3_pre_topc(B_218,'#skF_4')
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v1_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_1348])).

tff(c_1368,plain,(
    ! [B_220] :
      ( v3_pre_topc(B_220,'#skF_4')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_66,c_1358])).

tff(c_1380,plain,(
    ! [B_4] :
      ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),B_4),'#skF_4')
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_1368])).

tff(c_1805,plain,(
    ! [B_266,A_267] :
      ( v4_pre_topc(B_266,A_267)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_267),B_266),A_267)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1808,plain,(
    ! [B_266] :
      ( v4_pre_topc(B_266,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),B_266),'#skF_4')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_1805])).

tff(c_1840,plain,(
    ! [B_270] :
      ( v4_pre_topc(B_270,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),B_270),'#skF_4')
      | ~ m1_subset_1(B_270,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1239,c_1808])).

tff(c_1845,plain,(
    ! [B_271] :
      ( v4_pre_topc(B_271,'#skF_4')
      | ~ m1_subset_1(B_271,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1380,c_1840])).

tff(c_1856,plain,(
    v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_1845])).

tff(c_1863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1347,c_1856])).

tff(c_1864,plain,(
    k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) = k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1346])).

tff(c_2195,plain,(
    ! [B_307,A_308] :
      ( v1_tops_1(B_307,A_308)
      | k2_pre_topc(A_308,B_307) != k2_struct_0(A_308)
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2215,plain,(
    ! [A_309] :
      ( v1_tops_1(u1_struct_0(A_309),A_309)
      | k2_pre_topc(A_309,u1_struct_0(A_309)) != k2_struct_0(A_309)
      | ~ l1_pre_topc(A_309) ) ),
    inference(resolution,[status(thm)],[c_79,c_2195])).

tff(c_2221,plain,
    ( v1_tops_1(k2_struct_0('#skF_4'),'#skF_4')
    | k2_pre_topc('#skF_4',u1_struct_0('#skF_4')) != k2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_2215])).

tff(c_2224,plain,(
    v1_tops_1(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1864,c_1239,c_2221])).

tff(c_2319,plain,(
    ! [B_322,A_323] :
      ( v2_tex_2(B_322,A_323)
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323)
      | ~ v1_tdlat_3(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2329,plain,(
    ! [B_322] :
      ( v2_tex_2(B_322,'#skF_4')
      | ~ m1_subset_1(B_322,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_2319])).

tff(c_2337,plain,(
    ! [B_322] :
      ( v2_tex_2(B_322,'#skF_4')
      | ~ m1_subset_1(B_322,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2329])).

tff(c_2340,plain,(
    ! [B_324] :
      ( v2_tex_2(B_324,'#skF_4')
      | ~ m1_subset_1(B_324,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2337])).

tff(c_2355,plain,(
    v2_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_2340])).

tff(c_2881,plain,(
    ! [B_376,A_377] :
      ( v3_tex_2(B_376,A_377)
      | ~ v2_tex_2(B_376,A_377)
      | ~ v1_tops_1(B_376,A_377)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_2898,plain,(
    ! [B_376] :
      ( v3_tex_2(B_376,'#skF_4')
      | ~ v2_tex_2(B_376,'#skF_4')
      | ~ v1_tops_1(B_376,'#skF_4')
      | ~ m1_subset_1(B_376,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_2881])).

tff(c_2908,plain,(
    ! [B_376] :
      ( v3_tex_2(B_376,'#skF_4')
      | ~ v2_tex_2(B_376,'#skF_4')
      | ~ v1_tops_1(B_376,'#skF_4')
      | ~ m1_subset_1(B_376,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2898])).

tff(c_2924,plain,(
    ! [B_381] :
      ( v3_tex_2(B_381,'#skF_4')
      | ~ v2_tex_2(B_381,'#skF_4')
      | ~ v1_tops_1(B_381,'#skF_4')
      | ~ m1_subset_1(B_381,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2908])).

tff(c_2942,plain,
    ( v3_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v2_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v1_tops_1(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_2924])).

tff(c_2951,plain,(
    v3_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2224,c_2355,c_2942])).

tff(c_2953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1302,c_2951])).

tff(c_2954,plain,(
    v2_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1301])).

tff(c_2976,plain,(
    ! [A_385,B_386] :
      ( k2_pre_topc(A_385,B_386) = B_386
      | ~ v4_pre_topc(B_386,A_385)
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(A_385)))
      | ~ l1_pre_topc(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2986,plain,(
    ! [B_386] :
      ( k2_pre_topc('#skF_4',B_386) = B_386
      | ~ v4_pre_topc(B_386,'#skF_4')
      | ~ m1_subset_1(B_386,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_2976])).

tff(c_3547,plain,(
    ! [B_446] :
      ( k2_pre_topc('#skF_4',B_446) = B_446
      | ~ v4_pre_topc(B_446,'#skF_4')
      | ~ m1_subset_1(B_446,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2986])).

tff(c_3560,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1241,c_3547])).

tff(c_3564,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3560])).

tff(c_3565,plain,(
    ! [B_447,A_448] :
      ( v3_pre_topc(B_447,A_448)
      | ~ m1_subset_1(B_447,k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ v1_tdlat_3(A_448)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3575,plain,(
    ! [B_447] :
      ( v3_pre_topc(B_447,'#skF_4')
      | ~ m1_subset_1(B_447,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v1_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_3565])).

tff(c_3585,plain,(
    ! [B_449] :
      ( v3_pre_topc(B_449,'#skF_4')
      | ~ m1_subset_1(B_449,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_66,c_3575])).

tff(c_3597,plain,(
    ! [B_4] :
      ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),B_4),'#skF_4')
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_3585])).

tff(c_3744,plain,(
    ! [B_465,A_466] :
      ( v4_pre_topc(B_465,A_466)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_466),B_465),A_466)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0(A_466)))
      | ~ l1_pre_topc(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3747,plain,(
    ! [B_465] :
      ( v4_pre_topc(B_465,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),B_465),'#skF_4')
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_3744])).

tff(c_3758,plain,(
    ! [B_469] :
      ( v4_pre_topc(B_469,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),B_469),'#skF_4')
      | ~ m1_subset_1(B_469,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1239,c_3747])).

tff(c_3763,plain,(
    ! [B_470] :
      ( v4_pre_topc(B_470,'#skF_4')
      | ~ m1_subset_1(B_470,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3597,c_3758])).

tff(c_3770,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1241,c_3763])).

tff(c_3779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3564,c_3770])).

tff(c_3780,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3560])).

tff(c_3821,plain,(
    ! [A_474,B_475] :
      ( k2_pre_topc(A_474,B_475) = k2_struct_0(A_474)
      | ~ v1_tops_1(B_475,A_474)
      | ~ m1_subset_1(B_475,k1_zfmisc_1(u1_struct_0(A_474)))
      | ~ l1_pre_topc(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3831,plain,(
    ! [B_475] :
      ( k2_pre_topc('#skF_4',B_475) = k2_struct_0('#skF_4')
      | ~ v1_tops_1(B_475,'#skF_4')
      | ~ m1_subset_1(B_475,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_3821])).

tff(c_3848,plain,(
    ! [B_478] :
      ( k2_pre_topc('#skF_4',B_478) = k2_struct_0('#skF_4')
      | ~ v1_tops_1(B_478,'#skF_4')
      | ~ m1_subset_1(B_478,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3831])).

tff(c_3855,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = k2_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1241,c_3848])).

tff(c_3862,plain,
    ( k2_struct_0('#skF_4') = '#skF_5'
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3780,c_3855])).

tff(c_3865,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3862])).

tff(c_3873,plain,(
    ! [B_481,A_482] :
      ( v1_tops_1(B_481,A_482)
      | k2_pre_topc(A_482,B_481) != k2_struct_0(A_482)
      | ~ m1_subset_1(B_481,k1_zfmisc_1(u1_struct_0(A_482)))
      | ~ l1_pre_topc(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3883,plain,(
    ! [B_481] :
      ( v1_tops_1(B_481,'#skF_4')
      | k2_pre_topc('#skF_4',B_481) != k2_struct_0('#skF_4')
      | ~ m1_subset_1(B_481,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_3873])).

tff(c_3909,plain,(
    ! [B_486] :
      ( v1_tops_1(B_486,'#skF_4')
      | k2_pre_topc('#skF_4',B_486) != k2_struct_0('#skF_4')
      | ~ m1_subset_1(B_486,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3883])).

tff(c_3916,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1241,c_3909])).

tff(c_3923,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_struct_0('#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3780,c_3916])).

tff(c_3924,plain,(
    k2_struct_0('#skF_4') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3865,c_3923])).

tff(c_4204,plain,(
    ! [A_513,B_514,C_515] :
      ( r2_hidden('#skF_1'(A_513,B_514,C_515),B_514)
      | r1_tarski(B_514,C_515)
      | ~ m1_subset_1(C_515,k1_zfmisc_1(A_513))
      | ~ m1_subset_1(B_514,k1_zfmisc_1(A_513)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4665,plain,(
    ! [A_564,B_565,C_566,A_567] :
      ( r2_hidden('#skF_1'(A_564,B_565,C_566),A_567)
      | ~ m1_subset_1(B_565,k1_zfmisc_1(A_567))
      | r1_tarski(B_565,C_566)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(A_564))
      | ~ m1_subset_1(B_565,k1_zfmisc_1(A_564)) ) ),
    inference(resolution,[status(thm)],[c_4204,c_8])).

tff(c_10,plain,(
    ! [A_9,B_10,C_14] :
      ( ~ r2_hidden('#skF_1'(A_9,B_10,C_14),C_14)
      | r1_tarski(B_10,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4674,plain,(
    ! [B_568,A_569,A_570] :
      ( ~ m1_subset_1(B_568,k1_zfmisc_1(A_569))
      | r1_tarski(B_568,A_569)
      | ~ m1_subset_1(A_569,k1_zfmisc_1(A_570))
      | ~ m1_subset_1(B_568,k1_zfmisc_1(A_570)) ) ),
    inference(resolution,[status(thm)],[c_4665,c_10])).

tff(c_4695,plain,(
    ! [A_570] :
      ( r1_tarski('#skF_5',k2_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(A_570))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_570)) ) ),
    inference(resolution,[status(thm)],[c_1241,c_4674])).

tff(c_4699,plain,(
    ! [A_571] :
      ( ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(A_571))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_571)) ) ),
    inference(splitLeft,[status(thm)],[c_4695])).

tff(c_4703,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_79,c_4699])).

tff(c_4707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_4703])).

tff(c_4708,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4695])).

tff(c_48,plain,(
    ! [C_40,B_37,A_31] :
      ( C_40 = B_37
      | ~ r1_tarski(B_37,C_40)
      | ~ v2_tex_2(C_40,A_31)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ v3_tex_2(B_37,A_31)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4710,plain,(
    ! [A_31] :
      ( k2_struct_0('#skF_4') = '#skF_5'
      | ~ v2_tex_2(k2_struct_0('#skF_4'),A_31)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ v3_tex_2('#skF_5',A_31)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_4708,c_48])).

tff(c_4738,plain,(
    ! [A_579] :
      ( ~ v2_tex_2(k2_struct_0('#skF_4'),A_579)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_579)))
      | ~ v3_tex_2('#skF_5',A_579)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_579)))
      | ~ l1_pre_topc(A_579) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3924,c_4710])).

tff(c_4741,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_4738])).

tff(c_4744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1241,c_1239,c_1225,c_79,c_2954,c_4741])).

tff(c_4745,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3862])).

tff(c_1226,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1240,plain,(
    v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1239,c_1226])).

tff(c_4758,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4745,c_1240])).

tff(c_4767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:08:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.12  
% 5.96/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.12  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 5.96/2.12  
% 5.96/2.12  %Foreground sorts:
% 5.96/2.12  
% 5.96/2.12  
% 5.96/2.12  %Background operators:
% 5.96/2.12  
% 5.96/2.12  
% 5.96/2.12  %Foreground operators:
% 5.96/2.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.96/2.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.96/2.12  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.96/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.96/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.96/2.12  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.96/2.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.96/2.12  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.96/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.96/2.12  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.96/2.12  tff('#skF_5', type, '#skF_5': $i).
% 5.96/2.12  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.96/2.12  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.96/2.12  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.96/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.96/2.12  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.96/2.12  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.96/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.96/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.96/2.12  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.96/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.96/2.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.96/2.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.96/2.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.96/2.12  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.96/2.12  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.96/2.12  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.96/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.96/2.12  
% 5.96/2.15  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.96/2.15  tff(f_57, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 5.96/2.15  tff(f_188, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 5.96/2.15  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.96/2.15  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.96/2.15  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.96/2.15  tff(f_111, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 5.96/2.15  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.96/2.15  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.96/2.15  tff(f_140, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 5.96/2.15  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 5.96/2.15  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 5.96/2.15  tff(f_154, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 5.96/2.15  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 5.96/2.15  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 5.96/2.15  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 5.96/2.15  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.96/2.15  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.96/2.15  tff(c_16, plain, (![A_16]: (~v1_subset_1(k2_subset_1(A_16), A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.96/2.15  tff(c_80, plain, (![A_16]: (~v1_subset_1(A_16, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 5.96/2.15  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.96/2.15  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.96/2.15  tff(c_1227, plain, (![A_197]: (u1_struct_0(A_197)=k2_struct_0(A_197) | ~l1_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.96/2.15  tff(c_1235, plain, (![A_199]: (u1_struct_0(A_199)=k2_struct_0(A_199) | ~l1_pre_topc(A_199))), inference(resolution, [status(thm)], [c_20, c_1227])).
% 5.96/2.15  tff(c_1239, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_1235])).
% 5.96/2.15  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.96/2.15  tff(c_1241, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1239, c_62])).
% 5.96/2.15  tff(c_97, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.96/2.15  tff(c_102, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_20, c_97])).
% 5.96/2.15  tff(c_106, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_102])).
% 5.96/2.15  tff(c_78, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.96/2.15  tff(c_95, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_78])).
% 5.96/2.15  tff(c_107, plain, (~v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_95])).
% 5.96/2.15  tff(c_72, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.96/2.15  tff(c_113, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_72])).
% 5.96/2.15  tff(c_114, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_113])).
% 5.96/2.15  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.96/2.15  tff(c_79, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.96/2.15  tff(c_108, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_62])).
% 5.96/2.15  tff(c_115, plain, (![B_59, A_60]: (v1_subset_1(B_59, A_60) | B_59=A_60 | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.96/2.15  tff(c_118, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4')) | k2_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_108, c_115])).
% 5.96/2.15  tff(c_124, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_107, c_118])).
% 5.96/2.15  tff(c_131, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_106])).
% 5.96/2.15  tff(c_229, plain, (![A_79, B_80]: (k2_pre_topc(A_79, B_80)=B_80 | ~v4_pre_topc(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.96/2.15  tff(c_239, plain, (![B_80]: (k2_pre_topc('#skF_4', B_80)=B_80 | ~v4_pre_topc(B_80, '#skF_4') | ~m1_subset_1(B_80, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_229])).
% 5.96/2.15  tff(c_255, plain, (![B_82]: (k2_pre_topc('#skF_4', B_82)=B_82 | ~v4_pre_topc(B_82, '#skF_4') | ~m1_subset_1(B_82, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_239])).
% 5.96/2.15  tff(c_265, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_79, c_255])).
% 5.96/2.15  tff(c_266, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_265])).
% 5.96/2.15  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.96/2.15  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.96/2.15  tff(c_66, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.96/2.15  tff(c_197, plain, (![B_75, A_76]: (v3_pre_topc(B_75, A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~v1_tdlat_3(A_76) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.96/2.15  tff(c_207, plain, (![B_75]: (v3_pre_topc(B_75, '#skF_4') | ~m1_subset_1(B_75, k1_zfmisc_1('#skF_5')) | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_197])).
% 5.96/2.15  tff(c_217, plain, (![B_77]: (v3_pre_topc(B_77, '#skF_4') | ~m1_subset_1(B_77, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_66, c_207])).
% 5.96/2.15  tff(c_226, plain, (![B_4]: (v3_pre_topc(k3_subset_1('#skF_5', B_4), '#skF_4') | ~m1_subset_1(B_4, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_217])).
% 5.96/2.15  tff(c_459, plain, (![B_108, A_109]: (v4_pre_topc(B_108, A_109) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_109), B_108), A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.96/2.15  tff(c_465, plain, (![B_108]: (v4_pre_topc(B_108, '#skF_4') | ~v3_pre_topc(k3_subset_1('#skF_5', B_108), '#skF_4') | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_459])).
% 5.96/2.15  tff(c_489, plain, (![B_112]: (v4_pre_topc(B_112, '#skF_4') | ~v3_pre_topc(k3_subset_1('#skF_5', B_112), '#skF_4') | ~m1_subset_1(B_112, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_131, c_465])).
% 5.96/2.15  tff(c_494, plain, (![B_113]: (v4_pre_topc(B_113, '#skF_4') | ~m1_subset_1(B_113, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_226, c_489])).
% 5.96/2.15  tff(c_502, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_79, c_494])).
% 5.96/2.15  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_502])).
% 5.96/2.15  tff(c_508, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_265])).
% 5.96/2.15  tff(c_554, plain, (![B_120, A_121]: (v1_tops_1(B_120, A_121) | k2_pre_topc(A_121, B_120)!=k2_struct_0(A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.96/2.15  tff(c_564, plain, (![B_120]: (v1_tops_1(B_120, '#skF_4') | k2_pre_topc('#skF_4', B_120)!=k2_struct_0('#skF_4') | ~m1_subset_1(B_120, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_554])).
% 5.96/2.15  tff(c_574, plain, (![B_122]: (v1_tops_1(B_122, '#skF_4') | k2_pre_topc('#skF_4', B_122)!='#skF_5' | ~m1_subset_1(B_122, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_124, c_564])).
% 5.96/2.15  tff(c_582, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_79, c_574])).
% 5.96/2.15  tff(c_586, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_508, c_582])).
% 5.96/2.15  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.96/2.15  tff(c_615, plain, (![B_128, A_129]: (v2_tex_2(B_128, A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~v1_tdlat_3(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.96/2.15  tff(c_625, plain, (![B_128]: (v2_tex_2(B_128, '#skF_4') | ~m1_subset_1(B_128, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_615])).
% 5.96/2.15  tff(c_633, plain, (![B_128]: (v2_tex_2(B_128, '#skF_4') | ~m1_subset_1(B_128, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_625])).
% 5.96/2.15  tff(c_636, plain, (![B_130]: (v2_tex_2(B_130, '#skF_4') | ~m1_subset_1(B_130, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_633])).
% 5.96/2.15  tff(c_646, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_79, c_636])).
% 5.96/2.15  tff(c_1168, plain, (![B_194, A_195]: (v3_tex_2(B_194, A_195) | ~v2_tex_2(B_194, A_195) | ~v1_tops_1(B_194, A_195) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.96/2.15  tff(c_1185, plain, (![B_194]: (v3_tex_2(B_194, '#skF_4') | ~v2_tex_2(B_194, '#skF_4') | ~v1_tops_1(B_194, '#skF_4') | ~m1_subset_1(B_194, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_1168])).
% 5.96/2.15  tff(c_1195, plain, (![B_194]: (v3_tex_2(B_194, '#skF_4') | ~v2_tex_2(B_194, '#skF_4') | ~v1_tops_1(B_194, '#skF_4') | ~m1_subset_1(B_194, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1185])).
% 5.96/2.15  tff(c_1198, plain, (![B_196]: (v3_tex_2(B_196, '#skF_4') | ~v2_tex_2(B_196, '#skF_4') | ~v1_tops_1(B_196, '#skF_4') | ~m1_subset_1(B_196, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_1195])).
% 5.96/2.15  tff(c_1213, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_79, c_1198])).
% 5.96/2.15  tff(c_1219, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_646, c_1213])).
% 5.96/2.15  tff(c_1221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_1219])).
% 5.96/2.15  tff(c_1222, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_113])).
% 5.96/2.15  tff(c_1224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_1222])).
% 5.96/2.15  tff(c_1225, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_78])).
% 5.96/2.15  tff(c_1276, plain, (![B_209, A_210]: (v2_tex_2(B_209, A_210) | ~v3_tex_2(B_209, A_210) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.96/2.15  tff(c_1296, plain, (![A_211]: (v2_tex_2(u1_struct_0(A_211), A_211) | ~v3_tex_2(u1_struct_0(A_211), A_211) | ~l1_pre_topc(A_211))), inference(resolution, [status(thm)], [c_79, c_1276])).
% 5.96/2.15  tff(c_1299, plain, (v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v3_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1239, c_1296])).
% 5.96/2.15  tff(c_1301, plain, (v2_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~v3_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1239, c_1299])).
% 5.96/2.15  tff(c_1302, plain, (~v3_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1301])).
% 5.96/2.15  tff(c_1321, plain, (![A_215, B_216]: (k2_pre_topc(A_215, B_216)=B_216 | ~v4_pre_topc(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.96/2.15  tff(c_1341, plain, (![A_217]: (k2_pre_topc(A_217, u1_struct_0(A_217))=u1_struct_0(A_217) | ~v4_pre_topc(u1_struct_0(A_217), A_217) | ~l1_pre_topc(A_217))), inference(resolution, [status(thm)], [c_79, c_1321])).
% 5.96/2.15  tff(c_1344, plain, (k2_pre_topc('#skF_4', u1_struct_0('#skF_4'))=u1_struct_0('#skF_4') | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1239, c_1341])).
% 5.96/2.15  tff(c_1346, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))=k2_struct_0('#skF_4') | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1239, c_1239, c_1344])).
% 5.96/2.15  tff(c_1347, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1346])).
% 5.96/2.15  tff(c_1348, plain, (![B_218, A_219]: (v3_pre_topc(B_218, A_219) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_219))) | ~v1_tdlat_3(A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.96/2.15  tff(c_1358, plain, (![B_218]: (v3_pre_topc(B_218, '#skF_4') | ~m1_subset_1(B_218, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_1348])).
% 5.96/2.15  tff(c_1368, plain, (![B_220]: (v3_pre_topc(B_220, '#skF_4') | ~m1_subset_1(B_220, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_66, c_1358])).
% 5.96/2.15  tff(c_1380, plain, (![B_4]: (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), B_4), '#skF_4') | ~m1_subset_1(B_4, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_6, c_1368])).
% 5.96/2.15  tff(c_1805, plain, (![B_266, A_267]: (v4_pre_topc(B_266, A_267) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_267), B_266), A_267) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.96/2.15  tff(c_1808, plain, (![B_266]: (v4_pre_topc(B_266, '#skF_4') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), B_266), '#skF_4') | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_1805])).
% 5.96/2.15  tff(c_1840, plain, (![B_270]: (v4_pre_topc(B_270, '#skF_4') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), B_270), '#skF_4') | ~m1_subset_1(B_270, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1239, c_1808])).
% 5.96/2.15  tff(c_1845, plain, (![B_271]: (v4_pre_topc(B_271, '#skF_4') | ~m1_subset_1(B_271, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1380, c_1840])).
% 5.96/2.15  tff(c_1856, plain, (v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_79, c_1845])).
% 5.96/2.15  tff(c_1863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1347, c_1856])).
% 5.96/2.15  tff(c_1864, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1346])).
% 5.96/2.15  tff(c_2195, plain, (![B_307, A_308]: (v1_tops_1(B_307, A_308) | k2_pre_topc(A_308, B_307)!=k2_struct_0(A_308) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.96/2.15  tff(c_2215, plain, (![A_309]: (v1_tops_1(u1_struct_0(A_309), A_309) | k2_pre_topc(A_309, u1_struct_0(A_309))!=k2_struct_0(A_309) | ~l1_pre_topc(A_309))), inference(resolution, [status(thm)], [c_79, c_2195])).
% 5.96/2.15  tff(c_2221, plain, (v1_tops_1(k2_struct_0('#skF_4'), '#skF_4') | k2_pre_topc('#skF_4', u1_struct_0('#skF_4'))!=k2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1239, c_2215])).
% 5.96/2.15  tff(c_2224, plain, (v1_tops_1(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1864, c_1239, c_2221])).
% 5.96/2.15  tff(c_2319, plain, (![B_322, A_323]: (v2_tex_2(B_322, A_323) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(A_323))) | ~l1_pre_topc(A_323) | ~v1_tdlat_3(A_323) | ~v2_pre_topc(A_323) | v2_struct_0(A_323))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.96/2.15  tff(c_2329, plain, (![B_322]: (v2_tex_2(B_322, '#skF_4') | ~m1_subset_1(B_322, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_2319])).
% 5.96/2.15  tff(c_2337, plain, (![B_322]: (v2_tex_2(B_322, '#skF_4') | ~m1_subset_1(B_322, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2329])).
% 5.96/2.15  tff(c_2340, plain, (![B_324]: (v2_tex_2(B_324, '#skF_4') | ~m1_subset_1(B_324, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_2337])).
% 5.96/2.15  tff(c_2355, plain, (v2_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_79, c_2340])).
% 5.96/2.15  tff(c_2881, plain, (![B_376, A_377]: (v3_tex_2(B_376, A_377) | ~v2_tex_2(B_376, A_377) | ~v1_tops_1(B_376, A_377) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_377))) | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.96/2.15  tff(c_2898, plain, (![B_376]: (v3_tex_2(B_376, '#skF_4') | ~v2_tex_2(B_376, '#skF_4') | ~v1_tops_1(B_376, '#skF_4') | ~m1_subset_1(B_376, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_2881])).
% 5.96/2.15  tff(c_2908, plain, (![B_376]: (v3_tex_2(B_376, '#skF_4') | ~v2_tex_2(B_376, '#skF_4') | ~v1_tops_1(B_376, '#skF_4') | ~m1_subset_1(B_376, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2898])).
% 5.96/2.15  tff(c_2924, plain, (![B_381]: (v3_tex_2(B_381, '#skF_4') | ~v2_tex_2(B_381, '#skF_4') | ~v1_tops_1(B_381, '#skF_4') | ~m1_subset_1(B_381, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_2908])).
% 5.96/2.15  tff(c_2942, plain, (v3_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~v2_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~v1_tops_1(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_79, c_2924])).
% 5.96/2.15  tff(c_2951, plain, (v3_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2224, c_2355, c_2942])).
% 5.96/2.15  tff(c_2953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1302, c_2951])).
% 5.96/2.15  tff(c_2954, plain, (v2_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_1301])).
% 5.96/2.15  tff(c_2976, plain, (![A_385, B_386]: (k2_pre_topc(A_385, B_386)=B_386 | ~v4_pre_topc(B_386, A_385) | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0(A_385))) | ~l1_pre_topc(A_385))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.96/2.15  tff(c_2986, plain, (![B_386]: (k2_pre_topc('#skF_4', B_386)=B_386 | ~v4_pre_topc(B_386, '#skF_4') | ~m1_subset_1(B_386, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_2976])).
% 5.96/2.15  tff(c_3547, plain, (![B_446]: (k2_pre_topc('#skF_4', B_446)=B_446 | ~v4_pre_topc(B_446, '#skF_4') | ~m1_subset_1(B_446, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2986])).
% 5.96/2.15  tff(c_3560, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1241, c_3547])).
% 5.96/2.15  tff(c_3564, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_3560])).
% 5.96/2.15  tff(c_3565, plain, (![B_447, A_448]: (v3_pre_topc(B_447, A_448) | ~m1_subset_1(B_447, k1_zfmisc_1(u1_struct_0(A_448))) | ~v1_tdlat_3(A_448) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.96/2.15  tff(c_3575, plain, (![B_447]: (v3_pre_topc(B_447, '#skF_4') | ~m1_subset_1(B_447, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_3565])).
% 5.96/2.15  tff(c_3585, plain, (![B_449]: (v3_pre_topc(B_449, '#skF_4') | ~m1_subset_1(B_449, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_66, c_3575])).
% 5.96/2.15  tff(c_3597, plain, (![B_4]: (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), B_4), '#skF_4') | ~m1_subset_1(B_4, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_6, c_3585])).
% 5.96/2.15  tff(c_3744, plain, (![B_465, A_466]: (v4_pre_topc(B_465, A_466) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_466), B_465), A_466) | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0(A_466))) | ~l1_pre_topc(A_466))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.96/2.15  tff(c_3747, plain, (![B_465]: (v4_pre_topc(B_465, '#skF_4') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), B_465), '#skF_4') | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_3744])).
% 5.96/2.15  tff(c_3758, plain, (![B_469]: (v4_pre_topc(B_469, '#skF_4') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), B_469), '#skF_4') | ~m1_subset_1(B_469, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1239, c_3747])).
% 5.96/2.15  tff(c_3763, plain, (![B_470]: (v4_pre_topc(B_470, '#skF_4') | ~m1_subset_1(B_470, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_3597, c_3758])).
% 5.96/2.15  tff(c_3770, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1241, c_3763])).
% 5.96/2.15  tff(c_3779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3564, c_3770])).
% 5.96/2.15  tff(c_3780, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_3560])).
% 5.96/2.15  tff(c_3821, plain, (![A_474, B_475]: (k2_pre_topc(A_474, B_475)=k2_struct_0(A_474) | ~v1_tops_1(B_475, A_474) | ~m1_subset_1(B_475, k1_zfmisc_1(u1_struct_0(A_474))) | ~l1_pre_topc(A_474))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.96/2.15  tff(c_3831, plain, (![B_475]: (k2_pre_topc('#skF_4', B_475)=k2_struct_0('#skF_4') | ~v1_tops_1(B_475, '#skF_4') | ~m1_subset_1(B_475, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_3821])).
% 5.96/2.15  tff(c_3848, plain, (![B_478]: (k2_pre_topc('#skF_4', B_478)=k2_struct_0('#skF_4') | ~v1_tops_1(B_478, '#skF_4') | ~m1_subset_1(B_478, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3831])).
% 5.96/2.15  tff(c_3855, plain, (k2_pre_topc('#skF_4', '#skF_5')=k2_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1241, c_3848])).
% 5.96/2.15  tff(c_3862, plain, (k2_struct_0('#skF_4')='#skF_5' | ~v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3780, c_3855])).
% 5.96/2.15  tff(c_3865, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_3862])).
% 5.96/2.15  tff(c_3873, plain, (![B_481, A_482]: (v1_tops_1(B_481, A_482) | k2_pre_topc(A_482, B_481)!=k2_struct_0(A_482) | ~m1_subset_1(B_481, k1_zfmisc_1(u1_struct_0(A_482))) | ~l1_pre_topc(A_482))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.96/2.15  tff(c_3883, plain, (![B_481]: (v1_tops_1(B_481, '#skF_4') | k2_pre_topc('#skF_4', B_481)!=k2_struct_0('#skF_4') | ~m1_subset_1(B_481, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_3873])).
% 5.96/2.15  tff(c_3909, plain, (![B_486]: (v1_tops_1(B_486, '#skF_4') | k2_pre_topc('#skF_4', B_486)!=k2_struct_0('#skF_4') | ~m1_subset_1(B_486, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3883])).
% 5.96/2.15  tff(c_3916, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1241, c_3909])).
% 5.96/2.15  tff(c_3923, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_struct_0('#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3780, c_3916])).
% 5.96/2.15  tff(c_3924, plain, (k2_struct_0('#skF_4')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3865, c_3923])).
% 5.96/2.15  tff(c_4204, plain, (![A_513, B_514, C_515]: (r2_hidden('#skF_1'(A_513, B_514, C_515), B_514) | r1_tarski(B_514, C_515) | ~m1_subset_1(C_515, k1_zfmisc_1(A_513)) | ~m1_subset_1(B_514, k1_zfmisc_1(A_513)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.96/2.15  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.96/2.15  tff(c_4665, plain, (![A_564, B_565, C_566, A_567]: (r2_hidden('#skF_1'(A_564, B_565, C_566), A_567) | ~m1_subset_1(B_565, k1_zfmisc_1(A_567)) | r1_tarski(B_565, C_566) | ~m1_subset_1(C_566, k1_zfmisc_1(A_564)) | ~m1_subset_1(B_565, k1_zfmisc_1(A_564)))), inference(resolution, [status(thm)], [c_4204, c_8])).
% 5.96/2.15  tff(c_10, plain, (![A_9, B_10, C_14]: (~r2_hidden('#skF_1'(A_9, B_10, C_14), C_14) | r1_tarski(B_10, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.96/2.15  tff(c_4674, plain, (![B_568, A_569, A_570]: (~m1_subset_1(B_568, k1_zfmisc_1(A_569)) | r1_tarski(B_568, A_569) | ~m1_subset_1(A_569, k1_zfmisc_1(A_570)) | ~m1_subset_1(B_568, k1_zfmisc_1(A_570)))), inference(resolution, [status(thm)], [c_4665, c_10])).
% 5.96/2.15  tff(c_4695, plain, (![A_570]: (r1_tarski('#skF_5', k2_struct_0('#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(A_570)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_570)))), inference(resolution, [status(thm)], [c_1241, c_4674])).
% 5.96/2.15  tff(c_4699, plain, (![A_571]: (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(A_571)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_571)))), inference(splitLeft, [status(thm)], [c_4695])).
% 5.96/2.15  tff(c_4703, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_79, c_4699])).
% 5.96/2.15  tff(c_4707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1241, c_4703])).
% 5.96/2.15  tff(c_4708, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_4695])).
% 5.96/2.15  tff(c_48, plain, (![C_40, B_37, A_31]: (C_40=B_37 | ~r1_tarski(B_37, C_40) | ~v2_tex_2(C_40, A_31) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_31))) | ~v3_tex_2(B_37, A_31) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.96/2.15  tff(c_4710, plain, (![A_31]: (k2_struct_0('#skF_4')='#skF_5' | ~v2_tex_2(k2_struct_0('#skF_4'), A_31) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_31))) | ~v3_tex_2('#skF_5', A_31) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_4708, c_48])).
% 5.96/2.15  tff(c_4738, plain, (![A_579]: (~v2_tex_2(k2_struct_0('#skF_4'), A_579) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_579))) | ~v3_tex_2('#skF_5', A_579) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_579))) | ~l1_pre_topc(A_579))), inference(negUnitSimplification, [status(thm)], [c_3924, c_4710])).
% 5.96/2.15  tff(c_4741, plain, (~v2_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v3_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1239, c_4738])).
% 5.96/2.15  tff(c_4744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_1241, c_1239, c_1225, c_79, c_2954, c_4741])).
% 5.96/2.15  tff(c_4745, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_3862])).
% 5.96/2.15  tff(c_1226, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_78])).
% 5.96/2.15  tff(c_1240, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1239, c_1226])).
% 5.96/2.15  tff(c_4758, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4745, c_1240])).
% 5.96/2.15  tff(c_4767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_4758])).
% 5.96/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.15  
% 5.96/2.15  Inference rules
% 5.96/2.15  ----------------------
% 5.96/2.15  #Ref     : 0
% 5.96/2.15  #Sup     : 888
% 5.96/2.15  #Fact    : 0
% 5.96/2.15  #Define  : 0
% 5.96/2.15  #Split   : 24
% 5.96/2.15  #Chain   : 0
% 5.96/2.15  #Close   : 0
% 5.96/2.15  
% 5.96/2.15  Ordering : KBO
% 5.96/2.15  
% 5.96/2.15  Simplification rules
% 5.96/2.15  ----------------------
% 5.96/2.15  #Subsume      : 100
% 5.96/2.15  #Demod        : 706
% 5.96/2.15  #Tautology    : 231
% 5.96/2.15  #SimpNegUnit  : 88
% 5.96/2.15  #BackRed      : 20
% 5.96/2.15  
% 5.96/2.15  #Partial instantiations: 0
% 5.96/2.15  #Strategies tried      : 1
% 5.96/2.15  
% 5.96/2.15  Timing (in seconds)
% 5.96/2.15  ----------------------
% 5.96/2.16  Preprocessing        : 0.35
% 5.96/2.16  Parsing              : 0.19
% 5.96/2.16  CNF conversion       : 0.03
% 5.96/2.16  Main loop            : 1.01
% 5.96/2.16  Inferencing          : 0.40
% 5.96/2.16  Reduction            : 0.30
% 5.96/2.16  Demodulation         : 0.20
% 5.96/2.16  BG Simplification    : 0.04
% 5.96/2.16  Subsumption          : 0.19
% 5.96/2.16  Abstraction          : 0.05
% 5.96/2.16  MUC search           : 0.00
% 5.96/2.16  Cooper               : 0.00
% 5.96/2.16  Total                : 1.44
% 5.96/2.16  Index Insertion      : 0.00
% 5.96/2.16  Index Deletion       : 0.00
% 5.96/2.16  Index Matching       : 0.00
% 5.96/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:07 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 236 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  239 ( 693 expanded)
%              Number of equality atoms :   30 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
              & ( ( v2_pre_topc(A)
                  & k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
               => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_81,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_subset_1(u1_struct_0(A),k2_struct_0(A),k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_101,plain,(
    k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,
    ( k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) != k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_107,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_26])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [A_36,B_37] :
      ( k4_subset_1(u1_struct_0(A_36),B_37,k3_subset_1(u1_struct_0(A_36),B_37)) = k2_struct_0(A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k4_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k2_struct_0(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_51),B_52),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_struct_0(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4])).

tff(c_164,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k2_struct_0(A_56),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_struct_0(A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56))) ) ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_179,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_164])).

tff(c_180,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_183,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_180])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_183])).

tff(c_188,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_189,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k7_subset_1(A_6,B_7,C_8),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    ! [B_34,A_35] :
      ( v4_pre_topc(B_34,A_35)
      | k2_pre_topc(A_35,B_34) != B_34
      | ~ v2_pre_topc(A_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_83,plain,(
    ! [A_35,B_7,C_8] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_35),B_7,C_8),A_35)
      | k2_pre_topc(A_35,k7_subset_1(u1_struct_0(A_35),B_7,C_8)) != k7_subset_1(u1_struct_0(A_35),B_7,C_8)
      | ~ v2_pre_topc(A_35)
      | ~ l1_pre_topc(A_35)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_35))) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_114,plain,(
    ! [A_42,B_43] :
      ( k7_subset_1(u1_struct_0(A_42),k2_struct_0(A_42),k7_subset_1(u1_struct_0(A_42),k2_struct_0(A_42),B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_9,B_11] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_9),k2_struct_0(A_9),B_11),A_9)
      | ~ v4_pre_topc(B_11,A_9)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_218,plain,(
    ! [B_60,A_61] :
      ( v3_pre_topc(B_60,A_61)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(A_61),k2_struct_0(A_61),B_60),A_61)
      | ~ m1_subset_1(k7_subset_1(u1_struct_0(A_61),k2_struct_0(A_61),B_60),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_struct_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_10])).

tff(c_235,plain,(
    ! [C_64,A_65] :
      ( v3_pre_topc(C_64,A_65)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(A_65),k2_struct_0(A_65),C_64),A_65)
      | ~ l1_pre_topc(A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_struct_0(A_65)
      | ~ m1_subset_1(k2_struct_0(A_65),k1_zfmisc_1(u1_struct_0(A_65))) ) ),
    inference(resolution,[status(thm)],[c_6,c_218])).

tff(c_291,plain,(
    ! [C_75,A_76] :
      ( v3_pre_topc(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_struct_0(A_76)
      | k2_pre_topc(A_76,k7_subset_1(u1_struct_0(A_76),k2_struct_0(A_76),C_75)) != k7_subset_1(u1_struct_0(A_76),k2_struct_0(A_76),C_75)
      | ~ v2_pre_topc(A_76)
      | ~ l1_pre_topc(A_76)
      | ~ m1_subset_1(k2_struct_0(A_76),k1_zfmisc_1(u1_struct_0(A_76))) ) ),
    inference(resolution,[status(thm)],[c_83,c_235])).

tff(c_297,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_291])).

tff(c_303,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_24,c_38,c_189,c_22,c_297])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_303])).

tff(c_306,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_348,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(k2_struct_0(A_87),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_87),B_88),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_struct_0(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4])).

tff(c_354,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1(k2_struct_0(A_89),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_struct_0(A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89))) ) ),
    inference(resolution,[status(thm)],[c_2,c_348])).

tff(c_369,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_354])).

tff(c_370,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_373,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_370])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_373])).

tff(c_379,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_378,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_316,plain,(
    ! [A_81,B_82] :
      ( k7_subset_1(u1_struct_0(A_81),k2_struct_0(A_81),k7_subset_1(u1_struct_0(A_81),k2_struct_0(A_81),B_82)) = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [B_11,A_9] :
      ( v4_pre_topc(B_11,A_9)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_9),k2_struct_0(A_9),B_11),A_9)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_429,plain,(
    ! [A_101,B_102] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_101),k2_struct_0(A_101),B_102),A_101)
      | ~ v3_pre_topc(B_102,A_101)
      | ~ m1_subset_1(k7_subset_1(u1_struct_0(A_101),k2_struct_0(A_101),B_102),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_struct_0(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_8])).

tff(c_438,plain,(
    ! [A_103,C_104] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_103),k2_struct_0(A_103),C_104),A_103)
      | ~ v3_pre_topc(C_104,A_103)
      | ~ l1_pre_topc(A_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_struct_0(A_103)
      | ~ m1_subset_1(k2_struct_0(A_103),k1_zfmisc_1(u1_struct_0(A_103))) ) ),
    inference(resolution,[status(thm)],[c_6,c_429])).

tff(c_41,plain,(
    ! [A_29,B_30] :
      ( k2_pre_topc(A_29,B_30) = B_30
      | ~ v4_pre_topc(B_30,A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,(
    ! [A_29,B_7,C_8] :
      ( k2_pre_topc(A_29,k7_subset_1(u1_struct_0(A_29),B_7,C_8)) = k7_subset_1(u1_struct_0(A_29),B_7,C_8)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(A_29),B_7,C_8),A_29)
      | ~ l1_pre_topc(A_29)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_29))) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_454,plain,(
    ! [A_108,C_109] :
      ( k2_pre_topc(A_108,k7_subset_1(u1_struct_0(A_108),k2_struct_0(A_108),C_109)) = k7_subset_1(u1_struct_0(A_108),k2_struct_0(A_108),C_109)
      | ~ v3_pre_topc(C_109,A_108)
      | ~ l1_pre_topc(A_108)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_struct_0(A_108)
      | ~ m1_subset_1(k2_struct_0(A_108),k1_zfmisc_1(u1_struct_0(A_108))) ) ),
    inference(resolution,[status(thm)],[c_438,c_53])).

tff(c_456,plain,(
    ! [C_109] :
      ( k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_109)) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_109)
      | ~ v3_pre_topc(C_109,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_378,c_454])).

tff(c_460,plain,(
    ! [C_110] :
      ( k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_110)) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_110)
      | ~ v3_pre_topc(C_110,'#skF_1')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_24,c_456])).

tff(c_307,plain,(
    k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) != k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_466,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_307])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_306,c_466])).

tff(c_479,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_531,plain,(
    ! [A_123,B_124] :
      ( k4_subset_1(u1_struct_0(A_123),B_124,k3_subset_1(u1_struct_0(A_123),B_124)) = k2_struct_0(A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_585,plain,(
    ! [A_135,B_136] :
      ( m1_subset_1(k2_struct_0(A_135),k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_135),B_136),k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_struct_0(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_4])).

tff(c_591,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1(k2_struct_0(A_137),k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_struct_0(A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137))) ) ),
    inference(resolution,[status(thm)],[c_2,c_585])).

tff(c_606,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_591])).

tff(c_607,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_610,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_607])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_610])).

tff(c_616,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_615,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_553,plain,(
    ! [A_129,B_130] :
      ( k7_subset_1(u1_struct_0(A_129),k2_struct_0(A_129),k7_subset_1(u1_struct_0(A_129),k2_struct_0(A_129),B_130)) = B_130
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_647,plain,(
    ! [A_145,B_146] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_145),k2_struct_0(A_145),B_146),A_145)
      | ~ v3_pre_topc(B_146,A_145)
      | ~ m1_subset_1(k7_subset_1(u1_struct_0(A_145),k2_struct_0(A_145),B_146),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_struct_0(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_8])).

tff(c_656,plain,(
    ! [A_147,C_148] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_147),k2_struct_0(A_147),C_148),A_147)
      | ~ v3_pre_topc(C_148,A_147)
      | ~ l1_pre_topc(A_147)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_struct_0(A_147)
      | ~ m1_subset_1(k2_struct_0(A_147),k1_zfmisc_1(u1_struct_0(A_147))) ) ),
    inference(resolution,[status(thm)],[c_6,c_647])).

tff(c_483,plain,(
    ! [A_116,B_117] :
      ( k2_pre_topc(A_116,B_117) = B_117
      | ~ v4_pre_topc(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_495,plain,(
    ! [A_116,B_7,C_8] :
      ( k2_pre_topc(A_116,k7_subset_1(u1_struct_0(A_116),B_7,C_8)) = k7_subset_1(u1_struct_0(A_116),B_7,C_8)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(A_116),B_7,C_8),A_116)
      | ~ l1_pre_topc(A_116)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_116))) ) ),
    inference(resolution,[status(thm)],[c_6,c_483])).

tff(c_690,plain,(
    ! [A_156,C_157] :
      ( k2_pre_topc(A_156,k7_subset_1(u1_struct_0(A_156),k2_struct_0(A_156),C_157)) = k7_subset_1(u1_struct_0(A_156),k2_struct_0(A_156),C_157)
      | ~ v3_pre_topc(C_157,A_156)
      | ~ l1_pre_topc(A_156)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_struct_0(A_156)
      | ~ m1_subset_1(k2_struct_0(A_156),k1_zfmisc_1(u1_struct_0(A_156))) ) ),
    inference(resolution,[status(thm)],[c_656,c_495])).

tff(c_692,plain,(
    ! [C_157] :
      ( k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_157)) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_157)
      | ~ v3_pre_topc(C_157,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(C_157,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_615,c_690])).

tff(c_704,plain,(
    ! [C_161] :
      ( k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_161)) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_161)
      | ~ v3_pre_topc(C_161,'#skF_1')
      | ~ m1_subset_1(C_161,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_24,c_692])).

tff(c_480,plain,(
    ~ v2_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) != k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')
    | v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_507,plain,(
    k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) != k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_480,c_34])).

tff(c_710,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_507])).

tff(c_722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_479,c_710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:37:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  %$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.77/1.43  
% 2.77/1.43  %Foreground sorts:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Background operators:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Foreground operators:
% 2.77/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.77/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.77/1.43  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.43  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.77/1.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.77/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.77/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.77/1.43  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.77/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.43  
% 2.77/1.45  tff(f_97, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) => (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) & ((v2_pre_topc(A) & (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_pre_topc)).
% 2.77/1.45  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.77/1.45  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.77/1.45  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_pre_topc)).
% 2.77/1.45  tff(f_35, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.77/1.45  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 2.77/1.45  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.77/1.45  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_subset_1(u1_struct_0(A), k2_struct_0(A), k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 2.77/1.45  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 2.77/1.45  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.45  tff(c_32, plain, (v3_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.45  tff(c_101, plain, (k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_32])).
% 2.77/1.45  tff(c_26, plain, (k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2'))!=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.45  tff(c_107, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_26])).
% 2.77/1.45  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.45  tff(c_12, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.77/1.45  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.45  tff(c_89, plain, (![A_36, B_37]: (k4_subset_1(u1_struct_0(A_36), B_37, k3_subset_1(u1_struct_0(A_36), B_37))=k2_struct_0(A_36) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.45  tff(c_4, plain, (![A_3, B_4, C_5]: (m1_subset_1(k4_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.45  tff(c_150, plain, (![A_51, B_52]: (m1_subset_1(k2_struct_0(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_51), B_52), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_struct_0(A_51))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4])).
% 2.77/1.45  tff(c_164, plain, (![A_56, B_57]: (m1_subset_1(k2_struct_0(A_56), k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_struct_0(A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))))), inference(resolution, [status(thm)], [c_2, c_150])).
% 2.77/1.45  tff(c_179, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_164])).
% 2.77/1.45  tff(c_180, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_179])).
% 2.77/1.45  tff(c_183, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_180])).
% 2.77/1.45  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_183])).
% 2.77/1.45  tff(c_188, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_179])).
% 2.77/1.45  tff(c_36, plain, (v3_pre_topc('#skF_2', '#skF_1') | v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.45  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 2.77/1.45  tff(c_189, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_179])).
% 2.77/1.45  tff(c_6, plain, (![A_6, B_7, C_8]: (m1_subset_1(k7_subset_1(A_6, B_7, C_8), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.45  tff(c_66, plain, (![B_34, A_35]: (v4_pre_topc(B_34, A_35) | k2_pre_topc(A_35, B_34)!=B_34 | ~v2_pre_topc(A_35) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.77/1.45  tff(c_83, plain, (![A_35, B_7, C_8]: (v4_pre_topc(k7_subset_1(u1_struct_0(A_35), B_7, C_8), A_35) | k2_pre_topc(A_35, k7_subset_1(u1_struct_0(A_35), B_7, C_8))!=k7_subset_1(u1_struct_0(A_35), B_7, C_8) | ~v2_pre_topc(A_35) | ~l1_pre_topc(A_35) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_35))))), inference(resolution, [status(thm)], [c_6, c_66])).
% 2.77/1.45  tff(c_114, plain, (![A_42, B_43]: (k7_subset_1(u1_struct_0(A_42), k2_struct_0(A_42), k7_subset_1(u1_struct_0(A_42), k2_struct_0(A_42), B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.77/1.45  tff(c_10, plain, (![A_9, B_11]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_9), k2_struct_0(A_9), B_11), A_9) | ~v4_pre_topc(B_11, A_9) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.77/1.45  tff(c_218, plain, (![B_60, A_61]: (v3_pre_topc(B_60, A_61) | ~v4_pre_topc(k7_subset_1(u1_struct_0(A_61), k2_struct_0(A_61), B_60), A_61) | ~m1_subset_1(k7_subset_1(u1_struct_0(A_61), k2_struct_0(A_61), B_60), k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_struct_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_114, c_10])).
% 2.77/1.45  tff(c_235, plain, (![C_64, A_65]: (v3_pre_topc(C_64, A_65) | ~v4_pre_topc(k7_subset_1(u1_struct_0(A_65), k2_struct_0(A_65), C_64), A_65) | ~l1_pre_topc(A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_struct_0(A_65) | ~m1_subset_1(k2_struct_0(A_65), k1_zfmisc_1(u1_struct_0(A_65))))), inference(resolution, [status(thm)], [c_6, c_218])).
% 2.77/1.45  tff(c_291, plain, (![C_75, A_76]: (v3_pre_topc(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_struct_0(A_76) | k2_pre_topc(A_76, k7_subset_1(u1_struct_0(A_76), k2_struct_0(A_76), C_75))!=k7_subset_1(u1_struct_0(A_76), k2_struct_0(A_76), C_75) | ~v2_pre_topc(A_76) | ~l1_pre_topc(A_76) | ~m1_subset_1(k2_struct_0(A_76), k1_zfmisc_1(u1_struct_0(A_76))))), inference(resolution, [status(thm)], [c_83, c_235])).
% 2.77/1.45  tff(c_297, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_101, c_291])).
% 2.77/1.45  tff(c_303, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_24, c_38, c_189, c_22, c_297])).
% 2.77/1.45  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_303])).
% 2.77/1.45  tff(c_306, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.77/1.45  tff(c_348, plain, (![A_87, B_88]: (m1_subset_1(k2_struct_0(A_87), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_87), B_88), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_struct_0(A_87))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4])).
% 2.77/1.45  tff(c_354, plain, (![A_89, B_90]: (m1_subset_1(k2_struct_0(A_89), k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_struct_0(A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))))), inference(resolution, [status(thm)], [c_2, c_348])).
% 2.77/1.45  tff(c_369, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_354])).
% 2.77/1.45  tff(c_370, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_369])).
% 2.77/1.45  tff(c_373, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_370])).
% 2.77/1.45  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_373])).
% 2.77/1.45  tff(c_379, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_369])).
% 2.77/1.45  tff(c_378, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_369])).
% 2.77/1.45  tff(c_316, plain, (![A_81, B_82]: (k7_subset_1(u1_struct_0(A_81), k2_struct_0(A_81), k7_subset_1(u1_struct_0(A_81), k2_struct_0(A_81), B_82))=B_82 | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.77/1.45  tff(c_8, plain, (![B_11, A_9]: (v4_pre_topc(B_11, A_9) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_9), k2_struct_0(A_9), B_11), A_9) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.77/1.45  tff(c_429, plain, (![A_101, B_102]: (v4_pre_topc(k7_subset_1(u1_struct_0(A_101), k2_struct_0(A_101), B_102), A_101) | ~v3_pre_topc(B_102, A_101) | ~m1_subset_1(k7_subset_1(u1_struct_0(A_101), k2_struct_0(A_101), B_102), k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_struct_0(A_101))), inference(superposition, [status(thm), theory('equality')], [c_316, c_8])).
% 2.77/1.45  tff(c_438, plain, (![A_103, C_104]: (v4_pre_topc(k7_subset_1(u1_struct_0(A_103), k2_struct_0(A_103), C_104), A_103) | ~v3_pre_topc(C_104, A_103) | ~l1_pre_topc(A_103) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_struct_0(A_103) | ~m1_subset_1(k2_struct_0(A_103), k1_zfmisc_1(u1_struct_0(A_103))))), inference(resolution, [status(thm)], [c_6, c_429])).
% 2.77/1.45  tff(c_41, plain, (![A_29, B_30]: (k2_pre_topc(A_29, B_30)=B_30 | ~v4_pre_topc(B_30, A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.77/1.45  tff(c_53, plain, (![A_29, B_7, C_8]: (k2_pre_topc(A_29, k7_subset_1(u1_struct_0(A_29), B_7, C_8))=k7_subset_1(u1_struct_0(A_29), B_7, C_8) | ~v4_pre_topc(k7_subset_1(u1_struct_0(A_29), B_7, C_8), A_29) | ~l1_pre_topc(A_29) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_29))))), inference(resolution, [status(thm)], [c_6, c_41])).
% 2.77/1.45  tff(c_454, plain, (![A_108, C_109]: (k2_pre_topc(A_108, k7_subset_1(u1_struct_0(A_108), k2_struct_0(A_108), C_109))=k7_subset_1(u1_struct_0(A_108), k2_struct_0(A_108), C_109) | ~v3_pre_topc(C_109, A_108) | ~l1_pre_topc(A_108) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_struct_0(A_108) | ~m1_subset_1(k2_struct_0(A_108), k1_zfmisc_1(u1_struct_0(A_108))))), inference(resolution, [status(thm)], [c_438, c_53])).
% 2.77/1.45  tff(c_456, plain, (![C_109]: (k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_109))=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_109) | ~v3_pre_topc(C_109, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_378, c_454])).
% 2.77/1.45  tff(c_460, plain, (![C_110]: (k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_110))=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_110) | ~v3_pre_topc(C_110, '#skF_1') | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_24, c_456])).
% 2.77/1.45  tff(c_307, plain, (k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2'))!=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_32])).
% 2.77/1.45  tff(c_466, plain, (~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_460, c_307])).
% 2.77/1.45  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_306, c_466])).
% 2.77/1.45  tff(c_479, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 2.77/1.45  tff(c_531, plain, (![A_123, B_124]: (k4_subset_1(u1_struct_0(A_123), B_124, k3_subset_1(u1_struct_0(A_123), B_124))=k2_struct_0(A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.45  tff(c_585, plain, (![A_135, B_136]: (m1_subset_1(k2_struct_0(A_135), k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_135), B_136), k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_struct_0(A_135))), inference(superposition, [status(thm), theory('equality')], [c_531, c_4])).
% 2.77/1.45  tff(c_591, plain, (![A_137, B_138]: (m1_subset_1(k2_struct_0(A_137), k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_struct_0(A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))))), inference(resolution, [status(thm)], [c_2, c_585])).
% 2.77/1.45  tff(c_606, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_591])).
% 2.77/1.45  tff(c_607, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_606])).
% 2.77/1.45  tff(c_610, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_607])).
% 2.77/1.45  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_610])).
% 2.77/1.45  tff(c_616, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_606])).
% 2.77/1.45  tff(c_615, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_606])).
% 2.77/1.45  tff(c_553, plain, (![A_129, B_130]: (k7_subset_1(u1_struct_0(A_129), k2_struct_0(A_129), k7_subset_1(u1_struct_0(A_129), k2_struct_0(A_129), B_130))=B_130 | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.77/1.45  tff(c_647, plain, (![A_145, B_146]: (v4_pre_topc(k7_subset_1(u1_struct_0(A_145), k2_struct_0(A_145), B_146), A_145) | ~v3_pre_topc(B_146, A_145) | ~m1_subset_1(k7_subset_1(u1_struct_0(A_145), k2_struct_0(A_145), B_146), k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_struct_0(A_145))), inference(superposition, [status(thm), theory('equality')], [c_553, c_8])).
% 2.77/1.45  tff(c_656, plain, (![A_147, C_148]: (v4_pre_topc(k7_subset_1(u1_struct_0(A_147), k2_struct_0(A_147), C_148), A_147) | ~v3_pre_topc(C_148, A_147) | ~l1_pre_topc(A_147) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_struct_0(A_147) | ~m1_subset_1(k2_struct_0(A_147), k1_zfmisc_1(u1_struct_0(A_147))))), inference(resolution, [status(thm)], [c_6, c_647])).
% 2.77/1.45  tff(c_483, plain, (![A_116, B_117]: (k2_pre_topc(A_116, B_117)=B_117 | ~v4_pre_topc(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.77/1.45  tff(c_495, plain, (![A_116, B_7, C_8]: (k2_pre_topc(A_116, k7_subset_1(u1_struct_0(A_116), B_7, C_8))=k7_subset_1(u1_struct_0(A_116), B_7, C_8) | ~v4_pre_topc(k7_subset_1(u1_struct_0(A_116), B_7, C_8), A_116) | ~l1_pre_topc(A_116) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_116))))), inference(resolution, [status(thm)], [c_6, c_483])).
% 2.77/1.45  tff(c_690, plain, (![A_156, C_157]: (k2_pre_topc(A_156, k7_subset_1(u1_struct_0(A_156), k2_struct_0(A_156), C_157))=k7_subset_1(u1_struct_0(A_156), k2_struct_0(A_156), C_157) | ~v3_pre_topc(C_157, A_156) | ~l1_pre_topc(A_156) | ~m1_subset_1(C_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_struct_0(A_156) | ~m1_subset_1(k2_struct_0(A_156), k1_zfmisc_1(u1_struct_0(A_156))))), inference(resolution, [status(thm)], [c_656, c_495])).
% 2.77/1.45  tff(c_692, plain, (![C_157]: (k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_157))=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_157) | ~v3_pre_topc(C_157, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1(C_157, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_615, c_690])).
% 2.77/1.45  tff(c_704, plain, (![C_161]: (k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_161))=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_161) | ~v3_pre_topc(C_161, '#skF_1') | ~m1_subset_1(C_161, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_24, c_692])).
% 2.77/1.45  tff(c_480, plain, (~v2_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 2.77/1.45  tff(c_34, plain, (k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2'))!=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2') | v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.45  tff(c_507, plain, (k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2'))!=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_480, c_34])).
% 2.77/1.45  tff(c_710, plain, (~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_704, c_507])).
% 2.77/1.45  tff(c_722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_479, c_710])).
% 2.77/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.45  
% 2.77/1.45  Inference rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Ref     : 0
% 2.77/1.45  #Sup     : 140
% 2.77/1.45  #Fact    : 0
% 2.77/1.45  #Define  : 0
% 2.77/1.45  #Split   : 11
% 2.77/1.45  #Chain   : 0
% 2.77/1.45  #Close   : 0
% 2.77/1.45  
% 2.77/1.45  Ordering : KBO
% 2.77/1.45  
% 2.77/1.45  Simplification rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Subsume      : 24
% 2.77/1.45  #Demod        : 49
% 2.77/1.45  #Tautology    : 47
% 2.77/1.45  #SimpNegUnit  : 6
% 2.77/1.45  #BackRed      : 0
% 2.77/1.45  
% 2.77/1.45  #Partial instantiations: 0
% 2.77/1.45  #Strategies tried      : 1
% 2.77/1.45  
% 2.77/1.45  Timing (in seconds)
% 2.77/1.45  ----------------------
% 2.77/1.46  Preprocessing        : 0.30
% 2.77/1.46  Parsing              : 0.17
% 2.77/1.46  CNF conversion       : 0.02
% 2.77/1.46  Main loop            : 0.39
% 2.77/1.46  Inferencing          : 0.16
% 2.77/1.46  Reduction            : 0.10
% 2.77/1.46  Demodulation         : 0.07
% 2.77/1.46  BG Simplification    : 0.02
% 2.77/1.46  Subsumption          : 0.07
% 2.77/1.46  Abstraction          : 0.02
% 2.77/1.46  MUC search           : 0.00
% 2.77/1.46  Cooper               : 0.00
% 2.77/1.46  Total                : 0.73
% 2.77/1.46  Index Insertion      : 0.00
% 2.77/1.46  Index Deletion       : 0.00
% 2.77/1.46  Index Matching       : 0.00
% 2.77/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

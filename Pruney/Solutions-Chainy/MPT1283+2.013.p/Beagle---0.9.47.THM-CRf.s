%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:22 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 283 expanded)
%              Number of leaves         :   25 ( 107 expanded)
%              Depth                    :   12
%              Number of atoms          :  147 ( 802 expanded)
%              Number of equality atoms :   24 (  77 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v4_pre_topc(B,A) )
             => ( v5_tops_1(B,A)
              <=> v6_tops_1(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tops_1)).

tff(f_48,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tops_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(c_32,plain,
    ( ~ v6_tops_1('#skF_2','#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_39,plain,(
    ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_57,plain,(
    ! [A_25,B_26] :
      ( k2_pre_topc(A_25,B_26) = B_26
      | ~ v4_pre_topc(B_26,A_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_57])).

tff(c_68,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_64])).

tff(c_353,plain,(
    ! [A_57,B_58] :
      ( k2_pre_topc(A_57,k1_tops_1(A_57,k2_pre_topc(A_57,B_58))) = k2_pre_topc(A_57,B_58)
      | ~ v3_pre_topc(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_360,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_353])).

tff(c_367,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_68,c_68,c_360])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( v5_tops_1(B_10,A_8)
      | k2_pre_topc(A_8,k1_tops_1(A_8,B_10)) != B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_370,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_10])).

tff(c_375,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_370])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_375])).

tff(c_378,plain,(
    ~ v6_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_379,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_383,plain,(
    ! [A_61,B_62] :
      ( k3_subset_1(A_61,k3_subset_1(A_61,B_62)) = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_389,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_383])).

tff(c_482,plain,(
    ! [B_73,A_74] :
      ( v6_tops_1(B_73,A_74)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_74),B_73),A_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_489,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_482])).

tff(c_491,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_379,c_489])).

tff(c_492,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_491])).

tff(c_495,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_492])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_495])).

tff(c_501,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_12,plain,(
    ! [A_8,B_10] :
      ( k2_pre_topc(A_8,k1_tops_1(A_8,B_10)) = B_10
      | ~ v5_tops_1(B_10,A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_503,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_501,c_12])).

tff(c_511,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_503])).

tff(c_583,plain,(
    ~ v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_511])).

tff(c_549,plain,(
    ! [B_79,A_80] :
      ( v3_pre_topc(B_79,A_80)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_80),B_79),A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_559,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_549])).

tff(c_562,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_501,c_24,c_559])).

tff(c_20,plain,(
    ! [A_14,B_16] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_14),B_16),A_14)
      | ~ v3_pre_topc(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( k2_pre_topc(A_5,B_7) = B_7
      | ~ v4_pre_topc(B_7,A_5)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_506,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_501,c_8])).

tff(c_514,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_506])).

tff(c_563,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_514])).

tff(c_566,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_563])).

tff(c_570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_566])).

tff(c_571,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_514])).

tff(c_590,plain,(
    ! [A_81,B_82] :
      ( k2_pre_topc(A_81,k1_tops_1(A_81,k2_pre_topc(A_81,B_82))) = k2_pre_topc(A_81,B_82)
      | ~ v3_pre_topc(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_592,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_501,c_590])).

tff(c_600,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_562,c_571,c_571,c_592])).

tff(c_607,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_10])).

tff(c_612,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_501,c_607])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_612])).

tff(c_616,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_511])).

tff(c_14,plain,(
    ! [B_13,A_11] :
      ( v6_tops_1(B_13,A_11)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_11),B_13),A_11)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_619,plain,
    ( v6_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_616,c_14])).

tff(c_622,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_619])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.38  %$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.80/1.38  
% 2.80/1.38  %Foreground sorts:
% 2.80/1.38  
% 2.80/1.38  
% 2.80/1.38  %Background operators:
% 2.80/1.38  
% 2.80/1.38  
% 2.80/1.38  %Foreground operators:
% 2.80/1.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.80/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.38  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 2.80/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.80/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.80/1.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.80/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.80/1.38  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.80/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.80/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.80/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.38  
% 2.80/1.40  tff(f_98, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v4_pre_topc(B, A)) => (v5_tops_1(B, A) <=> v6_tops_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tops_1)).
% 2.80/1.40  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.80/1.40  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tops_1)).
% 2.80/1.40  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 2.80/1.40  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.80/1.40  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.80/1.40  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> v5_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_tops_1)).
% 2.80/1.40  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 2.80/1.40  tff(c_32, plain, (~v6_tops_1('#skF_2', '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.80/1.40  tff(c_39, plain, (~v5_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 2.80/1.40  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.80/1.40  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.80/1.40  tff(c_26, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.80/1.40  tff(c_24, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.80/1.40  tff(c_57, plain, (![A_25, B_26]: (k2_pre_topc(A_25, B_26)=B_26 | ~v4_pre_topc(B_26, A_25) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.40  tff(c_64, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_57])).
% 2.80/1.40  tff(c_68, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_64])).
% 2.80/1.40  tff(c_353, plain, (![A_57, B_58]: (k2_pre_topc(A_57, k1_tops_1(A_57, k2_pre_topc(A_57, B_58)))=k2_pre_topc(A_57, B_58) | ~v3_pre_topc(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.80/1.40  tff(c_360, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_353])).
% 2.80/1.40  tff(c_367, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_68, c_68, c_360])).
% 2.80/1.40  tff(c_10, plain, (![B_10, A_8]: (v5_tops_1(B_10, A_8) | k2_pre_topc(A_8, k1_tops_1(A_8, B_10))!=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.40  tff(c_370, plain, (v5_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_367, c_10])).
% 2.80/1.40  tff(c_375, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_370])).
% 2.80/1.40  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_375])).
% 2.80/1.40  tff(c_378, plain, (~v6_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.80/1.40  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.40  tff(c_379, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.80/1.40  tff(c_383, plain, (![A_61, B_62]: (k3_subset_1(A_61, k3_subset_1(A_61, B_62))=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.40  tff(c_389, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_28, c_383])).
% 2.80/1.40  tff(c_482, plain, (![B_73, A_74]: (v6_tops_1(B_73, A_74) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_74), B_73), A_74) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.80/1.40  tff(c_489, plain, (v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_389, c_482])).
% 2.80/1.40  tff(c_491, plain, (v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_379, c_489])).
% 2.80/1.40  tff(c_492, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_491])).
% 2.80/1.40  tff(c_495, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_492])).
% 2.80/1.40  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_495])).
% 2.80/1.40  tff(c_501, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_491])).
% 2.80/1.40  tff(c_12, plain, (![A_8, B_10]: (k2_pre_topc(A_8, k1_tops_1(A_8, B_10))=B_10 | ~v5_tops_1(B_10, A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.40  tff(c_503, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_501, c_12])).
% 2.80/1.40  tff(c_511, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_503])).
% 2.80/1.40  tff(c_583, plain, (~v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_511])).
% 2.80/1.40  tff(c_549, plain, (![B_79, A_80]: (v3_pre_topc(B_79, A_80) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_80), B_79), A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.40  tff(c_559, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_389, c_549])).
% 2.80/1.40  tff(c_562, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_501, c_24, c_559])).
% 2.80/1.40  tff(c_20, plain, (![A_14, B_16]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_14), B_16), A_14) | ~v3_pre_topc(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.40  tff(c_8, plain, (![A_5, B_7]: (k2_pre_topc(A_5, B_7)=B_7 | ~v4_pre_topc(B_7, A_5) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.40  tff(c_506, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_501, c_8])).
% 2.80/1.40  tff(c_514, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_506])).
% 2.80/1.40  tff(c_563, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_514])).
% 2.80/1.40  tff(c_566, plain, (~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_563])).
% 2.80/1.40  tff(c_570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_566])).
% 2.80/1.40  tff(c_571, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_514])).
% 2.80/1.40  tff(c_590, plain, (![A_81, B_82]: (k2_pre_topc(A_81, k1_tops_1(A_81, k2_pre_topc(A_81, B_82)))=k2_pre_topc(A_81, B_82) | ~v3_pre_topc(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.80/1.40  tff(c_592, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_501, c_590])).
% 2.80/1.40  tff(c_600, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_562, c_571, c_571, c_592])).
% 2.80/1.40  tff(c_607, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_600, c_10])).
% 2.80/1.40  tff(c_612, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_501, c_607])).
% 2.80/1.40  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_583, c_612])).
% 2.80/1.40  tff(c_616, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_511])).
% 2.80/1.40  tff(c_14, plain, (![B_13, A_11]: (v6_tops_1(B_13, A_11) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_11), B_13), A_11) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.80/1.40  tff(c_619, plain, (v6_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_616, c_14])).
% 2.80/1.40  tff(c_622, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_619])).
% 2.80/1.40  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_378, c_622])).
% 2.80/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  Inference rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Ref     : 0
% 2.80/1.40  #Sup     : 121
% 2.80/1.40  #Fact    : 0
% 2.80/1.40  #Define  : 0
% 2.80/1.40  #Split   : 9
% 2.80/1.40  #Chain   : 0
% 2.80/1.40  #Close   : 0
% 2.80/1.40  
% 2.80/1.40  Ordering : KBO
% 2.80/1.40  
% 2.80/1.40  Simplification rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Subsume      : 7
% 2.80/1.40  #Demod        : 119
% 2.80/1.40  #Tautology    : 60
% 2.80/1.40  #SimpNegUnit  : 9
% 2.80/1.40  #BackRed      : 0
% 2.80/1.40  
% 2.80/1.40  #Partial instantiations: 0
% 2.80/1.40  #Strategies tried      : 1
% 2.80/1.40  
% 2.80/1.40  Timing (in seconds)
% 2.80/1.40  ----------------------
% 2.80/1.40  Preprocessing        : 0.31
% 2.80/1.40  Parsing              : 0.18
% 2.80/1.40  CNF conversion       : 0.02
% 2.80/1.40  Main loop            : 0.31
% 2.80/1.40  Inferencing          : 0.12
% 2.80/1.40  Reduction            : 0.09
% 2.80/1.40  Demodulation         : 0.06
% 2.80/1.40  BG Simplification    : 0.02
% 2.80/1.40  Subsumption          : 0.06
% 2.80/1.40  Abstraction          : 0.02
% 2.80/1.40  MUC search           : 0.00
% 2.80/1.40  Cooper               : 0.00
% 2.80/1.40  Total                : 0.66
% 2.80/1.40  Index Insertion      : 0.00
% 2.80/1.40  Index Deletion       : 0.00
% 2.80/1.40  Index Matching       : 0.00
% 2.80/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

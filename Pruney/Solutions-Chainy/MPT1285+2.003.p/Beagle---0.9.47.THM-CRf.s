%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:24 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  234 (1024 expanded)
%              Number of leaves         :   33 ( 357 expanded)
%              Depth                    :   18
%              Number of atoms          :  463 (3930 expanded)
%              Number of equality atoms :   62 ( 245 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v3_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v6_tops_1(D,B) )
                      & ( v6_tops_1(C,A)
                       => ( v3_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_67,axiom,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_56,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_5903,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_67,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_78,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_68,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_280,plain,(
    ! [A_72,B_73] :
      ( k1_tops_1(A_72,k2_pre_topc(A_72,B_73)) = B_73
      | ~ v6_tops_1(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_291,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_280])).

tff(c_300,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_291])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(A_56,k3_subset_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_80])).

tff(c_409,plain,(
    ! [A_80,B_81] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_80),B_81),A_80)
      | ~ v4_pre_topc(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_419,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_409])).

tff(c_425,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_419])).

tff(c_426,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_425])).

tff(c_430,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_433,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_430])).

tff(c_437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_433])).

tff(c_439,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( v3_pre_topc(k1_tops_1(A_26,B_27),A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_448,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_439,c_34])).

tff(c_468,plain,(
    v3_pre_topc(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_448])).

tff(c_748,plain,(
    ! [A_88,B_89] :
      ( k3_subset_1(u1_struct_0(A_88),k2_pre_topc(A_88,k3_subset_1(u1_struct_0(A_88),B_89))) = k1_tops_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_785,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_748])).

tff(c_796,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_439,c_785])).

tff(c_38,plain,(
    ! [B_32,A_30] :
      ( v4_pre_topc(B_32,A_30)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_30),B_32),A_30)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_808,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ v3_pre_topc(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_38])).

tff(c_822,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_468,c_808])).

tff(c_851,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_822])).

tff(c_856,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_851])).

tff(c_860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_856])).

tff(c_862,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_822])).

tff(c_871,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_862,c_34])).

tff(c_890,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_300,c_871])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_890])).

tff(c_894,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_893,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_895,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_893])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_927,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(B_94,k2_pre_topc(A_95,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_934,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_927])).

tff(c_941,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_934])).

tff(c_900,plain,(
    ! [A_90,B_91] :
      ( k3_subset_1(A_90,k3_subset_1(A_90,B_91)) = B_91
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_906,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_900])).

tff(c_1101,plain,(
    ! [B_108,A_109] :
      ( v4_pre_topc(B_108,A_109)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_109),B_108),A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1108,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_1101])).

tff(c_1113,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_894,c_1108])).

tff(c_1146,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1113])).

tff(c_1149,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_1146])).

tff(c_1153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1149])).

tff(c_1154,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_1155,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( k2_pre_topc(A_12,B_14) = B_14
      | ~ v4_pre_topc(B_14,A_12)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1204,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1155,c_18])).

tff(c_1220,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1154,c_1204])).

tff(c_1688,plain,(
    ! [A_130,B_131] :
      ( k3_subset_1(u1_struct_0(A_130),k2_pre_topc(A_130,k3_subset_1(u1_struct_0(A_130),B_131))) = k1_tops_1(A_130,B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1721,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_1688])).

tff(c_1739,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_906,c_1721])).

tff(c_1116,plain,(
    ! [A_110,B_111] :
      ( k1_tops_1(A_110,k2_pre_topc(A_110,B_111)) = B_111
      | ~ v6_tops_1(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1127,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1116])).

tff(c_1136,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_1127])).

tff(c_2112,plain,(
    ! [B_138,A_139] :
      ( v4_tops_1(B_138,A_139)
      | ~ r1_tarski(B_138,k2_pre_topc(A_139,k1_tops_1(A_139,B_138)))
      | ~ r1_tarski(k1_tops_1(A_139,k2_pre_topc(A_139,B_138)),B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2128,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_2112])).

tff(c_2136,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_6,c_941,c_1739,c_2128])).

tff(c_2138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_895,c_2136])).

tff(c_2140,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_893])).

tff(c_2142,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_2140,c_56])).

tff(c_26,plain,(
    ! [A_18,B_20] :
      ( r1_tarski(k1_tops_1(A_18,k2_pre_topc(A_18,B_20)),B_20)
      | ~ v4_tops_1(B_20,A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2172,plain,(
    ! [B_144,A_145] :
      ( r1_tarski(B_144,k2_pre_topc(A_145,B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2177,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2172])).

tff(c_2183,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2177])).

tff(c_2139,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_893])).

tff(c_2146,plain,(
    ! [A_142,B_143] :
      ( k3_subset_1(A_142,k3_subset_1(A_142,B_143)) = B_143
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2154,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_2146])).

tff(c_2337,plain,(
    ! [B_158,A_159] :
      ( v4_pre_topc(B_158,A_159)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_159),B_158),A_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2347,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2154,c_2337])).

tff(c_2351,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2139,c_2347])).

tff(c_2371,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2351])).

tff(c_2399,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_2371])).

tff(c_2403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2399])).

tff(c_2405,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2351])).

tff(c_2993,plain,(
    ! [A_180,B_181] :
      ( k3_subset_1(u1_struct_0(A_180),k2_pre_topc(A_180,k3_subset_1(u1_struct_0(A_180),B_181))) = k1_tops_1(A_180,B_181)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3039,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2154,c_2993])).

tff(c_3053,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2405,c_3039])).

tff(c_3169,plain,
    ( m1_subset_1(k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3053,c_8])).

tff(c_3771,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3169])).

tff(c_3774,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3771])).

tff(c_3778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_3774])).

tff(c_3780,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3169])).

tff(c_2404,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2351])).

tff(c_2472,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2405,c_18])).

tff(c_2487,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2404,c_2472])).

tff(c_3026,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2487,c_2993])).

tff(c_3047,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_2154,c_3026])).

tff(c_3264,plain,(
    ! [A_182,B_183,C_184] :
      ( r1_tarski(k1_tops_1(A_182,B_183),k1_tops_1(A_182,C_184))
      | ~ r1_tarski(B_183,C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3275,plain,(
    ! [C_184] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_184))
      | ~ r1_tarski('#skF_4',C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3047,c_3264])).

tff(c_3303,plain,(
    ! [C_184] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_184))
      | ~ r1_tarski('#skF_4',C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_3275])).

tff(c_3849,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_3780,c_3303])).

tff(c_3871,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_3849])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3895,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3871,c_2])).

tff(c_4091,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3895])).

tff(c_4094,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_4091])).

tff(c_4098,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_2142,c_4094])).

tff(c_4099,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3895])).

tff(c_28,plain,(
    ! [B_23,A_21] :
      ( v6_tops_1(B_23,A_21)
      | k1_tops_1(A_21,k2_pre_topc(A_21,B_23)) != B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4134,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4099,c_28])).

tff(c_4160,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_4134])).

tff(c_4162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_4160])).

tff(c_4164,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4165,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_4164,c_62])).

tff(c_4202,plain,(
    ! [B_207,A_208] :
      ( r1_tarski(B_207,k2_pre_topc(A_208,B_207))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4207,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_4202])).

tff(c_4213,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4207])).

tff(c_4163,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4176,plain,(
    ! [A_205,B_206] :
      ( k3_subset_1(A_205,k3_subset_1(A_205,B_206)) = B_206
      | ~ m1_subset_1(B_206,k1_zfmisc_1(A_205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4184,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_4176])).

tff(c_4358,plain,(
    ! [B_221,A_222] :
      ( v4_pre_topc(B_221,A_222)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_222),B_221),A_222)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4368,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4184,c_4358])).

tff(c_4372,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4163,c_4368])).

tff(c_4391,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4372])).

tff(c_4395,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_4391])).

tff(c_4399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4395])).

tff(c_4401,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_4372])).

tff(c_4929,plain,(
    ! [A_243,B_244] :
      ( k3_subset_1(u1_struct_0(A_243),k2_pre_topc(A_243,k3_subset_1(u1_struct_0(A_243),B_244))) = k1_tops_1(A_243,B_244)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4972,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4184,c_4929])).

tff(c_4984,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4401,c_4972])).

tff(c_5062,plain,
    ( m1_subset_1(k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4984,c_8])).

tff(c_5438,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5062])).

tff(c_5441,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_5438])).

tff(c_5445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_5441])).

tff(c_5447,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5062])).

tff(c_4400,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4372])).

tff(c_4406,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4401,c_18])).

tff(c_4418,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4400,c_4406])).

tff(c_4962,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4418,c_4929])).

tff(c_4980,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_4184,c_4962])).

tff(c_5121,plain,(
    ! [A_245,B_246,C_247] :
      ( r1_tarski(k1_tops_1(A_245,B_246),k1_tops_1(A_245,C_247))
      | ~ r1_tarski(B_246,C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5126,plain,(
    ! [C_247] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_247))
      | ~ r1_tarski('#skF_4',C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4980,c_5121])).

tff(c_5150,plain,(
    ! [C_247] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_247))
      | ~ r1_tarski('#skF_4',C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_5126])).

tff(c_5453,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_5447,c_5150])).

tff(c_5473,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4213,c_5453])).

tff(c_5496,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5473,c_2])).

tff(c_5818,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5496])).

tff(c_5821,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_5818])).

tff(c_5825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_4165,c_5821])).

tff(c_5826,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5496])).

tff(c_5863,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5826,c_28])).

tff(c_5889,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_5863])).

tff(c_5891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_5889])).

tff(c_5892,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6205,plain,(
    ! [A_286,B_287] :
      ( k1_tops_1(A_286,k2_pre_topc(A_286,B_287)) = B_287
      | ~ v6_tops_1(B_287,A_286)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6218,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_6205])).

tff(c_6230,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5892,c_6218])).

tff(c_5972,plain,(
    ! [A_270,B_271] :
      ( m1_subset_1(k2_pre_topc(A_270,B_271),k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6423,plain,(
    ! [A_296,B_297] :
      ( v3_pre_topc(k1_tops_1(A_296,k2_pre_topc(A_296,B_297)),A_296)
      | ~ v2_pre_topc(A_296)
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ l1_pre_topc(A_296) ) ),
    inference(resolution,[status(thm)],[c_5972,c_34])).

tff(c_6426,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6230,c_6423])).

tff(c_6431,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_52,c_6426])).

tff(c_6433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5903,c_6431])).

tff(c_6435,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6434,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6436,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6434])).

tff(c_6468,plain,(
    ! [B_302,A_303] :
      ( r1_tarski(B_302,k2_pre_topc(A_303,B_302))
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0(A_303)))
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6475,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_6468])).

tff(c_6482,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6475])).

tff(c_6442,plain,(
    ! [A_300,B_301] :
      ( k3_subset_1(A_300,k3_subset_1(A_300,B_301)) = B_301
      | ~ m1_subset_1(B_301,k1_zfmisc_1(A_300)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6451,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_6442])).

tff(c_6730,plain,(
    ! [B_320,A_321] :
      ( v4_pre_topc(B_320,A_321)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_321),B_320),A_321)
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6740,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6451,c_6730])).

tff(c_6746,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6435,c_6740])).

tff(c_6750,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6746])).

tff(c_6753,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_6750])).

tff(c_6757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6753])).

tff(c_6758,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_6746])).

tff(c_6759,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_6746])).

tff(c_6769,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6759,c_18])).

tff(c_6785,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6758,c_6769])).

tff(c_7241,plain,(
    ! [A_338,B_339] :
      ( k3_subset_1(u1_struct_0(A_338),k2_pre_topc(A_338,k3_subset_1(u1_struct_0(A_338),B_339))) = k1_tops_1(A_338,B_339)
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ l1_pre_topc(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7274,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6785,c_7241])).

tff(c_7292,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_6451,c_7274])).

tff(c_6810,plain,(
    ! [A_322,B_323] :
      ( k1_tops_1(A_322,k2_pre_topc(A_322,B_323)) = B_323
      | ~ v6_tops_1(B_323,A_322)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ l1_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6825,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_6810])).

tff(c_6840,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5892,c_6825])).

tff(c_7675,plain,(
    ! [B_346,A_347] :
      ( v4_tops_1(B_346,A_347)
      | ~ r1_tarski(B_346,k2_pre_topc(A_347,k1_tops_1(A_347,B_346)))
      | ~ r1_tarski(k1_tops_1(A_347,k2_pre_topc(A_347,B_346)),B_346)
      | ~ m1_subset_1(B_346,k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ l1_pre_topc(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7688,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6840,c_7675])).

tff(c_7700,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_6,c_6482,c_7292,c_7688])).

tff(c_7702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6436,c_7700])).

tff(c_7704,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_6434])).

tff(c_5893,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_7704,c_5893,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.54/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/2.53  
% 7.54/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/2.53  %$ v6_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.54/2.53  
% 7.54/2.53  %Foreground sorts:
% 7.54/2.53  
% 7.54/2.53  
% 7.54/2.53  %Background operators:
% 7.54/2.53  
% 7.54/2.53  
% 7.54/2.53  %Foreground operators:
% 7.54/2.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.54/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.54/2.53  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 7.54/2.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.54/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.54/2.53  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.54/2.53  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 7.54/2.53  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.54/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.54/2.53  tff('#skF_3', type, '#skF_3': $i).
% 7.54/2.53  tff('#skF_1', type, '#skF_1': $i).
% 7.54/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.54/2.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.54/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.54/2.53  tff('#skF_4', type, '#skF_4': $i).
% 7.54/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.54/2.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.54/2.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.54/2.53  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.54/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.54/2.53  
% 7.54/2.56  tff(f_161, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 7.54/2.56  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 7.54/2.56  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.54/2.56  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.54/2.56  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.54/2.56  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 7.54/2.56  tff(f_108, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 7.54/2.56  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 7.54/2.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.54/2.56  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 7.54/2.56  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.54/2.56  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 7.54/2.56  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 7.54/2.56  tff(c_56, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_5903, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 7.54/2.56  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_60, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_67, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 7.54/2.56  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_58, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_78, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 7.54/2.56  tff(c_64, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_68, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 7.54/2.56  tff(c_280, plain, (![A_72, B_73]: (k1_tops_1(A_72, k2_pre_topc(A_72, B_73))=B_73 | ~v6_tops_1(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.54/2.56  tff(c_291, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_280])).
% 7.54/2.56  tff(c_300, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_291])).
% 7.54/2.56  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.54/2.56  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.54/2.56  tff(c_80, plain, (![A_56, B_57]: (k3_subset_1(A_56, k3_subset_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.54/2.56  tff(c_89, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_80])).
% 7.54/2.56  tff(c_409, plain, (![A_80, B_81]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_80), B_81), A_80) | ~v4_pre_topc(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.54/2.56  tff(c_419, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_89, c_409])).
% 7.54/2.56  tff(c_425, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_419])).
% 7.54/2.56  tff(c_426, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_78, c_425])).
% 7.54/2.56  tff(c_430, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_426])).
% 7.54/2.56  tff(c_433, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_430])).
% 7.54/2.56  tff(c_437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_433])).
% 7.54/2.56  tff(c_439, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_426])).
% 7.54/2.56  tff(c_34, plain, (![A_26, B_27]: (v3_pre_topc(k1_tops_1(A_26, B_27), A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.54/2.56  tff(c_448, plain, (v3_pre_topc(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_439, c_34])).
% 7.54/2.56  tff(c_468, plain, (v3_pre_topc(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_448])).
% 7.54/2.56  tff(c_748, plain, (![A_88, B_89]: (k3_subset_1(u1_struct_0(A_88), k2_pre_topc(A_88, k3_subset_1(u1_struct_0(A_88), B_89)))=k1_tops_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.54/2.56  tff(c_785, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_89, c_748])).
% 7.54/2.56  tff(c_796, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_439, c_785])).
% 7.54/2.56  tff(c_38, plain, (![B_32, A_30]: (v4_pre_topc(B_32, A_30) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_30), B_32), A_30) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.54/2.56  tff(c_808, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~v3_pre_topc(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_796, c_38])).
% 7.54/2.56  tff(c_822, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_468, c_808])).
% 7.54/2.56  tff(c_851, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_822])).
% 7.54/2.56  tff(c_856, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_851])).
% 7.54/2.56  tff(c_860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_856])).
% 7.54/2.56  tff(c_862, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_822])).
% 7.54/2.56  tff(c_871, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_862, c_34])).
% 7.54/2.56  tff(c_890, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_300, c_871])).
% 7.54/2.56  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_890])).
% 7.54/2.56  tff(c_894, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 7.54/2.56  tff(c_893, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 7.54/2.56  tff(c_895, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_893])).
% 7.54/2.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.54/2.56  tff(c_927, plain, (![B_94, A_95]: (r1_tarski(B_94, k2_pre_topc(A_95, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.54/2.56  tff(c_934, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_927])).
% 7.54/2.56  tff(c_941, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_934])).
% 7.54/2.56  tff(c_900, plain, (![A_90, B_91]: (k3_subset_1(A_90, k3_subset_1(A_90, B_91))=B_91 | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.54/2.56  tff(c_906, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_900])).
% 7.54/2.56  tff(c_1101, plain, (![B_108, A_109]: (v4_pre_topc(B_108, A_109) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_109), B_108), A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.54/2.56  tff(c_1108, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_906, c_1101])).
% 7.54/2.56  tff(c_1113, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_894, c_1108])).
% 7.54/2.56  tff(c_1146, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1113])).
% 7.54/2.56  tff(c_1149, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1146])).
% 7.54/2.56  tff(c_1153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1149])).
% 7.54/2.56  tff(c_1154, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_1113])).
% 7.54/2.56  tff(c_1155, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1113])).
% 7.54/2.56  tff(c_18, plain, (![A_12, B_14]: (k2_pre_topc(A_12, B_14)=B_14 | ~v4_pre_topc(B_14, A_12) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.54/2.56  tff(c_1204, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1155, c_18])).
% 7.54/2.56  tff(c_1220, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1154, c_1204])).
% 7.54/2.56  tff(c_1688, plain, (![A_130, B_131]: (k3_subset_1(u1_struct_0(A_130), k2_pre_topc(A_130, k3_subset_1(u1_struct_0(A_130), B_131)))=k1_tops_1(A_130, B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.54/2.56  tff(c_1721, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1220, c_1688])).
% 7.54/2.56  tff(c_1739, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_906, c_1721])).
% 7.54/2.56  tff(c_1116, plain, (![A_110, B_111]: (k1_tops_1(A_110, k2_pre_topc(A_110, B_111))=B_111 | ~v6_tops_1(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.54/2.56  tff(c_1127, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1116])).
% 7.54/2.56  tff(c_1136, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_1127])).
% 7.54/2.56  tff(c_2112, plain, (![B_138, A_139]: (v4_tops_1(B_138, A_139) | ~r1_tarski(B_138, k2_pre_topc(A_139, k1_tops_1(A_139, B_138))) | ~r1_tarski(k1_tops_1(A_139, k2_pre_topc(A_139, B_138)), B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.54/2.56  tff(c_2128, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1136, c_2112])).
% 7.54/2.56  tff(c_2136, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_6, c_941, c_1739, c_2128])).
% 7.54/2.56  tff(c_2138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_895, c_2136])).
% 7.54/2.56  tff(c_2140, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_893])).
% 7.54/2.56  tff(c_2142, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_2140, c_56])).
% 7.54/2.56  tff(c_26, plain, (![A_18, B_20]: (r1_tarski(k1_tops_1(A_18, k2_pre_topc(A_18, B_20)), B_20) | ~v4_tops_1(B_20, A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.54/2.56  tff(c_2172, plain, (![B_144, A_145]: (r1_tarski(B_144, k2_pre_topc(A_145, B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.54/2.56  tff(c_2177, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_2172])).
% 7.54/2.56  tff(c_2183, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2177])).
% 7.54/2.56  tff(c_2139, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_893])).
% 7.54/2.56  tff(c_2146, plain, (![A_142, B_143]: (k3_subset_1(A_142, k3_subset_1(A_142, B_143))=B_143 | ~m1_subset_1(B_143, k1_zfmisc_1(A_142)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.54/2.56  tff(c_2154, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_44, c_2146])).
% 7.54/2.56  tff(c_2337, plain, (![B_158, A_159]: (v4_pre_topc(B_158, A_159) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_159), B_158), A_159) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.54/2.56  tff(c_2347, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2154, c_2337])).
% 7.54/2.56  tff(c_2351, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2139, c_2347])).
% 7.54/2.56  tff(c_2371, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_2351])).
% 7.54/2.56  tff(c_2399, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_2371])).
% 7.54/2.56  tff(c_2403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2399])).
% 7.54/2.56  tff(c_2405, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_2351])).
% 7.54/2.56  tff(c_2993, plain, (![A_180, B_181]: (k3_subset_1(u1_struct_0(A_180), k2_pre_topc(A_180, k3_subset_1(u1_struct_0(A_180), B_181)))=k1_tops_1(A_180, B_181) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.54/2.56  tff(c_3039, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2154, c_2993])).
% 7.54/2.56  tff(c_3053, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2405, c_3039])).
% 7.54/2.56  tff(c_3169, plain, (m1_subset_1(k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3053, c_8])).
% 7.54/2.56  tff(c_3771, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3169])).
% 7.54/2.56  tff(c_3774, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3771])).
% 7.54/2.56  tff(c_3778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_3774])).
% 7.54/2.56  tff(c_3780, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3169])).
% 7.54/2.56  tff(c_2404, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_2351])).
% 7.54/2.56  tff(c_2472, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2405, c_18])).
% 7.54/2.56  tff(c_2487, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2404, c_2472])).
% 7.54/2.56  tff(c_3026, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2487, c_2993])).
% 7.54/2.56  tff(c_3047, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_2154, c_3026])).
% 7.54/2.56  tff(c_3264, plain, (![A_182, B_183, C_184]: (r1_tarski(k1_tops_1(A_182, B_183), k1_tops_1(A_182, C_184)) | ~r1_tarski(B_183, C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0(A_182))) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.54/2.56  tff(c_3275, plain, (![C_184]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_184)) | ~r1_tarski('#skF_4', C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3047, c_3264])).
% 7.54/2.56  tff(c_3303, plain, (![C_184]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_184)) | ~r1_tarski('#skF_4', C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_3275])).
% 7.54/2.56  tff(c_3849, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_3780, c_3303])).
% 7.54/2.56  tff(c_3871, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2183, c_3849])).
% 7.54/2.56  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.54/2.56  tff(c_3895, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(resolution, [status(thm)], [c_3871, c_2])).
% 7.54/2.56  tff(c_4091, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_3895])).
% 7.54/2.56  tff(c_4094, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_4091])).
% 7.54/2.56  tff(c_4098, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_2142, c_4094])).
% 7.54/2.56  tff(c_4099, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_3895])).
% 7.54/2.56  tff(c_28, plain, (![B_23, A_21]: (v6_tops_1(B_23, A_21) | k1_tops_1(A_21, k2_pre_topc(A_21, B_23))!=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.54/2.56  tff(c_4134, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4099, c_28])).
% 7.54/2.56  tff(c_4160, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_4134])).
% 7.54/2.56  tff(c_4162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_4160])).
% 7.54/2.56  tff(c_4164, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 7.54/2.56  tff(c_62, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_4165, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_4164, c_62])).
% 7.54/2.56  tff(c_4202, plain, (![B_207, A_208]: (r1_tarski(B_207, k2_pre_topc(A_208, B_207)) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.54/2.56  tff(c_4207, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_4202])).
% 7.54/2.56  tff(c_4213, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4207])).
% 7.54/2.56  tff(c_4163, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 7.54/2.56  tff(c_4176, plain, (![A_205, B_206]: (k3_subset_1(A_205, k3_subset_1(A_205, B_206))=B_206 | ~m1_subset_1(B_206, k1_zfmisc_1(A_205)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.54/2.56  tff(c_4184, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_44, c_4176])).
% 7.54/2.56  tff(c_4358, plain, (![B_221, A_222]: (v4_pre_topc(B_221, A_222) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_222), B_221), A_222) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.54/2.56  tff(c_4368, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4184, c_4358])).
% 7.54/2.56  tff(c_4372, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4163, c_4368])).
% 7.54/2.56  tff(c_4391, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_4372])).
% 7.54/2.56  tff(c_4395, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_4391])).
% 7.54/2.56  tff(c_4399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_4395])).
% 7.54/2.56  tff(c_4401, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_4372])).
% 7.54/2.56  tff(c_4929, plain, (![A_243, B_244]: (k3_subset_1(u1_struct_0(A_243), k2_pre_topc(A_243, k3_subset_1(u1_struct_0(A_243), B_244)))=k1_tops_1(A_243, B_244) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.54/2.56  tff(c_4972, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4184, c_4929])).
% 7.54/2.56  tff(c_4984, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4401, c_4972])).
% 7.54/2.56  tff(c_5062, plain, (m1_subset_1(k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4984, c_8])).
% 7.54/2.56  tff(c_5438, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_5062])).
% 7.54/2.56  tff(c_5441, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_5438])).
% 7.54/2.56  tff(c_5445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_5441])).
% 7.54/2.56  tff(c_5447, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_5062])).
% 7.54/2.56  tff(c_4400, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_4372])).
% 7.54/2.56  tff(c_4406, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4401, c_18])).
% 7.54/2.56  tff(c_4418, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4400, c_4406])).
% 7.54/2.56  tff(c_4962, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4418, c_4929])).
% 7.54/2.56  tff(c_4980, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_4184, c_4962])).
% 7.54/2.56  tff(c_5121, plain, (![A_245, B_246, C_247]: (r1_tarski(k1_tops_1(A_245, B_246), k1_tops_1(A_245, C_247)) | ~r1_tarski(B_246, C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0(A_245))) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.54/2.56  tff(c_5126, plain, (![C_247]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_247)) | ~r1_tarski('#skF_4', C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4980, c_5121])).
% 7.54/2.56  tff(c_5150, plain, (![C_247]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_247)) | ~r1_tarski('#skF_4', C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_5126])).
% 7.54/2.56  tff(c_5453, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_5447, c_5150])).
% 7.54/2.56  tff(c_5473, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4213, c_5453])).
% 7.54/2.56  tff(c_5496, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(resolution, [status(thm)], [c_5473, c_2])).
% 7.54/2.56  tff(c_5818, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_5496])).
% 7.54/2.56  tff(c_5821, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_5818])).
% 7.54/2.56  tff(c_5825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_4165, c_5821])).
% 7.54/2.56  tff(c_5826, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_5496])).
% 7.54/2.56  tff(c_5863, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5826, c_28])).
% 7.54/2.56  tff(c_5889, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_5863])).
% 7.54/2.56  tff(c_5891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_5889])).
% 7.54/2.56  tff(c_5892, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_60])).
% 7.54/2.56  tff(c_6205, plain, (![A_286, B_287]: (k1_tops_1(A_286, k2_pre_topc(A_286, B_287))=B_287 | ~v6_tops_1(B_287, A_286) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_pre_topc(A_286))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.54/2.56  tff(c_6218, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_6205])).
% 7.54/2.56  tff(c_6230, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5892, c_6218])).
% 7.54/2.56  tff(c_5972, plain, (![A_270, B_271]: (m1_subset_1(k2_pre_topc(A_270, B_271), k1_zfmisc_1(u1_struct_0(A_270))) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.54/2.56  tff(c_6423, plain, (![A_296, B_297]: (v3_pre_topc(k1_tops_1(A_296, k2_pre_topc(A_296, B_297)), A_296) | ~v2_pre_topc(A_296) | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0(A_296))) | ~l1_pre_topc(A_296))), inference(resolution, [status(thm)], [c_5972, c_34])).
% 7.54/2.56  tff(c_6426, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6230, c_6423])).
% 7.54/2.56  tff(c_6431, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_52, c_6426])).
% 7.54/2.56  tff(c_6433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5903, c_6431])).
% 7.54/2.56  tff(c_6435, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 7.54/2.56  tff(c_6434, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 7.54/2.56  tff(c_6436, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_6434])).
% 7.54/2.56  tff(c_6468, plain, (![B_302, A_303]: (r1_tarski(B_302, k2_pre_topc(A_303, B_302)) | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0(A_303))) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.54/2.56  tff(c_6475, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_6468])).
% 7.54/2.56  tff(c_6482, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6475])).
% 7.54/2.56  tff(c_6442, plain, (![A_300, B_301]: (k3_subset_1(A_300, k3_subset_1(A_300, B_301))=B_301 | ~m1_subset_1(B_301, k1_zfmisc_1(A_300)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.54/2.56  tff(c_6451, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_6442])).
% 7.54/2.56  tff(c_6730, plain, (![B_320, A_321]: (v4_pre_topc(B_320, A_321) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_321), B_320), A_321) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_321))) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.54/2.56  tff(c_6740, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6451, c_6730])).
% 7.54/2.56  tff(c_6746, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6435, c_6740])).
% 7.54/2.56  tff(c_6750, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_6746])).
% 7.54/2.56  tff(c_6753, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_6750])).
% 7.54/2.56  tff(c_6757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_6753])).
% 7.54/2.56  tff(c_6758, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_6746])).
% 7.54/2.56  tff(c_6759, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_6746])).
% 7.54/2.56  tff(c_6769, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6759, c_18])).
% 7.54/2.56  tff(c_6785, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6758, c_6769])).
% 7.54/2.56  tff(c_7241, plain, (![A_338, B_339]: (k3_subset_1(u1_struct_0(A_338), k2_pre_topc(A_338, k3_subset_1(u1_struct_0(A_338), B_339)))=k1_tops_1(A_338, B_339) | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0(A_338))) | ~l1_pre_topc(A_338))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.54/2.56  tff(c_7274, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6785, c_7241])).
% 7.54/2.56  tff(c_7292, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_6451, c_7274])).
% 7.54/2.56  tff(c_6810, plain, (![A_322, B_323]: (k1_tops_1(A_322, k2_pre_topc(A_322, B_323))=B_323 | ~v6_tops_1(B_323, A_322) | ~m1_subset_1(B_323, k1_zfmisc_1(u1_struct_0(A_322))) | ~l1_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.54/2.56  tff(c_6825, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_6810])).
% 7.54/2.56  tff(c_6840, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5892, c_6825])).
% 7.54/2.56  tff(c_7675, plain, (![B_346, A_347]: (v4_tops_1(B_346, A_347) | ~r1_tarski(B_346, k2_pre_topc(A_347, k1_tops_1(A_347, B_346))) | ~r1_tarski(k1_tops_1(A_347, k2_pre_topc(A_347, B_346)), B_346) | ~m1_subset_1(B_346, k1_zfmisc_1(u1_struct_0(A_347))) | ~l1_pre_topc(A_347))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.54/2.56  tff(c_7688, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6840, c_7675])).
% 7.54/2.56  tff(c_7700, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_6, c_6482, c_7292, c_7688])).
% 7.54/2.56  tff(c_7702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6436, c_7700])).
% 7.54/2.56  tff(c_7704, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_6434])).
% 7.54/2.56  tff(c_5893, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 7.54/2.56  tff(c_54, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.54/2.56  tff(c_7708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6435, c_7704, c_5893, c_54])).
% 7.54/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/2.56  
% 7.54/2.56  Inference rules
% 7.54/2.56  ----------------------
% 7.54/2.56  #Ref     : 0
% 7.54/2.56  #Sup     : 1621
% 7.54/2.56  #Fact    : 0
% 7.54/2.56  #Define  : 0
% 7.54/2.56  #Split   : 104
% 7.54/2.56  #Chain   : 0
% 7.54/2.56  #Close   : 0
% 7.54/2.56  
% 7.54/2.56  Ordering : KBO
% 7.54/2.56  
% 7.54/2.56  Simplification rules
% 7.54/2.56  ----------------------
% 7.54/2.56  #Subsume      : 138
% 7.54/2.56  #Demod        : 2217
% 7.54/2.56  #Tautology    : 699
% 7.54/2.56  #SimpNegUnit  : 43
% 7.54/2.56  #BackRed      : 26
% 7.54/2.56  
% 7.54/2.56  #Partial instantiations: 0
% 7.54/2.56  #Strategies tried      : 1
% 7.54/2.56  
% 7.54/2.56  Timing (in seconds)
% 7.54/2.56  ----------------------
% 7.54/2.56  Preprocessing        : 0.35
% 7.54/2.56  Parsing              : 0.19
% 7.54/2.56  CNF conversion       : 0.03
% 7.54/2.56  Main loop            : 1.41
% 7.54/2.56  Inferencing          : 0.45
% 7.54/2.56  Reduction            : 0.54
% 7.54/2.56  Demodulation         : 0.38
% 7.54/2.56  BG Simplification    : 0.06
% 7.54/2.56  Subsumption          : 0.26
% 7.54/2.56  Abstraction          : 0.07
% 7.54/2.56  MUC search           : 0.00
% 7.54/2.56  Cooper               : 0.00
% 7.54/2.56  Total                : 1.82
% 7.54/2.56  Index Insertion      : 0.00
% 7.54/2.56  Index Deletion       : 0.00
% 7.54/2.56  Index Matching       : 0.00
% 7.54/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------

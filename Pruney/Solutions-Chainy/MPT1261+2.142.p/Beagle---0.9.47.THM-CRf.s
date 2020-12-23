%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:31 EST 2020

% Result     : Theorem 18.20s
% Output     : CNFRefutation 18.47s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 156 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 326 expanded)
%              Number of equality atoms :   45 (  92 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_70336,plain,(
    ! [A_785,B_786,C_787] :
      ( k7_subset_1(A_785,B_786,C_787) = k4_xboole_0(B_786,C_787)
      | ~ m1_subset_1(B_786,k1_zfmisc_1(A_785)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70339,plain,(
    ! [C_787] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_787) = k4_xboole_0('#skF_2',C_787) ),
    inference(resolution,[status(thm)],[c_36,c_70336])).

tff(c_42,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_240,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1757,plain,(
    ! [B_120,A_121] :
      ( v4_pre_topc(B_120,A_121)
      | k2_pre_topc(A_121,B_120) != B_120
      | ~ v2_pre_topc(A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1763,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1757])).

tff(c_1767,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_1763])).

tff(c_1768,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_1767])).

tff(c_794,plain,(
    ! [B_90,A_91] :
      ( r1_tarski(B_90,k2_pre_topc(A_91,B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_796,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_794])).

tff(c_799,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_796])).

tff(c_1016,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(k1_tops_1(A_100,B_101),B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1018,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1016])).

tff(c_1021,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1018])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1029,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1021,c_10])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5554,plain,(
    ! [C_237] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_237)
      | ~ r1_tarski('#skF_2',C_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_8])).

tff(c_69065,plain,(
    ! [C_724] :
      ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_724) = C_724
      | ~ r1_tarski('#skF_2',C_724) ) ),
    inference(resolution,[status(thm)],[c_5554,c_10])).

tff(c_707,plain,(
    ! [A_84,B_85,C_86] :
      ( k7_subset_1(A_84,B_85,C_86) = k4_xboole_0(B_85,C_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_774,plain,(
    ! [C_89] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_89) = k4_xboole_0('#skF_2',C_89) ),
    inference(resolution,[status(thm)],[c_36,c_707])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_114,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_780,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_114])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_876,plain,(
    k5_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_18])).

tff(c_3972,plain,(
    k5_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_876])).

tff(c_1215,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k2_pre_topc(A_104,B_105),k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4727,plain,(
    ! [A_201,B_202,C_203] :
      ( k7_subset_1(u1_struct_0(A_201),k2_pre_topc(A_201,B_202),C_203) = k4_xboole_0(k2_pre_topc(A_201,B_202),C_203)
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(resolution,[status(thm)],[c_1215,c_22])).

tff(c_4731,plain,(
    ! [C_203] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_203) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_203)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_4727])).

tff(c_4899,plain,(
    ! [C_208] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_208) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_208) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4731])).

tff(c_32,plain,(
    ! [A_30,B_32] :
      ( k7_subset_1(u1_struct_0(A_30),k2_pre_topc(A_30,B_32),k1_tops_1(A_30,B_32)) = k2_tops_1(A_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4906,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4899,c_32])).

tff(c_4916,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_4906])).

tff(c_27098,plain,(
    k5_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4916,c_18])).

tff(c_27131,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_27098])).

tff(c_69163,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_69065,c_27131])).

tff(c_69364,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_69163])).

tff(c_69366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1768,c_69364])).

tff(c_69367,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_69744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69367,c_114])).

tff(c_69745,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_69872,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69745,c_42])).

tff(c_70403,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70339,c_69872])).

tff(c_71163,plain,(
    ! [A_815,B_816] :
      ( k2_pre_topc(A_815,B_816) = B_816
      | ~ v4_pre_topc(B_816,A_815)
      | ~ m1_subset_1(B_816,k1_zfmisc_1(u1_struct_0(A_815)))
      | ~ l1_pre_topc(A_815) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_71169,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_71163])).

tff(c_71173,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_69745,c_71169])).

tff(c_71802,plain,(
    ! [A_847,B_848] :
      ( k7_subset_1(u1_struct_0(A_847),k2_pre_topc(A_847,B_848),k1_tops_1(A_847,B_848)) = k2_tops_1(A_847,B_848)
      | ~ m1_subset_1(B_848,k1_zfmisc_1(u1_struct_0(A_847)))
      | ~ l1_pre_topc(A_847) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_71811,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_71173,c_71802])).

tff(c_71815,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_70339,c_71811])).

tff(c_71817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70403,c_71815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.20/10.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.20/10.37  
% 18.20/10.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.20/10.37  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 18.20/10.37  
% 18.20/10.37  %Foreground sorts:
% 18.20/10.37  
% 18.20/10.37  
% 18.20/10.37  %Background operators:
% 18.20/10.37  
% 18.20/10.37  
% 18.20/10.37  %Foreground operators:
% 18.20/10.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.20/10.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.20/10.37  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 18.20/10.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.20/10.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 18.20/10.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.20/10.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.20/10.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.20/10.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 18.20/10.37  tff('#skF_2', type, '#skF_2': $i).
% 18.20/10.37  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 18.20/10.37  tff('#skF_1', type, '#skF_1': $i).
% 18.20/10.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.20/10.37  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 18.20/10.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.20/10.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.20/10.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.20/10.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 18.20/10.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.20/10.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.20/10.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.20/10.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 18.20/10.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.20/10.37  
% 18.47/10.39  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 18.47/10.39  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 18.47/10.39  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 18.47/10.39  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 18.47/10.39  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 18.47/10.39  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.47/10.39  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 18.47/10.39  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 18.47/10.39  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 18.47/10.39  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 18.47/10.39  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.47/10.39  tff(c_70336, plain, (![A_785, B_786, C_787]: (k7_subset_1(A_785, B_786, C_787)=k4_xboole_0(B_786, C_787) | ~m1_subset_1(B_786, k1_zfmisc_1(A_785)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.47/10.39  tff(c_70339, plain, (![C_787]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_787)=k4_xboole_0('#skF_2', C_787))), inference(resolution, [status(thm)], [c_36, c_70336])).
% 18.47/10.39  tff(c_42, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.47/10.39  tff(c_240, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 18.47/10.39  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.47/10.39  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.47/10.39  tff(c_1757, plain, (![B_120, A_121]: (v4_pre_topc(B_120, A_121) | k2_pre_topc(A_121, B_120)!=B_120 | ~v2_pre_topc(A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.47/10.39  tff(c_1763, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1757])).
% 18.47/10.39  tff(c_1767, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_1763])).
% 18.47/10.39  tff(c_1768, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_240, c_1767])).
% 18.47/10.39  tff(c_794, plain, (![B_90, A_91]: (r1_tarski(B_90, k2_pre_topc(A_91, B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.47/10.39  tff(c_796, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_794])).
% 18.47/10.39  tff(c_799, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_796])).
% 18.47/10.39  tff(c_1016, plain, (![A_100, B_101]: (r1_tarski(k1_tops_1(A_100, B_101), B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.47/10.39  tff(c_1018, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1016])).
% 18.47/10.39  tff(c_1021, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1018])).
% 18.47/10.39  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.47/10.39  tff(c_1029, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_1021, c_10])).
% 18.47/10.39  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.47/10.39  tff(c_5554, plain, (![C_237]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_237) | ~r1_tarski('#skF_2', C_237))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_8])).
% 18.47/10.39  tff(c_69065, plain, (![C_724]: (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_724)=C_724 | ~r1_tarski('#skF_2', C_724))), inference(resolution, [status(thm)], [c_5554, c_10])).
% 18.47/10.39  tff(c_707, plain, (![A_84, B_85, C_86]: (k7_subset_1(A_84, B_85, C_86)=k4_xboole_0(B_85, C_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.47/10.39  tff(c_774, plain, (![C_89]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_89)=k4_xboole_0('#skF_2', C_89))), inference(resolution, [status(thm)], [c_36, c_707])).
% 18.47/10.39  tff(c_48, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.47/10.39  tff(c_114, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 18.47/10.39  tff(c_780, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_774, c_114])).
% 18.47/10.39  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.47/10.39  tff(c_876, plain, (k5_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_780, c_18])).
% 18.47/10.39  tff(c_3972, plain, (k5_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1029, c_876])).
% 18.47/10.39  tff(c_1215, plain, (![A_104, B_105]: (m1_subset_1(k2_pre_topc(A_104, B_105), k1_zfmisc_1(u1_struct_0(A_104))) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.47/10.39  tff(c_22, plain, (![A_19, B_20, C_21]: (k7_subset_1(A_19, B_20, C_21)=k4_xboole_0(B_20, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.47/10.39  tff(c_4727, plain, (![A_201, B_202, C_203]: (k7_subset_1(u1_struct_0(A_201), k2_pre_topc(A_201, B_202), C_203)=k4_xboole_0(k2_pre_topc(A_201, B_202), C_203) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(resolution, [status(thm)], [c_1215, c_22])).
% 18.47/10.39  tff(c_4731, plain, (![C_203]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_203)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_203) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_4727])).
% 18.47/10.39  tff(c_4899, plain, (![C_208]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_208)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_208))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4731])).
% 18.47/10.39  tff(c_32, plain, (![A_30, B_32]: (k7_subset_1(u1_struct_0(A_30), k2_pre_topc(A_30, B_32), k1_tops_1(A_30, B_32))=k2_tops_1(A_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.47/10.39  tff(c_4906, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4899, c_32])).
% 18.47/10.39  tff(c_4916, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_4906])).
% 18.47/10.39  tff(c_27098, plain, (k5_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4916, c_18])).
% 18.47/10.39  tff(c_27131, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_27098])).
% 18.47/10.39  tff(c_69163, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_69065, c_27131])).
% 18.47/10.39  tff(c_69364, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_799, c_69163])).
% 18.47/10.39  tff(c_69366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1768, c_69364])).
% 18.47/10.39  tff(c_69367, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 18.47/10.39  tff(c_69744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69367, c_114])).
% 18.47/10.39  tff(c_69745, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 18.47/10.39  tff(c_69872, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69745, c_42])).
% 18.47/10.39  tff(c_70403, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70339, c_69872])).
% 18.47/10.39  tff(c_71163, plain, (![A_815, B_816]: (k2_pre_topc(A_815, B_816)=B_816 | ~v4_pre_topc(B_816, A_815) | ~m1_subset_1(B_816, k1_zfmisc_1(u1_struct_0(A_815))) | ~l1_pre_topc(A_815))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.47/10.39  tff(c_71169, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_71163])).
% 18.47/10.39  tff(c_71173, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_69745, c_71169])).
% 18.47/10.39  tff(c_71802, plain, (![A_847, B_848]: (k7_subset_1(u1_struct_0(A_847), k2_pre_topc(A_847, B_848), k1_tops_1(A_847, B_848))=k2_tops_1(A_847, B_848) | ~m1_subset_1(B_848, k1_zfmisc_1(u1_struct_0(A_847))) | ~l1_pre_topc(A_847))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.47/10.39  tff(c_71811, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_71173, c_71802])).
% 18.47/10.39  tff(c_71815, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_70339, c_71811])).
% 18.47/10.39  tff(c_71817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70403, c_71815])).
% 18.47/10.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.47/10.39  
% 18.47/10.39  Inference rules
% 18.47/10.39  ----------------------
% 18.47/10.39  #Ref     : 4
% 18.47/10.39  #Sup     : 18714
% 18.47/10.39  #Fact    : 0
% 18.47/10.39  #Define  : 0
% 18.47/10.39  #Split   : 7
% 18.47/10.39  #Chain   : 0
% 18.47/10.39  #Close   : 0
% 18.47/10.39  
% 18.47/10.39  Ordering : KBO
% 18.47/10.39  
% 18.47/10.39  Simplification rules
% 18.47/10.39  ----------------------
% 18.47/10.39  #Subsume      : 5003
% 18.47/10.39  #Demod        : 11342
% 18.47/10.39  #Tautology    : 9829
% 18.47/10.39  #SimpNegUnit  : 274
% 18.47/10.39  #BackRed      : 8
% 18.47/10.39  
% 18.47/10.39  #Partial instantiations: 0
% 18.47/10.39  #Strategies tried      : 1
% 18.47/10.39  
% 18.47/10.39  Timing (in seconds)
% 18.47/10.39  ----------------------
% 18.47/10.39  Preprocessing        : 0.33
% 18.47/10.39  Parsing              : 0.18
% 18.47/10.39  CNF conversion       : 0.02
% 18.47/10.39  Main loop            : 9.29
% 18.47/10.39  Inferencing          : 1.21
% 18.47/10.39  Reduction            : 5.54
% 18.47/10.39  Demodulation         : 4.88
% 18.47/10.39  BG Simplification    : 0.12
% 18.47/10.39  Subsumption          : 1.96
% 18.47/10.39  Abstraction          : 0.21
% 18.47/10.39  MUC search           : 0.00
% 18.47/10.39  Cooper               : 0.00
% 18.47/10.39  Total                : 9.64
% 18.47/10.39  Index Insertion      : 0.00
% 18.47/10.39  Index Deletion       : 0.00
% 18.47/10.39  Index Matching       : 0.00
% 18.47/10.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

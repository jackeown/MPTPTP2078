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
% DateTime   : Thu Dec  3 10:22:02 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 154 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 367 expanded)
%              Number of equality atoms :   24 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_pre_topc(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_53,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_50])).

tff(c_651,plain,(
    ! [B_75,A_76] :
      ( v2_tops_1(B_75,A_76)
      | ~ r1_tarski(B_75,k2_tops_1(A_76,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_653,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_651])).

tff(c_655,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6,c_653])).

tff(c_38,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_145,plain,(
    ! [A_53,B_54] :
      ( k2_pre_topc(A_53,B_54) = B_54
      | ~ v4_pre_topc(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_162,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_145])).

tff(c_173,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_162])).

tff(c_703,plain,(
    ! [B_79,A_80] :
      ( v3_tops_1(B_79,A_80)
      | ~ v2_tops_1(k2_pre_topc(A_80,B_79),A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_705,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_703])).

tff(c_707,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_655,c_705])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_707])).

tff(c_710,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_711,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_771,plain,(
    ! [B_94,A_95] :
      ( v2_tops_1(B_94,A_95)
      | ~ v3_tops_1(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_788,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_771])).

tff(c_799,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_711,c_788])).

tff(c_868,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(B_106,k2_tops_1(A_107,B_106))
      | ~ v2_tops_1(B_106,A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_882,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_868])).

tff(c_894,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_799,c_882])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_898,plain,
    ( k2_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_894,c_2])).

tff(c_904,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_710,c_898])).

tff(c_800,plain,(
    ! [A_96,B_97] :
      ( k2_pre_topc(A_96,B_97) = B_97
      | ~ v4_pre_topc(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_817,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_800])).

tff(c_828,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_817])).

tff(c_1836,plain,(
    ! [A_154,B_155] :
      ( k9_subset_1(u1_struct_0(A_154),k2_pre_topc(A_154,B_155),k2_pre_topc(A_154,k3_subset_1(u1_struct_0(A_154),B_155))) = k2_tops_1(A_154,B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1851,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_1836])).

tff(c_1855,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1851])).

tff(c_723,plain,(
    ! [A_88,C_89,B_90] :
      ( k9_subset_1(A_88,C_89,B_90) = k9_subset_1(A_88,B_90,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_732,plain,(
    ! [B_90] : k9_subset_1(u1_struct_0('#skF_1'),B_90,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_90) ),
    inference(resolution,[status(thm)],[c_40,c_723])).

tff(c_733,plain,(
    ! [B_91] : k9_subset_1(u1_struct_0('#skF_1'),B_91,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_91) ),
    inference(resolution,[status(thm)],[c_40,c_723])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_745,plain,(
    ! [B_91] :
      ( m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_91),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_12])).

tff(c_758,plain,(
    ! [B_92] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_92),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_745])).

tff(c_762,plain,(
    ! [B_90] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),B_90,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_758])).

tff(c_1695,plain,(
    ! [A_142,B_143,C_144] :
      ( r1_tarski(k3_subset_1(A_142,B_143),k3_subset_1(A_142,k9_subset_1(A_142,B_143,C_144)))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_142))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1718,plain,(
    ! [B_90] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k9_subset_1(u1_struct_0('#skF_1'),B_90,'#skF_2')))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_1695])).

tff(c_1784,plain,(
    ! [B_152] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k9_subset_1(u1_struct_0('#skF_1'),B_152,'#skF_2')))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1718])).

tff(c_14,plain,(
    ! [B_12,C_14,A_11] :
      ( r1_tarski(B_12,C_14)
      | ~ r1_tarski(k3_subset_1(A_11,C_14),k3_subset_1(A_11,B_12))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1787,plain,(
    ! [B_152] :
      ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),B_152,'#skF_2'),'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),B_152,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_1784,c_14])).

tff(c_1813,plain,(
    ! [B_153] :
      ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),B_153,'#skF_2'),'#skF_2')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_40,c_1787])).

tff(c_1830,plain,(
    ! [B_90] :
      ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_90),'#skF_2')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_1813])).

tff(c_1892,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1855,c_1830])).

tff(c_1926,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_904,c_1892])).

tff(c_1980,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1926])).

tff(c_1983,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1980])).

tff(c_1986,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_1983])).

tff(c_1990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:13:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.64  
% 3.79/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.64  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.79/1.64  
% 3.79/1.64  %Foreground sorts:
% 3.79/1.64  
% 3.79/1.64  
% 3.79/1.64  %Background operators:
% 3.79/1.64  
% 3.79/1.64  
% 3.79/1.64  %Foreground operators:
% 3.79/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.64  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.79/1.64  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.79/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.79/1.64  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.79/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/1.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.79/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.79/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.79/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/1.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.79/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.79/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.79/1.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.79/1.64  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.79/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/1.64  
% 3.79/1.66  tff(f_126, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 3.79/1.66  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.79/1.66  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.79/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.79/1.66  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.79/1.66  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.79/1.66  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 3.79/1.66  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 3.79/1.66  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 3.79/1.66  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.79/1.66  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.79/1.66  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 3.79/1.66  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.79/1.66  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.79/1.66  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.79/1.66  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.79/1.66  tff(c_20, plain, (![A_19, B_20]: (m1_subset_1(k2_pre_topc(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.79/1.66  tff(c_44, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.79/1.66  tff(c_53, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 3.79/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.66  tff(c_50, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.79/1.66  tff(c_54, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_53, c_50])).
% 3.79/1.66  tff(c_651, plain, (![B_75, A_76]: (v2_tops_1(B_75, A_76) | ~r1_tarski(B_75, k2_tops_1(A_76, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.79/1.66  tff(c_653, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_54, c_651])).
% 3.79/1.66  tff(c_655, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_6, c_653])).
% 3.79/1.66  tff(c_38, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.79/1.66  tff(c_145, plain, (![A_53, B_54]: (k2_pre_topc(A_53, B_54)=B_54 | ~v4_pre_topc(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.79/1.66  tff(c_162, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_145])).
% 3.79/1.66  tff(c_173, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_162])).
% 3.79/1.66  tff(c_703, plain, (![B_79, A_80]: (v3_tops_1(B_79, A_80) | ~v2_tops_1(k2_pre_topc(A_80, B_79), A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.79/1.66  tff(c_705, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_173, c_703])).
% 3.79/1.66  tff(c_707, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_655, c_705])).
% 3.79/1.66  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_707])).
% 3.79/1.66  tff(c_710, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 3.79/1.66  tff(c_711, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 3.79/1.66  tff(c_771, plain, (![B_94, A_95]: (v2_tops_1(B_94, A_95) | ~v3_tops_1(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.79/1.66  tff(c_788, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_771])).
% 3.79/1.66  tff(c_799, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_711, c_788])).
% 3.79/1.66  tff(c_868, plain, (![B_106, A_107]: (r1_tarski(B_106, k2_tops_1(A_107, B_106)) | ~v2_tops_1(B_106, A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.79/1.66  tff(c_882, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_868])).
% 3.79/1.66  tff(c_894, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_799, c_882])).
% 3.79/1.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.66  tff(c_898, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_894, c_2])).
% 3.79/1.66  tff(c_904, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_710, c_898])).
% 3.79/1.66  tff(c_800, plain, (![A_96, B_97]: (k2_pre_topc(A_96, B_97)=B_97 | ~v4_pre_topc(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.79/1.66  tff(c_817, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_800])).
% 3.79/1.66  tff(c_828, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_817])).
% 3.79/1.66  tff(c_1836, plain, (![A_154, B_155]: (k9_subset_1(u1_struct_0(A_154), k2_pre_topc(A_154, B_155), k2_pre_topc(A_154, k3_subset_1(u1_struct_0(A_154), B_155)))=k2_tops_1(A_154, B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.79/1.66  tff(c_1851, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_828, c_1836])).
% 3.79/1.66  tff(c_1855, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1851])).
% 3.79/1.66  tff(c_723, plain, (![A_88, C_89, B_90]: (k9_subset_1(A_88, C_89, B_90)=k9_subset_1(A_88, B_90, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.79/1.66  tff(c_732, plain, (![B_90]: (k9_subset_1(u1_struct_0('#skF_1'), B_90, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_90))), inference(resolution, [status(thm)], [c_40, c_723])).
% 3.79/1.66  tff(c_733, plain, (![B_91]: (k9_subset_1(u1_struct_0('#skF_1'), B_91, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_91))), inference(resolution, [status(thm)], [c_40, c_723])).
% 3.79/1.66  tff(c_12, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.66  tff(c_745, plain, (![B_91]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_91), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_733, c_12])).
% 3.79/1.66  tff(c_758, plain, (![B_92]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_92), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_745])).
% 3.79/1.66  tff(c_762, plain, (![B_90]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), B_90, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_732, c_758])).
% 3.79/1.66  tff(c_1695, plain, (![A_142, B_143, C_144]: (r1_tarski(k3_subset_1(A_142, B_143), k3_subset_1(A_142, k9_subset_1(A_142, B_143, C_144))) | ~m1_subset_1(C_144, k1_zfmisc_1(A_142)) | ~m1_subset_1(B_143, k1_zfmisc_1(A_142)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.79/1.66  tff(c_1718, plain, (![B_90]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k9_subset_1(u1_struct_0('#skF_1'), B_90, '#skF_2'))) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_732, c_1695])).
% 3.79/1.66  tff(c_1784, plain, (![B_152]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k9_subset_1(u1_struct_0('#skF_1'), B_152, '#skF_2'))) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1718])).
% 3.79/1.66  tff(c_14, plain, (![B_12, C_14, A_11]: (r1_tarski(B_12, C_14) | ~r1_tarski(k3_subset_1(A_11, C_14), k3_subset_1(A_11, B_12)) | ~m1_subset_1(C_14, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.79/1.66  tff(c_1787, plain, (![B_152]: (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), B_152, '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), B_152, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_1784, c_14])).
% 3.79/1.66  tff(c_1813, plain, (![B_153]: (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), B_153, '#skF_2'), '#skF_2') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_762, c_40, c_1787])).
% 3.79/1.66  tff(c_1830, plain, (![B_90]: (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_90), '#skF_2') | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_732, c_1813])).
% 3.79/1.66  tff(c_1892, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1855, c_1830])).
% 3.79/1.66  tff(c_1926, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_904, c_1892])).
% 3.79/1.66  tff(c_1980, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1926])).
% 3.79/1.66  tff(c_1983, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1980])).
% 3.79/1.66  tff(c_1986, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_1983])).
% 3.79/1.66  tff(c_1990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1986])).
% 3.79/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.66  
% 3.79/1.66  Inference rules
% 3.79/1.66  ----------------------
% 3.79/1.66  #Ref     : 0
% 3.79/1.66  #Sup     : 440
% 3.79/1.66  #Fact    : 0
% 3.79/1.66  #Define  : 0
% 3.79/1.66  #Split   : 2
% 3.79/1.66  #Chain   : 0
% 3.79/1.66  #Close   : 0
% 3.79/1.66  
% 3.79/1.66  Ordering : KBO
% 3.79/1.66  
% 3.79/1.66  Simplification rules
% 3.79/1.66  ----------------------
% 3.79/1.66  #Subsume      : 24
% 3.79/1.66  #Demod        : 245
% 3.79/1.66  #Tautology    : 146
% 3.79/1.66  #SimpNegUnit  : 5
% 3.79/1.66  #BackRed      : 0
% 3.79/1.66  
% 3.79/1.66  #Partial instantiations: 0
% 3.79/1.66  #Strategies tried      : 1
% 3.79/1.66  
% 3.79/1.66  Timing (in seconds)
% 3.79/1.66  ----------------------
% 3.79/1.66  Preprocessing        : 0.32
% 3.79/1.66  Parsing              : 0.18
% 3.79/1.66  CNF conversion       : 0.02
% 3.79/1.66  Main loop            : 0.57
% 3.79/1.66  Inferencing          : 0.19
% 3.79/1.66  Reduction            : 0.23
% 3.79/1.66  Demodulation         : 0.18
% 3.79/1.66  BG Simplification    : 0.03
% 3.79/1.66  Subsumption          : 0.08
% 3.79/1.66  Abstraction          : 0.04
% 3.79/1.66  MUC search           : 0.00
% 3.79/1.66  Cooper               : 0.00
% 3.79/1.66  Total                : 0.93
% 3.79/1.66  Index Insertion      : 0.00
% 3.79/1.66  Index Deletion       : 0.00
% 3.79/1.66  Index Matching       : 0.00
% 3.79/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------

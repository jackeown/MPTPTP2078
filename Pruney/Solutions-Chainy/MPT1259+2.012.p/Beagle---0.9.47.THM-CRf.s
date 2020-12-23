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
% DateTime   : Thu Dec  3 10:21:00 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 222 expanded)
%              Number of leaves         :   29 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 530 expanded)
%              Number of equality atoms :   40 ( 134 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k2_tops_1(A,B)) = k2_tops_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l79_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_28,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_41,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_82,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = k3_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_100,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_97])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k2_tops_1(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_410,plain,(
    ! [A_67,B_68] :
      ( k2_pre_topc(A_67,k2_tops_1(A_67,B_68)) = k2_tops_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_416,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_410])).

tff(c_421,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_416])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k2_pre_topc(A_12,B_13),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_603,plain,(
    ! [A_75,B_76] :
      ( k1_tops_1(A_75,k2_tops_1(A_75,k2_tops_1(A_75,B_76))) = k1_xboole_0
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_840,plain,(
    ! [A_85,B_86] :
      ( k1_tops_1(A_85,k2_tops_1(A_85,k2_tops_1(A_85,k2_pre_topc(A_85,B_86)))) = k1_xboole_0
      | ~ v2_pre_topc(A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_18,c_603])).

tff(c_852,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))) = k1_xboole_0
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_840])).

tff(c_856,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))) = k1_xboole_0
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_852])).

tff(c_1081,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_856])).

tff(c_1084,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1081])).

tff(c_1088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1084])).

tff(c_1090,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_24,plain,(
    ! [A_19,B_21] :
      ( k2_pre_topc(A_19,k2_tops_1(A_19,B_21)) = k2_tops_1(A_19,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1094,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1090,c_24])).

tff(c_1102,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1094])).

tff(c_609,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_603])).

tff(c_614,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_609])).

tff(c_694,plain,(
    ! [A_79,B_80] :
      ( k7_subset_1(u1_struct_0(A_79),k2_pre_topc(A_79,B_80),k1_tops_1(A_79,B_80)) = k2_tops_1(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_703,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_694])).

tff(c_710,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_703])).

tff(c_1351,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_710])).

tff(c_1352,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1351])).

tff(c_1355,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1352])).

tff(c_1359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1090,c_1355])).

tff(c_1360,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1351])).

tff(c_335,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k2_tops_1(A_61,B_62),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( k7_subset_1(A_9,B_10,C_11) = k4_xboole_0(B_10,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1574,plain,(
    ! [A_102,B_103,C_104] :
      ( k7_subset_1(u1_struct_0(A_102),k2_tops_1(A_102,B_103),C_104) = k4_xboole_0(k2_tops_1(A_102,B_103),C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_335,c_16])).

tff(c_1578,plain,(
    ! [C_104] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_104) = k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_104)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1090,c_1574])).

tff(c_1590,plain,(
    ! [C_104] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_104) = k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1578])).

tff(c_2465,plain,(
    k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_1590])).

tff(c_2471,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2465])).

tff(c_2473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.79  
% 4.08/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.79  %$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.08/1.79  
% 4.08/1.79  %Foreground sorts:
% 4.08/1.79  
% 4.08/1.79  
% 4.08/1.79  %Background operators:
% 4.08/1.79  
% 4.08/1.79  
% 4.08/1.79  %Foreground operators:
% 4.08/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.08/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.08/1.79  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.08/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.08/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.08/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.08/1.79  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.08/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.79  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.08/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.08/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.08/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.08/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.08/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.08/1.79  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.08/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.08/1.79  
% 4.30/1.81  tff(f_92, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k2_tops_1(A, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tops_1)).
% 4.30/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.30/1.81  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.30/1.81  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.30/1.81  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.30/1.81  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.30/1.81  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k2_tops_1(A, B)) = k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l79_tops_1)).
% 4.30/1.81  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.30/1.81  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l80_tops_1)).
% 4.30/1.81  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.30/1.81  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.30/1.81  tff(c_28, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.81  tff(c_37, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.30/1.81  tff(c_41, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_37])).
% 4.30/1.81  tff(c_42, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.30/1.81  tff(c_46, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_42])).
% 4.30/1.81  tff(c_82, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.30/1.81  tff(c_97, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_46, c_82])).
% 4.30/1.81  tff(c_100, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_41, c_97])).
% 4.30/1.81  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.81  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.81  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(k2_tops_1(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.30/1.81  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.81  tff(c_410, plain, (![A_67, B_68]: (k2_pre_topc(A_67, k2_tops_1(A_67, B_68))=k2_tops_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.30/1.81  tff(c_416, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_410])).
% 4.30/1.81  tff(c_421, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_416])).
% 4.30/1.81  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(k2_pre_topc(A_12, B_13), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.30/1.81  tff(c_603, plain, (![A_75, B_76]: (k1_tops_1(A_75, k2_tops_1(A_75, k2_tops_1(A_75, B_76)))=k1_xboole_0 | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.30/1.81  tff(c_840, plain, (![A_85, B_86]: (k1_tops_1(A_85, k2_tops_1(A_85, k2_tops_1(A_85, k2_pre_topc(A_85, B_86))))=k1_xboole_0 | ~v2_pre_topc(A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_18, c_603])).
% 4.30/1.81  tff(c_852, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))=k1_xboole_0 | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_421, c_840])).
% 4.30/1.81  tff(c_856, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))=k1_xboole_0 | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_852])).
% 4.30/1.81  tff(c_1081, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_856])).
% 4.30/1.81  tff(c_1084, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1081])).
% 4.30/1.81  tff(c_1088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1084])).
% 4.30/1.81  tff(c_1090, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_856])).
% 4.30/1.81  tff(c_24, plain, (![A_19, B_21]: (k2_pre_topc(A_19, k2_tops_1(A_19, B_21))=k2_tops_1(A_19, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.30/1.81  tff(c_1094, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1090, c_24])).
% 4.30/1.81  tff(c_1102, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1094])).
% 4.30/1.81  tff(c_609, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_603])).
% 4.30/1.81  tff(c_614, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_609])).
% 4.30/1.81  tff(c_694, plain, (![A_79, B_80]: (k7_subset_1(u1_struct_0(A_79), k2_pre_topc(A_79, B_80), k1_tops_1(A_79, B_80))=k2_tops_1(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.30/1.81  tff(c_703, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_614, c_694])).
% 4.30/1.81  tff(c_710, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_703])).
% 4.30/1.81  tff(c_1351, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_710])).
% 4.30/1.81  tff(c_1352, plain, (~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1351])).
% 4.30/1.81  tff(c_1355, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1352])).
% 4.30/1.81  tff(c_1359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1090, c_1355])).
% 4.30/1.81  tff(c_1360, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_1351])).
% 4.30/1.81  tff(c_335, plain, (![A_61, B_62]: (m1_subset_1(k2_tops_1(A_61, B_62), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.30/1.81  tff(c_16, plain, (![A_9, B_10, C_11]: (k7_subset_1(A_9, B_10, C_11)=k4_xboole_0(B_10, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.30/1.81  tff(c_1574, plain, (![A_102, B_103, C_104]: (k7_subset_1(u1_struct_0(A_102), k2_tops_1(A_102, B_103), C_104)=k4_xboole_0(k2_tops_1(A_102, B_103), C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_335, c_16])).
% 4.30/1.81  tff(c_1578, plain, (![C_104]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_104)=k4_xboole_0(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_104) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1090, c_1574])).
% 4.30/1.81  tff(c_1590, plain, (![C_104]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_104)=k4_xboole_0(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_104))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1578])).
% 4.30/1.81  tff(c_2465, plain, (k4_xboole_0(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1360, c_1590])).
% 4.30/1.81  tff(c_2471, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2465])).
% 4.30/1.81  tff(c_2473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2471])).
% 4.30/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.81  
% 4.30/1.81  Inference rules
% 4.30/1.81  ----------------------
% 4.30/1.81  #Ref     : 0
% 4.30/1.81  #Sup     : 615
% 4.30/1.81  #Fact    : 0
% 4.30/1.81  #Define  : 0
% 4.30/1.81  #Split   : 5
% 4.30/1.81  #Chain   : 0
% 4.30/1.81  #Close   : 0
% 4.30/1.81  
% 4.30/1.81  Ordering : KBO
% 4.30/1.81  
% 4.30/1.81  Simplification rules
% 4.30/1.81  ----------------------
% 4.30/1.81  #Subsume      : 78
% 4.30/1.81  #Demod        : 648
% 4.30/1.81  #Tautology    : 312
% 4.30/1.81  #SimpNegUnit  : 4
% 4.30/1.81  #BackRed      : 0
% 4.30/1.81  
% 4.30/1.81  #Partial instantiations: 0
% 4.30/1.81  #Strategies tried      : 1
% 4.30/1.81  
% 4.30/1.81  Timing (in seconds)
% 4.30/1.81  ----------------------
% 4.30/1.81  Preprocessing        : 0.31
% 4.30/1.81  Parsing              : 0.16
% 4.30/1.81  CNF conversion       : 0.02
% 4.30/1.81  Main loop            : 0.70
% 4.30/1.81  Inferencing          : 0.23
% 4.30/1.81  Reduction            : 0.26
% 4.30/1.81  Demodulation         : 0.20
% 4.30/1.81  BG Simplification    : 0.03
% 4.30/1.81  Subsumption          : 0.13
% 4.30/1.81  Abstraction          : 0.04
% 4.30/1.81  MUC search           : 0.00
% 4.30/1.81  Cooper               : 0.00
% 4.30/1.81  Total                : 1.05
% 4.30/1.81  Index Insertion      : 0.00
% 4.30/1.81  Index Deletion       : 0.00
% 4.30/1.81  Index Matching       : 0.00
% 4.30/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------

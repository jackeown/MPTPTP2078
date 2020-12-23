%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:07 EST 2020

% Result     : Theorem 8.67s
% Output     : CNFRefutation 8.67s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 178 expanded)
%              Number of leaves         :   34 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  153 ( 378 expanded)
%              Number of equality atoms :   48 (  96 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_114,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_280,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_774,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_777,plain,(
    ! [C_81] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_81) = k4_xboole_0('#skF_2',C_81) ),
    inference(resolution,[status(thm)],[c_38,c_774])).

tff(c_1516,plain,(
    ! [A_108,B_109] :
      ( k7_subset_1(u1_struct_0(A_108),B_109,k2_tops_1(A_108,B_109)) = k1_tops_1(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1520,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1516])).

tff(c_1524,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_777,c_1520])).

tff(c_22,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1606,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1524,c_22])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1142,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k1_tops_1(A_94,B_95),B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1144,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1142])).

tff(c_1147,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1144])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1156,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1147,c_4])).

tff(c_1201,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1156])).

tff(c_1205,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1201])).

tff(c_3338,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_1205])).

tff(c_1214,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k2_pre_topc(A_96,B_97),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] :
      ( k7_subset_1(A_17,B_18,C_19) = k4_xboole_0(B_18,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_15371,plain,(
    ! [A_265,B_266,C_267] :
      ( k7_subset_1(u1_struct_0(A_265),k2_pre_topc(A_265,B_266),C_267) = k4_xboole_0(k2_pre_topc(A_265,B_266),C_267)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(resolution,[status(thm)],[c_1214,c_24])).

tff(c_15375,plain,(
    ! [C_267] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_267) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_267)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_15371])).

tff(c_15831,plain,(
    ! [C_271] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_271) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_15375])).

tff(c_15841,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15831,c_114])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_115])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_394,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k4_xboole_0(A_65,B_66),C_67) = k4_xboole_0(A_65,k2_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6030,plain,(
    ! [A_186,B_187,C_188] : k4_xboole_0(k4_xboole_0(A_186,B_187),k4_xboole_0(A_186,k2_xboole_0(B_187,C_188))) = k3_xboole_0(k4_xboole_0(A_186,B_187),C_188) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_22])).

tff(c_6283,plain,(
    ! [A_186,B_4] : k4_xboole_0(k4_xboole_0(A_186,B_4),k4_xboole_0(A_186,B_4)) = k3_xboole_0(k4_xboole_0(A_186,B_4),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_6030])).

tff(c_6349,plain,(
    ! [B_4,A_186] : k3_xboole_0(B_4,k4_xboole_0(A_186,B_4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_2,c_6283])).

tff(c_15897,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15841,c_6349])).

tff(c_15967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3338,c_15897])).

tff(c_15968,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1156])).

tff(c_16116,plain,(
    ! [A_278,B_279] :
      ( v3_pre_topc(k1_tops_1(A_278,B_279),A_278)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16120,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_16116])).

tff(c_16124,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_15968,c_16120])).

tff(c_16126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_16124])).

tff(c_16127,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_16571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_16127])).

tff(c_16572,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_16750,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16572,c_44])).

tff(c_17707,plain,(
    ! [A_344,B_345] :
      ( r1_tarski(k1_tops_1(A_344,B_345),B_345)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17709,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_17707])).

tff(c_17712,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_17709])).

tff(c_17721,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_17712,c_4])).

tff(c_18217,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17721])).

tff(c_18996,plain,(
    ! [B_376,A_377,C_378] :
      ( r1_tarski(B_376,k1_tops_1(A_377,C_378))
      | ~ r1_tarski(B_376,C_378)
      | ~ v3_pre_topc(B_376,A_377)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_19000,plain,(
    ! [B_376] :
      ( r1_tarski(B_376,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_376,'#skF_2')
      | ~ v3_pre_topc(B_376,'#skF_1')
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_18996])).

tff(c_19104,plain,(
    ! [B_381] :
      ( r1_tarski(B_381,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_381,'#skF_2')
      | ~ v3_pre_topc(B_381,'#skF_1')
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_19000])).

tff(c_19111,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_19104])).

tff(c_19117,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16572,c_8,c_19111])).

tff(c_19119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18217,c_19117])).

tff(c_19120,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17721])).

tff(c_19722,plain,(
    ! [A_398,B_399] :
      ( k7_subset_1(u1_struct_0(A_398),k2_pre_topc(A_398,B_399),k1_tops_1(A_398,B_399)) = k2_tops_1(A_398,B_399)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ l1_pre_topc(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_19731,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19120,c_19722])).

tff(c_19735,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_19731])).

tff(c_19737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16750,c_19735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.30  % Computer   : n005.cluster.edu
% 0.12/0.30  % Model      : x86_64 x86_64
% 0.12/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.30  % Memory     : 8042.1875MB
% 0.12/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.30  % CPULimit   : 60
% 0.12/0.30  % DateTime   : Tue Dec  1 15:09:17 EST 2020
% 0.12/0.30  % CPUTime    : 
% 0.12/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.67/3.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/3.23  
% 8.67/3.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/3.23  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.67/3.23  
% 8.67/3.23  %Foreground sorts:
% 8.67/3.23  
% 8.67/3.23  
% 8.67/3.23  %Background operators:
% 8.67/3.23  
% 8.67/3.23  
% 8.67/3.23  %Foreground operators:
% 8.67/3.23  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.67/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.67/3.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.67/3.23  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.67/3.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.67/3.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.67/3.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.67/3.23  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.67/3.23  tff('#skF_2', type, '#skF_2': $i).
% 8.67/3.23  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.67/3.23  tff('#skF_1', type, '#skF_1': $i).
% 8.67/3.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.67/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.67/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.67/3.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.67/3.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.67/3.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.67/3.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.67/3.23  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.67/3.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.67/3.23  
% 8.67/3.25  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 8.67/3.25  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.67/3.25  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 8.67/3.25  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.67/3.25  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.67/3.25  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 8.67/3.25  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.67/3.25  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.67/3.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.67/3.25  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.67/3.25  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.67/3.25  tff(f_67, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 8.67/3.25  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 8.67/3.25  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 8.67/3.25  tff(c_50, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.67/3.25  tff(c_114, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 8.67/3.25  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.67/3.25  tff(c_280, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 8.67/3.25  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.67/3.25  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.67/3.25  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.67/3.25  tff(c_774, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.67/3.25  tff(c_777, plain, (![C_81]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_81)=k4_xboole_0('#skF_2', C_81))), inference(resolution, [status(thm)], [c_38, c_774])).
% 8.67/3.25  tff(c_1516, plain, (![A_108, B_109]: (k7_subset_1(u1_struct_0(A_108), B_109, k2_tops_1(A_108, B_109))=k1_tops_1(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.67/3.25  tff(c_1520, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1516])).
% 8.67/3.25  tff(c_1524, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_777, c_1520])).
% 8.67/3.25  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.67/3.25  tff(c_1606, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1524, c_22])).
% 8.67/3.25  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.67/3.25  tff(c_1142, plain, (![A_94, B_95]: (r1_tarski(k1_tops_1(A_94, B_95), B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.67/3.25  tff(c_1144, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1142])).
% 8.67/3.25  tff(c_1147, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1144])).
% 8.67/3.25  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.67/3.25  tff(c_1156, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1147, c_4])).
% 8.67/3.25  tff(c_1201, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1156])).
% 8.67/3.25  tff(c_1205, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1201])).
% 8.67/3.25  tff(c_3338, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_1205])).
% 8.67/3.25  tff(c_1214, plain, (![A_96, B_97]: (m1_subset_1(k2_pre_topc(A_96, B_97), k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.67/3.25  tff(c_24, plain, (![A_17, B_18, C_19]: (k7_subset_1(A_17, B_18, C_19)=k4_xboole_0(B_18, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.67/3.25  tff(c_15371, plain, (![A_265, B_266, C_267]: (k7_subset_1(u1_struct_0(A_265), k2_pre_topc(A_265, B_266), C_267)=k4_xboole_0(k2_pre_topc(A_265, B_266), C_267) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(resolution, [status(thm)], [c_1214, c_24])).
% 8.67/3.25  tff(c_15375, plain, (![C_267]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_267)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_267) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_15371])).
% 8.67/3.25  tff(c_15831, plain, (![C_271]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_271)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_271))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_15375])).
% 8.67/3.25  tff(c_15841, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15831, c_114])).
% 8.67/3.25  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.67/3.25  tff(c_115, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.67/3.25  tff(c_123, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_115])).
% 8.67/3.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.67/3.25  tff(c_96, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.67/3.25  tff(c_104, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_96])).
% 8.67/3.25  tff(c_394, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k4_xboole_0(A_65, B_66), C_67)=k4_xboole_0(A_65, k2_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.67/3.25  tff(c_6030, plain, (![A_186, B_187, C_188]: (k4_xboole_0(k4_xboole_0(A_186, B_187), k4_xboole_0(A_186, k2_xboole_0(B_187, C_188)))=k3_xboole_0(k4_xboole_0(A_186, B_187), C_188))), inference(superposition, [status(thm), theory('equality')], [c_394, c_22])).
% 8.67/3.25  tff(c_6283, plain, (![A_186, B_4]: (k4_xboole_0(k4_xboole_0(A_186, B_4), k4_xboole_0(A_186, B_4))=k3_xboole_0(k4_xboole_0(A_186, B_4), B_4))), inference(superposition, [status(thm), theory('equality')], [c_104, c_6030])).
% 8.67/3.25  tff(c_6349, plain, (![B_4, A_186]: (k3_xboole_0(B_4, k4_xboole_0(A_186, B_4))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_123, c_2, c_6283])).
% 8.67/3.25  tff(c_15897, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15841, c_6349])).
% 8.67/3.25  tff(c_15967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3338, c_15897])).
% 8.67/3.25  tff(c_15968, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_1156])).
% 8.67/3.25  tff(c_16116, plain, (![A_278, B_279]: (v3_pre_topc(k1_tops_1(A_278, B_279), A_278) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.67/3.25  tff(c_16120, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_16116])).
% 8.67/3.25  tff(c_16124, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_15968, c_16120])).
% 8.67/3.25  tff(c_16126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_16124])).
% 8.67/3.25  tff(c_16127, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 8.67/3.25  tff(c_16571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_16127])).
% 8.67/3.25  tff(c_16572, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 8.67/3.25  tff(c_16750, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16572, c_44])).
% 8.67/3.25  tff(c_17707, plain, (![A_344, B_345]: (r1_tarski(k1_tops_1(A_344, B_345), B_345) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.67/3.25  tff(c_17709, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_17707])).
% 8.67/3.25  tff(c_17712, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_17709])).
% 8.67/3.25  tff(c_17721, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_17712, c_4])).
% 8.67/3.25  tff(c_18217, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_17721])).
% 8.67/3.25  tff(c_18996, plain, (![B_376, A_377, C_378]: (r1_tarski(B_376, k1_tops_1(A_377, C_378)) | ~r1_tarski(B_376, C_378) | ~v3_pre_topc(B_376, A_377) | ~m1_subset_1(C_378, k1_zfmisc_1(u1_struct_0(A_377))) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_377))) | ~l1_pre_topc(A_377))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.67/3.25  tff(c_19000, plain, (![B_376]: (r1_tarski(B_376, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_376, '#skF_2') | ~v3_pre_topc(B_376, '#skF_1') | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_18996])).
% 8.67/3.25  tff(c_19104, plain, (![B_381]: (r1_tarski(B_381, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_381, '#skF_2') | ~v3_pre_topc(B_381, '#skF_1') | ~m1_subset_1(B_381, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_19000])).
% 8.67/3.25  tff(c_19111, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_19104])).
% 8.67/3.25  tff(c_19117, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16572, c_8, c_19111])).
% 8.67/3.25  tff(c_19119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18217, c_19117])).
% 8.67/3.25  tff(c_19120, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_17721])).
% 8.67/3.25  tff(c_19722, plain, (![A_398, B_399]: (k7_subset_1(u1_struct_0(A_398), k2_pre_topc(A_398, B_399), k1_tops_1(A_398, B_399))=k2_tops_1(A_398, B_399) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_398))) | ~l1_pre_topc(A_398))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.67/3.25  tff(c_19731, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_19120, c_19722])).
% 8.67/3.25  tff(c_19735, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_19731])).
% 8.67/3.25  tff(c_19737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16750, c_19735])).
% 8.67/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/3.25  
% 8.67/3.25  Inference rules
% 8.67/3.25  ----------------------
% 8.67/3.25  #Ref     : 1
% 8.67/3.25  #Sup     : 4953
% 8.67/3.25  #Fact    : 0
% 8.67/3.25  #Define  : 0
% 8.67/3.25  #Split   : 10
% 8.67/3.25  #Chain   : 0
% 8.67/3.25  #Close   : 0
% 8.67/3.25  
% 8.67/3.25  Ordering : KBO
% 8.67/3.25  
% 8.67/3.25  Simplification rules
% 8.67/3.25  ----------------------
% 8.67/3.25  #Subsume      : 584
% 8.67/3.25  #Demod        : 4274
% 8.67/3.25  #Tautology    : 3072
% 8.67/3.25  #SimpNegUnit  : 62
% 8.67/3.25  #BackRed      : 13
% 8.67/3.25  
% 8.67/3.25  #Partial instantiations: 0
% 8.67/3.25  #Strategies tried      : 1
% 8.67/3.25  
% 8.67/3.25  Timing (in seconds)
% 8.67/3.25  ----------------------
% 8.67/3.25  Preprocessing        : 0.35
% 8.67/3.25  Parsing              : 0.19
% 8.67/3.25  CNF conversion       : 0.02
% 8.67/3.25  Main loop            : 2.07
% 8.67/3.25  Inferencing          : 0.49
% 8.67/3.25  Reduction            : 1.08
% 8.67/3.25  Demodulation         : 0.92
% 8.67/3.25  BG Simplification    : 0.06
% 8.67/3.25  Subsumption          : 0.33
% 8.67/3.25  Abstraction          : 0.10
% 8.67/3.25  MUC search           : 0.00
% 8.67/3.25  Cooper               : 0.00
% 8.67/3.25  Total                : 2.46
% 8.67/3.25  Index Insertion      : 0.00
% 8.67/3.25  Index Deletion       : 0.00
% 8.67/3.25  Index Matching       : 0.00
% 8.67/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

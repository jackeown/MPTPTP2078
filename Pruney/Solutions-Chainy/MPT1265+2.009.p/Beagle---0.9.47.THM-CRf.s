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
% DateTime   : Thu Dec  3 10:21:42 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 354 expanded)
%              Number of leaves         :   34 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  153 ( 861 expanded)
%              Number of equality atoms :   36 ( 153 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & v1_tops_1(C,A)
                    & v3_pre_topc(C,A) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( v3_pre_topc(C,A)
                 => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_22,c_58])).

tff(c_67,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_69,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_40])).

tff(c_120,plain,(
    ! [A_52,B_53,C_54] :
      ( k9_subset_1(A_52,B_53,C_54) = k3_xboole_0(B_53,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_130,plain,(
    ! [B_53] : k9_subset_1(k2_struct_0('#skF_1'),B_53,'#skF_2') = k3_xboole_0(B_53,'#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_120])).

tff(c_223,plain,(
    ! [A_73,C_74,B_75] :
      ( k9_subset_1(A_73,C_74,B_75) = k9_subset_1(A_73,B_75,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_227,plain,(
    ! [B_75] : k9_subset_1(k2_struct_0('#skF_1'),B_75,'#skF_2') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_2',B_75) ),
    inference(resolution,[status(thm)],[c_69,c_223])).

tff(c_274,plain,(
    ! [B_78] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_2',B_78) = k3_xboole_0(B_78,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_227])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_38])).

tff(c_131,plain,(
    ! [B_53] : k9_subset_1(k2_struct_0('#skF_1'),B_53,'#skF_3') = k3_xboole_0(B_53,'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_285,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_131])).

tff(c_30,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_83,plain,(
    ~ v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_30])).

tff(c_158,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_83])).

tff(c_309,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_158])).

tff(c_36,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_393,plain,(
    ! [A_81,B_82] :
      ( k2_pre_topc(A_81,B_82) = k2_struct_0(A_81)
      | ~ v1_tops_1(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_400,plain,(
    ! [B_82] :
      ( k2_pre_topc('#skF_1',B_82) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_82,'#skF_1')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_393])).

tff(c_625,plain,(
    ! [B_100] :
      ( k2_pre_topc('#skF_1',B_100) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_100,'#skF_1')
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_400])).

tff(c_635,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_625])).

tff(c_646,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_635])).

tff(c_229,plain,(
    ! [B_75] : k9_subset_1(k2_struct_0('#skF_1'),B_75,'#skF_3') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_75) ),
    inference(resolution,[status(thm)],[c_68,c_223])).

tff(c_236,plain,(
    ! [B_75] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_75) = k3_xboole_0(B_75,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_229])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_558,plain,(
    ! [A_95,C_96,B_97] :
      ( k2_pre_topc(A_95,k9_subset_1(u1_struct_0(A_95),C_96,B_97)) = k2_pre_topc(A_95,C_96)
      | ~ v3_pre_topc(C_96,A_95)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v1_tops_1(B_97,A_95)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_563,plain,(
    ! [C_96,B_97] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),C_96,B_97)) = k2_pre_topc('#skF_1',C_96)
      | ~ v3_pre_topc(C_96,'#skF_1')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_97,'#skF_1')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_558])).

tff(c_832,plain,(
    ! [C_110,B_111] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),C_110,B_111)) = k2_pre_topc('#skF_1',C_110)
      | ~ v3_pre_topc(C_110,'#skF_1')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_111,'#skF_1')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_67,c_67,c_563])).

tff(c_839,plain,(
    ! [B_111] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_111)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_111,'#skF_1')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_68,c_832])).

tff(c_992,plain,(
    ! [B_121] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_121,'#skF_3')) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_121,'#skF_1')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_646,c_236,c_839])).

tff(c_999,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_992])).

tff(c_1010,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_285,c_999])).

tff(c_8,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_85,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_45,c_85])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_322,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_2])).

tff(c_99,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_69,c_85])).

tff(c_103,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_142,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_57,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_99,c_103])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_754,plain,(
    ! [A_108,A_109] :
      ( r1_tarski(A_108,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_108,A_109)
      | ~ r1_tarski(A_109,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_770,plain,
    ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_322,c_754])).

tff(c_804,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_770])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_443,plain,(
    ! [B_83,A_84] :
      ( v1_tops_1(B_83,A_84)
      | k2_pre_topc(A_84,B_83) != k2_struct_0(A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1361,plain,(
    ! [A_130,A_131] :
      ( v1_tops_1(A_130,A_131)
      | k2_pre_topc(A_131,A_130) != k2_struct_0(A_131)
      | ~ l1_pre_topc(A_131)
      | ~ r1_tarski(A_130,u1_struct_0(A_131)) ) ),
    inference(resolution,[status(thm)],[c_18,c_443])).

tff(c_1376,plain,(
    ! [A_130] :
      ( v1_tops_1(A_130,'#skF_1')
      | k2_pre_topc('#skF_1',A_130) != k2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_130,k2_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_1361])).

tff(c_1406,plain,(
    ! [A_132] :
      ( v1_tops_1(A_132,'#skF_1')
      | k2_pre_topc('#skF_1',A_132) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_132,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1376])).

tff(c_1424,plain,
    ( v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_804,c_1406])).

tff(c_1475,plain,(
    v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_1424])).

tff(c_1477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_1475])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.57  
% 3.36/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.57  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.36/1.57  
% 3.36/1.57  %Foreground sorts:
% 3.36/1.57  
% 3.36/1.57  
% 3.36/1.57  %Background operators:
% 3.36/1.57  
% 3.36/1.57  
% 3.36/1.57  %Foreground operators:
% 3.36/1.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.36/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.36/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.57  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.36/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.36/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.36/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.57  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.36/1.57  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.36/1.57  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.36/1.57  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.36/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.36/1.57  
% 3.36/1.59  tff(f_103, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_tops_1)).
% 3.36/1.59  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.36/1.59  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.36/1.59  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.36/1.59  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.36/1.59  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.36/1.59  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 3.36/1.59  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.36/1.59  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.36/1.59  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.36/1.59  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.36/1.59  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.36/1.59  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.59  tff(c_22, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.36/1.59  tff(c_58, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.36/1.59  tff(c_63, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_22, c_58])).
% 3.36/1.59  tff(c_67, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_63])).
% 3.36/1.59  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.59  tff(c_69, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_40])).
% 3.36/1.59  tff(c_120, plain, (![A_52, B_53, C_54]: (k9_subset_1(A_52, B_53, C_54)=k3_xboole_0(B_53, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.59  tff(c_130, plain, (![B_53]: (k9_subset_1(k2_struct_0('#skF_1'), B_53, '#skF_2')=k3_xboole_0(B_53, '#skF_2'))), inference(resolution, [status(thm)], [c_69, c_120])).
% 3.36/1.59  tff(c_223, plain, (![A_73, C_74, B_75]: (k9_subset_1(A_73, C_74, B_75)=k9_subset_1(A_73, B_75, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.59  tff(c_227, plain, (![B_75]: (k9_subset_1(k2_struct_0('#skF_1'), B_75, '#skF_2')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', B_75))), inference(resolution, [status(thm)], [c_69, c_223])).
% 3.36/1.59  tff(c_274, plain, (![B_78]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', B_78)=k3_xboole_0(B_78, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_227])).
% 3.36/1.59  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.59  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_38])).
% 3.36/1.59  tff(c_131, plain, (![B_53]: (k9_subset_1(k2_struct_0('#skF_1'), B_53, '#skF_3')=k3_xboole_0(B_53, '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_120])).
% 3.36/1.59  tff(c_285, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_274, c_131])).
% 3.36/1.59  tff(c_30, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.59  tff(c_83, plain, (~v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_30])).
% 3.36/1.59  tff(c_158, plain, (~v1_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_83])).
% 3.36/1.59  tff(c_309, plain, (~v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_158])).
% 3.36/1.59  tff(c_36, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.59  tff(c_32, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.59  tff(c_34, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.59  tff(c_393, plain, (![A_81, B_82]: (k2_pre_topc(A_81, B_82)=k2_struct_0(A_81) | ~v1_tops_1(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.59  tff(c_400, plain, (![B_82]: (k2_pre_topc('#skF_1', B_82)=k2_struct_0('#skF_1') | ~v1_tops_1(B_82, '#skF_1') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_393])).
% 3.36/1.59  tff(c_625, plain, (![B_100]: (k2_pre_topc('#skF_1', B_100)=k2_struct_0('#skF_1') | ~v1_tops_1(B_100, '#skF_1') | ~m1_subset_1(B_100, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_400])).
% 3.36/1.59  tff(c_635, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_625])).
% 3.36/1.59  tff(c_646, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_635])).
% 3.36/1.59  tff(c_229, plain, (![B_75]: (k9_subset_1(k2_struct_0('#skF_1'), B_75, '#skF_3')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_75))), inference(resolution, [status(thm)], [c_68, c_223])).
% 3.36/1.59  tff(c_236, plain, (![B_75]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_75)=k3_xboole_0(B_75, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_229])).
% 3.36/1.59  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.59  tff(c_558, plain, (![A_95, C_96, B_97]: (k2_pre_topc(A_95, k9_subset_1(u1_struct_0(A_95), C_96, B_97))=k2_pre_topc(A_95, C_96) | ~v3_pre_topc(C_96, A_95) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~v1_tops_1(B_97, A_95) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.36/1.59  tff(c_563, plain, (![C_96, B_97]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), C_96, B_97))=k2_pre_topc('#skF_1', C_96) | ~v3_pre_topc(C_96, '#skF_1') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_97, '#skF_1') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_558])).
% 3.36/1.59  tff(c_832, plain, (![C_110, B_111]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), C_110, B_111))=k2_pre_topc('#skF_1', C_110) | ~v3_pre_topc(C_110, '#skF_1') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_111, '#skF_1') | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_67, c_67, c_563])).
% 3.36/1.59  tff(c_839, plain, (![B_111]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_111))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_111, '#skF_1') | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_68, c_832])).
% 3.36/1.59  tff(c_992, plain, (![B_121]: (k2_pre_topc('#skF_1', k3_xboole_0(B_121, '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1(B_121, '#skF_1') | ~m1_subset_1(B_121, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_646, c_236, c_839])).
% 3.36/1.59  tff(c_999, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_69, c_992])).
% 3.36/1.59  tff(c_1010, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_285, c_999])).
% 3.36/1.59  tff(c_8, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.59  tff(c_10, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.59  tff(c_45, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.36/1.59  tff(c_85, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.59  tff(c_101, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(resolution, [status(thm)], [c_45, c_85])).
% 3.36/1.59  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.59  tff(c_322, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_285, c_2])).
% 3.36/1.59  tff(c_99, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_69, c_85])).
% 3.36/1.59  tff(c_103, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.59  tff(c_142, plain, (![A_57]: (r1_tarski(A_57, k2_struct_0('#skF_1')) | ~r1_tarski(A_57, '#skF_2'))), inference(resolution, [status(thm)], [c_99, c_103])).
% 3.36/1.59  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.59  tff(c_754, plain, (![A_108, A_109]: (r1_tarski(A_108, k2_struct_0('#skF_1')) | ~r1_tarski(A_108, A_109) | ~r1_tarski(A_109, '#skF_2'))), inference(resolution, [status(thm)], [c_142, c_4])).
% 3.36/1.59  tff(c_770, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_322, c_754])).
% 3.36/1.59  tff(c_804, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_770])).
% 3.36/1.59  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.59  tff(c_443, plain, (![B_83, A_84]: (v1_tops_1(B_83, A_84) | k2_pre_topc(A_84, B_83)!=k2_struct_0(A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.59  tff(c_1361, plain, (![A_130, A_131]: (v1_tops_1(A_130, A_131) | k2_pre_topc(A_131, A_130)!=k2_struct_0(A_131) | ~l1_pre_topc(A_131) | ~r1_tarski(A_130, u1_struct_0(A_131)))), inference(resolution, [status(thm)], [c_18, c_443])).
% 3.36/1.59  tff(c_1376, plain, (![A_130]: (v1_tops_1(A_130, '#skF_1') | k2_pre_topc('#skF_1', A_130)!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_130, k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_67, c_1361])).
% 3.36/1.59  tff(c_1406, plain, (![A_132]: (v1_tops_1(A_132, '#skF_1') | k2_pre_topc('#skF_1', A_132)!=k2_struct_0('#skF_1') | ~r1_tarski(A_132, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1376])).
% 3.36/1.59  tff(c_1424, plain, (v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_804, c_1406])).
% 3.36/1.59  tff(c_1475, plain, (v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_1424])).
% 3.36/1.59  tff(c_1477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_1475])).
% 3.36/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.59  
% 3.36/1.59  Inference rules
% 3.36/1.59  ----------------------
% 3.36/1.59  #Ref     : 0
% 3.36/1.59  #Sup     : 352
% 3.36/1.59  #Fact    : 0
% 3.36/1.59  #Define  : 0
% 3.36/1.59  #Split   : 3
% 3.36/1.59  #Chain   : 0
% 3.36/1.59  #Close   : 0
% 3.36/1.59  
% 3.36/1.59  Ordering : KBO
% 3.36/1.59  
% 3.36/1.59  Simplification rules
% 3.36/1.59  ----------------------
% 3.36/1.59  #Subsume      : 21
% 3.36/1.59  #Demod        : 135
% 3.36/1.59  #Tautology    : 118
% 3.36/1.59  #SimpNegUnit  : 4
% 3.36/1.59  #BackRed      : 4
% 3.36/1.59  
% 3.36/1.59  #Partial instantiations: 0
% 3.36/1.59  #Strategies tried      : 1
% 3.36/1.59  
% 3.36/1.59  Timing (in seconds)
% 3.36/1.59  ----------------------
% 3.36/1.59  Preprocessing        : 0.31
% 3.36/1.59  Parsing              : 0.17
% 3.36/1.59  CNF conversion       : 0.02
% 3.36/1.59  Main loop            : 0.50
% 3.36/1.59  Inferencing          : 0.17
% 3.36/1.59  Reduction            : 0.17
% 3.36/1.59  Demodulation         : 0.13
% 3.36/1.59  BG Simplification    : 0.02
% 3.36/1.59  Subsumption          : 0.09
% 3.36/1.59  Abstraction          : 0.03
% 3.36/1.59  MUC search           : 0.00
% 3.36/1.59  Cooper               : 0.00
% 3.36/1.59  Total                : 0.85
% 3.36/1.59  Index Insertion      : 0.00
% 3.36/1.59  Index Deletion       : 0.00
% 3.36/1.59  Index Matching       : 0.00
% 3.36/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

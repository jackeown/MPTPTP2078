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
% DateTime   : Thu Dec  3 10:20:27 EST 2020

% Result     : Theorem 10.03s
% Output     : CNFRefutation 10.03s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 225 expanded)
%              Number of leaves         :   27 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 ( 496 expanded)
%              Number of equality atoms :   39 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)),k2_pre_topc(A,k7_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => k2_pre_topc(A,k4_subset_1(u1_struct_0(A),B,C)) = k4_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_277,plain,(
    ! [A_77,B_78,C_79] :
      ( k4_subset_1(A_77,B_78,C_79) = k2_xboole_0(B_78,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_390,plain,(
    ! [B_89] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_89,'#skF_3') = k2_xboole_0(B_89,'#skF_3')
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_277])).

tff(c_413,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_390])).

tff(c_431,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_413])).

tff(c_16,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_pre_topc(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_209,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k2_pre_topc(A_64,B_65),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_16,B_17,C_18] :
      ( k7_subset_1(A_16,B_17,C_18) = k4_xboole_0(B_17,C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_606,plain,(
    ! [A_119,B_120,C_121] :
      ( k7_subset_1(u1_struct_0(A_119),k2_pre_topc(A_119,B_120),C_121) = k4_xboole_0(k2_pre_topc(A_119,B_120),C_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_209,c_14])).

tff(c_621,plain,(
    ! [C_121] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_121) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_121)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_606])).

tff(c_645,plain,(
    ! [C_122] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_122) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_621])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k7_subset_1(A_10,B_11,C_12),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_651,plain,(
    ! [C_122] :
      ( m1_subset_1(k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_122),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_10])).

tff(c_1348,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_1360,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1348])).

tff(c_1364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1360])).

tff(c_1366,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_623,plain,(
    ! [C_121] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),C_121) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),C_121)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_606])).

tff(c_657,plain,(
    ! [C_123] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),C_123) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),C_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_623])).

tff(c_663,plain,(
    ! [C_123] :
      ( m1_subset_1(k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),C_123),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_10])).

tff(c_734,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_663])).

tff(c_737,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_734])).

tff(c_741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_737])).

tff(c_743,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_663])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] :
      ( k4_subset_1(A_13,B_14,C_15) = k2_xboole_0(B_14,C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2697,plain,(
    ! [B_250] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_250,k2_pre_topc('#skF_1','#skF_3')) = k2_xboole_0(B_250,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_743,c_12])).

tff(c_2709,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1366,c_2697])).

tff(c_2755,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2709])).

tff(c_18,plain,(
    ! [A_21,B_25,C_27] :
      ( k4_subset_1(u1_struct_0(A_21),k2_pre_topc(A_21,B_25),k2_pre_topc(A_21,C_27)) = k2_pre_topc(A_21,k4_subset_1(u1_struct_0(A_21),B_25,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2783,plain,
    ( k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2755,c_18])).

tff(c_2790,plain,(
    k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_431,c_2783])).

tff(c_30,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_35,B_34] : r1_tarski(A_35,k2_xboole_0(B_34,A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_2864,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2790,c_45])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_164,plain,(
    ! [A_55,B_56,C_57] :
      ( k7_subset_1(A_55,B_56,C_57) = k4_xboole_0(B_56,C_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    ! [C_57] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_57) = k4_xboole_0('#skF_2',C_57) ),
    inference(resolution,[status(thm)],[c_24,c_164])).

tff(c_709,plain,(
    ! [A_130,B_131,B_132,C_133] :
      ( k4_subset_1(A_130,B_131,k7_subset_1(A_130,B_132,C_133)) = k2_xboole_0(B_131,k7_subset_1(A_130,B_132,C_133))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_130)) ) ),
    inference(resolution,[status(thm)],[c_10,c_277])).

tff(c_974,plain,(
    ! [B_149,C_150] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',k7_subset_1(u1_struct_0('#skF_1'),B_149,C_150)) = k2_xboole_0('#skF_3',k7_subset_1(u1_struct_0('#skF_1'),B_149,C_150))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_709])).

tff(c_1001,plain,(
    ! [C_57] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',k4_xboole_0('#skF_2',C_57)) = k2_xboole_0('#skF_3',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_57))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_974])).

tff(c_1016,plain,(
    ! [C_57] : k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',k4_xboole_0('#skF_2',C_57)) = k2_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_169,c_1001])).

tff(c_191,plain,(
    ! [A_60,B_61,C_62] :
      ( m1_subset_1(k7_subset_1(A_60,B_61,C_62),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_199,plain,(
    ! [C_57] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_57),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_191])).

tff(c_204,plain,(
    ! [C_57] : m1_subset_1(k4_xboole_0('#skF_2',C_57),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_199])).

tff(c_865,plain,(
    ! [A_139,B_140,B_141] :
      ( k4_subset_1(u1_struct_0(A_139),B_140,k2_pre_topc(A_139,B_141)) = k2_xboole_0(B_140,k2_pre_topc(A_139,B_141))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_16,c_277])).

tff(c_869,plain,(
    ! [B_141] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_141)) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_141))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_743,c_865])).

tff(c_8611,plain,(
    ! [B_528] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_528)) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_528))
      | ~ m1_subset_1(B_528,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_869])).

tff(c_8626,plain,(
    ! [B_528] :
      ( k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_528)) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_528))
      | ~ m1_subset_1(B_528,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1(B_528,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8611,c_18])).

tff(c_8664,plain,(
    ! [B_529] :
      ( k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_529)) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_529))
      | ~ m1_subset_1(B_529,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_8626])).

tff(c_8733,plain,(
    ! [C_57] : k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2',C_57))) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',k4_xboole_0('#skF_2',C_57))) ),
    inference(resolution,[status(thm)],[c_204,c_8664])).

tff(c_8786,plain,(
    ! [C_57] : k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2',C_57))) = k2_pre_topc('#skF_1',k2_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_57))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_8733])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_640,plain,(
    ! [C_121] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_121) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_621])).

tff(c_20,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_171,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_20])).

tff(c_644,plain,(
    ~ r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_171])).

tff(c_672,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_6,c_644])).

tff(c_8806,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8786,c_672])).

tff(c_8809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2864,c_4,c_8806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.03/3.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.03/3.98  
% 10.03/3.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.03/3.99  %$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 10.03/3.99  
% 10.03/3.99  %Foreground sorts:
% 10.03/3.99  
% 10.03/3.99  
% 10.03/3.99  %Background operators:
% 10.03/3.99  
% 10.03/3.99  
% 10.03/3.99  %Foreground operators:
% 10.03/3.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.03/3.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.03/3.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.03/3.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.03/3.99  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.03/3.99  tff('#skF_2', type, '#skF_2': $i).
% 10.03/3.99  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.03/3.99  tff('#skF_3', type, '#skF_3': $i).
% 10.03/3.99  tff('#skF_1', type, '#skF_1': $i).
% 10.03/3.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.03/3.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.03/3.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.03/3.99  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.03/3.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.03/3.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.03/3.99  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.03/3.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.03/3.99  
% 10.03/4.00  tff(f_80, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)), k2_pre_topc(A, k7_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_1)).
% 10.03/4.00  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.03/4.00  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.03/4.00  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.03/4.00  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.03/4.00  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 10.03/4.00  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k4_subset_1(u1_struct_0(A), B, C)) = k4_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_pre_topc)).
% 10.03/4.00  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.03/4.00  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.03/4.00  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 10.03/4.00  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.03/4.00  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.03/4.00  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.03/4.00  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.03/4.00  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.03/4.00  tff(c_277, plain, (![A_77, B_78, C_79]: (k4_subset_1(A_77, B_78, C_79)=k2_xboole_0(B_78, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.03/4.00  tff(c_390, plain, (![B_89]: (k4_subset_1(u1_struct_0('#skF_1'), B_89, '#skF_3')=k2_xboole_0(B_89, '#skF_3') | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_277])).
% 10.03/4.00  tff(c_413, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_390])).
% 10.03/4.00  tff(c_431, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_413])).
% 10.03/4.00  tff(c_16, plain, (![A_19, B_20]: (m1_subset_1(k2_pre_topc(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.03/4.00  tff(c_209, plain, (![A_64, B_65]: (m1_subset_1(k2_pre_topc(A_64, B_65), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.03/4.00  tff(c_14, plain, (![A_16, B_17, C_18]: (k7_subset_1(A_16, B_17, C_18)=k4_xboole_0(B_17, C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.03/4.00  tff(c_606, plain, (![A_119, B_120, C_121]: (k7_subset_1(u1_struct_0(A_119), k2_pre_topc(A_119, B_120), C_121)=k4_xboole_0(k2_pre_topc(A_119, B_120), C_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_209, c_14])).
% 10.03/4.00  tff(c_621, plain, (![C_121]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_121)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_121) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_606])).
% 10.03/4.00  tff(c_645, plain, (![C_122]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_122)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_122))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_621])).
% 10.03/4.00  tff(c_10, plain, (![A_10, B_11, C_12]: (m1_subset_1(k7_subset_1(A_10, B_11, C_12), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.03/4.00  tff(c_651, plain, (![C_122]: (m1_subset_1(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_122), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_645, c_10])).
% 10.03/4.00  tff(c_1348, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_651])).
% 10.03/4.00  tff(c_1360, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1348])).
% 10.03/4.00  tff(c_1364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1360])).
% 10.03/4.00  tff(c_1366, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_651])).
% 10.03/4.00  tff(c_623, plain, (![C_121]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), C_121)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), C_121) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_606])).
% 10.03/4.00  tff(c_657, plain, (![C_123]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), C_123)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), C_123))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_623])).
% 10.03/4.00  tff(c_663, plain, (![C_123]: (m1_subset_1(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), C_123), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_657, c_10])).
% 10.03/4.00  tff(c_734, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_663])).
% 10.03/4.00  tff(c_737, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_734])).
% 10.03/4.00  tff(c_741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_737])).
% 10.03/4.00  tff(c_743, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_663])).
% 10.03/4.00  tff(c_12, plain, (![A_13, B_14, C_15]: (k4_subset_1(A_13, B_14, C_15)=k2_xboole_0(B_14, C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.03/4.00  tff(c_2697, plain, (![B_250]: (k4_subset_1(u1_struct_0('#skF_1'), B_250, k2_pre_topc('#skF_1', '#skF_3'))=k2_xboole_0(B_250, k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_743, c_12])).
% 10.03/4.00  tff(c_2709, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1366, c_2697])).
% 10.03/4.00  tff(c_2755, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2709])).
% 10.03/4.00  tff(c_18, plain, (![A_21, B_25, C_27]: (k4_subset_1(u1_struct_0(A_21), k2_pre_topc(A_21, B_25), k2_pre_topc(A_21, C_27))=k2_pre_topc(A_21, k4_subset_1(u1_struct_0(A_21), B_25, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.03/4.00  tff(c_2783, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2755, c_18])).
% 10.03/4.00  tff(c_2790, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_431, c_2783])).
% 10.03/4.00  tff(c_30, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.03/4.00  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.03/4.00  tff(c_45, plain, (![A_35, B_34]: (r1_tarski(A_35, k2_xboole_0(B_34, A_35)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8])).
% 10.03/4.00  tff(c_2864, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2790, c_45])).
% 10.03/4.00  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.03/4.00  tff(c_164, plain, (![A_55, B_56, C_57]: (k7_subset_1(A_55, B_56, C_57)=k4_xboole_0(B_56, C_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.03/4.00  tff(c_169, plain, (![C_57]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_57)=k4_xboole_0('#skF_2', C_57))), inference(resolution, [status(thm)], [c_24, c_164])).
% 10.03/4.00  tff(c_709, plain, (![A_130, B_131, B_132, C_133]: (k4_subset_1(A_130, B_131, k7_subset_1(A_130, B_132, C_133))=k2_xboole_0(B_131, k7_subset_1(A_130, B_132, C_133)) | ~m1_subset_1(B_131, k1_zfmisc_1(A_130)) | ~m1_subset_1(B_132, k1_zfmisc_1(A_130)))), inference(resolution, [status(thm)], [c_10, c_277])).
% 10.03/4.00  tff(c_974, plain, (![B_149, C_150]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', k7_subset_1(u1_struct_0('#skF_1'), B_149, C_150))=k2_xboole_0('#skF_3', k7_subset_1(u1_struct_0('#skF_1'), B_149, C_150)) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_709])).
% 10.03/4.00  tff(c_1001, plain, (![C_57]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', k4_xboole_0('#skF_2', C_57))=k2_xboole_0('#skF_3', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_57)) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_169, c_974])).
% 10.03/4.00  tff(c_1016, plain, (![C_57]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', k4_xboole_0('#skF_2', C_57))=k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_57)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_169, c_1001])).
% 10.03/4.00  tff(c_191, plain, (![A_60, B_61, C_62]: (m1_subset_1(k7_subset_1(A_60, B_61, C_62), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.03/4.00  tff(c_199, plain, (![C_57]: (m1_subset_1(k4_xboole_0('#skF_2', C_57), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_169, c_191])).
% 10.03/4.00  tff(c_204, plain, (![C_57]: (m1_subset_1(k4_xboole_0('#skF_2', C_57), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_199])).
% 10.03/4.00  tff(c_865, plain, (![A_139, B_140, B_141]: (k4_subset_1(u1_struct_0(A_139), B_140, k2_pre_topc(A_139, B_141))=k2_xboole_0(B_140, k2_pre_topc(A_139, B_141)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_16, c_277])).
% 10.03/4.00  tff(c_869, plain, (![B_141]: (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_141))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_141)) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_743, c_865])).
% 10.03/4.00  tff(c_8611, plain, (![B_528]: (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_528))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_528)) | ~m1_subset_1(B_528, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_869])).
% 10.03/4.00  tff(c_8626, plain, (![B_528]: (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_528))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_528)) | ~m1_subset_1(B_528, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(B_528, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_8611, c_18])).
% 10.03/4.00  tff(c_8664, plain, (![B_529]: (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_529))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_529)) | ~m1_subset_1(B_529, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_8626])).
% 10.03/4.00  tff(c_8733, plain, (![C_57]: (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', C_57)))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', k4_xboole_0('#skF_2', C_57))))), inference(resolution, [status(thm)], [c_204, c_8664])).
% 10.03/4.00  tff(c_8786, plain, (![C_57]: (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', C_57)))=k2_pre_topc('#skF_1', k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_57))))), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_8733])).
% 10.03/4.00  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.03/4.00  tff(c_640, plain, (![C_121]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_121)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_121))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_621])).
% 10.03/4.00  tff(c_20, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.03/4.00  tff(c_171, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_20])).
% 10.03/4.00  tff(c_644, plain, (~r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_171])).
% 10.03/4.00  tff(c_672, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_644])).
% 10.03/4.00  tff(c_8806, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_8786, c_672])).
% 10.03/4.00  tff(c_8809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2864, c_4, c_8806])).
% 10.03/4.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.03/4.00  
% 10.03/4.00  Inference rules
% 10.03/4.00  ----------------------
% 10.03/4.00  #Ref     : 0
% 10.03/4.00  #Sup     : 2108
% 10.03/4.00  #Fact    : 0
% 10.03/4.00  #Define  : 0
% 10.03/4.00  #Split   : 4
% 10.03/4.00  #Chain   : 0
% 10.03/4.01  #Close   : 0
% 10.03/4.01  
% 10.03/4.01  Ordering : KBO
% 10.03/4.01  
% 10.03/4.01  Simplification rules
% 10.03/4.01  ----------------------
% 10.03/4.01  #Subsume      : 13
% 10.03/4.01  #Demod        : 1817
% 10.03/4.01  #Tautology    : 738
% 10.03/4.01  #SimpNegUnit  : 0
% 10.03/4.01  #BackRed      : 10
% 10.03/4.01  
% 10.03/4.01  #Partial instantiations: 0
% 10.03/4.01  #Strategies tried      : 1
% 10.03/4.01  
% 10.03/4.01  Timing (in seconds)
% 10.03/4.01  ----------------------
% 10.03/4.01  Preprocessing        : 0.32
% 10.03/4.01  Parsing              : 0.17
% 10.03/4.01  CNF conversion       : 0.02
% 10.03/4.01  Main loop            : 2.92
% 10.03/4.01  Inferencing          : 0.77
% 10.03/4.01  Reduction            : 1.45
% 10.03/4.01  Demodulation         : 1.23
% 10.03/4.01  BG Simplification    : 0.08
% 10.03/4.01  Subsumption          : 0.49
% 10.03/4.01  Abstraction          : 0.14
% 10.03/4.01  MUC search           : 0.00
% 10.03/4.01  Cooper               : 0.00
% 10.03/4.01  Total                : 3.27
% 10.03/4.01  Index Insertion      : 0.00
% 10.03/4.01  Index Deletion       : 0.00
% 10.03/4.01  Index Matching       : 0.00
% 10.03/4.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------

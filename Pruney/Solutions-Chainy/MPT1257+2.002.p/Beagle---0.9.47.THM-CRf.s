%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:57 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 378 expanded)
%              Number of leaves         :   28 ( 136 expanded)
%              Depth                    :   17
%              Number of atoms          :  123 ( 799 expanded)
%              Number of equality atoms :   18 ( 104 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_24,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k1_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_42,B_43] :
      ( k2_tops_1(A_42,k3_subset_1(u1_struct_0(A_42),B_43)) = k2_tops_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_114,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_105])).

tff(c_120,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_114])).

tff(c_18,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_tops_1(A_21,B_22),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_124,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_18])).

tff(c_128,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_124])).

tff(c_130,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_133,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_133])).

tff(c_139,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_14,plain,(
    ! [A_16,B_18] :
      ( k3_subset_1(u1_struct_0(A_16),k2_pre_topc(A_16,k3_subset_1(u1_struct_0(A_16),B_18))) = k1_tops_1(A_16,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_138,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_198,plain,(
    ! [A_50,B_51] :
      ( k4_subset_1(u1_struct_0(A_50),B_51,k2_tops_1(A_50,B_51)) = k2_pre_topc(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_200,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_139,c_198])).

tff(c_214,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_120,c_200])).

tff(c_232,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(k3_subset_1(A_52,k4_subset_1(A_52,B_53,C_54)),k3_subset_1(A_52,B_53))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_238,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_232])).

tff(c_253,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_138,c_238])).

tff(c_539,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_253])).

tff(c_544,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_539])).

tff(c_10,plain,(
    ! [B_13,C_15,A_12] :
      ( r1_xboole_0(B_13,C_15)
      | ~ r1_tarski(B_13,k3_subset_1(A_12,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_547,plain,
    ( r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_544,c_10])).

tff(c_550,plain,
    ( r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_547])).

tff(c_551,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_550])).

tff(c_574,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_551])).

tff(c_578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_574])).

tff(c_580,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( k4_subset_1(A_5,B_6,C_7) = k2_xboole_0(B_6,C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_409,plain,(
    ! [B_59] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_59,k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(B_59,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_138,c_6])).

tff(c_412,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_139,c_409])).

tff(c_432,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2,c_412])).

tff(c_927,plain,(
    ! [B_74] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_74,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_xboole_0(B_74,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_139,c_6])).

tff(c_8,plain,(
    ! [A_8,B_9,C_11] :
      ( r1_tarski(k3_subset_1(A_8,k4_subset_1(A_8,B_9,C_11)),k3_subset_1(A_8,B_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_937,plain,(
    ! [B_74] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0(B_74,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),B_74))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_8])).

tff(c_1217,plain,(
    ! [B_77] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0(B_77,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),B_77))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_937])).

tff(c_1223,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_1217])).

tff(c_1238,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1223])).

tff(c_1246,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1238])).

tff(c_1251,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1246])).

tff(c_1254,plain,
    ( r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1251,c_10])).

tff(c_1257,plain,(
    r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_138,c_1254])).

tff(c_1259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.59  
% 3.45/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.59  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.45/1.59  
% 3.45/1.59  %Foreground sorts:
% 3.45/1.59  
% 3.45/1.59  
% 3.45/1.59  %Background operators:
% 3.45/1.59  
% 3.45/1.59  
% 3.45/1.59  %Foreground operators:
% 3.45/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.59  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.45/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.45/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.59  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.45/1.59  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.45/1.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.45/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.45/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.45/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.45/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.45/1.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.45/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.59  
% 3.45/1.61  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_1)).
% 3.45/1.61  tff(f_66, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.45/1.61  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.45/1.61  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 3.45/1.61  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.45/1.61  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.45/1.61  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.45/1.61  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 3.45/1.61  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 3.45/1.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.45/1.61  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.45/1.61  tff(c_24, plain, (~r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.45/1.61  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.45/1.61  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.45/1.61  tff(c_16, plain, (![A_19, B_20]: (m1_subset_1(k1_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.61  tff(c_4, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.61  tff(c_105, plain, (![A_42, B_43]: (k2_tops_1(A_42, k3_subset_1(u1_struct_0(A_42), B_43))=k2_tops_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.45/1.61  tff(c_114, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_105])).
% 3.45/1.61  tff(c_120, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_114])).
% 3.45/1.61  tff(c_18, plain, (![A_21, B_22]: (m1_subset_1(k2_tops_1(A_21, B_22), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.45/1.61  tff(c_124, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_120, c_18])).
% 3.45/1.61  tff(c_128, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_124])).
% 3.45/1.61  tff(c_130, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_128])).
% 3.45/1.61  tff(c_133, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_4, c_130])).
% 3.45/1.61  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_133])).
% 3.45/1.61  tff(c_139, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_128])).
% 3.45/1.61  tff(c_14, plain, (![A_16, B_18]: (k3_subset_1(u1_struct_0(A_16), k2_pre_topc(A_16, k3_subset_1(u1_struct_0(A_16), B_18)))=k1_tops_1(A_16, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.45/1.61  tff(c_138, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_128])).
% 3.45/1.61  tff(c_198, plain, (![A_50, B_51]: (k4_subset_1(u1_struct_0(A_50), B_51, k2_tops_1(A_50, B_51))=k2_pre_topc(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.45/1.61  tff(c_200, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_139, c_198])).
% 3.45/1.61  tff(c_214, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_120, c_200])).
% 3.45/1.61  tff(c_232, plain, (![A_52, B_53, C_54]: (r1_tarski(k3_subset_1(A_52, k4_subset_1(A_52, B_53, C_54)), k3_subset_1(A_52, B_53)) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.45/1.61  tff(c_238, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_214, c_232])).
% 3.45/1.61  tff(c_253, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_138, c_238])).
% 3.45/1.61  tff(c_539, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_253])).
% 3.45/1.61  tff(c_544, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_539])).
% 3.45/1.61  tff(c_10, plain, (![B_13, C_15, A_12]: (r1_xboole_0(B_13, C_15) | ~r1_tarski(B_13, k3_subset_1(A_12, C_15)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.61  tff(c_547, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_544, c_10])).
% 3.45/1.61  tff(c_550, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_547])).
% 3.45/1.61  tff(c_551, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_550])).
% 3.45/1.61  tff(c_574, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_551])).
% 3.45/1.61  tff(c_578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_574])).
% 3.45/1.61  tff(c_580, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_550])).
% 3.45/1.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.45/1.61  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_subset_1(A_5, B_6, C_7)=k2_xboole_0(B_6, C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.45/1.61  tff(c_409, plain, (![B_59]: (k4_subset_1(u1_struct_0('#skF_1'), B_59, k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(B_59, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_138, c_6])).
% 3.45/1.61  tff(c_412, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_139, c_409])).
% 3.45/1.61  tff(c_432, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_2, c_412])).
% 3.45/1.61  tff(c_927, plain, (![B_74]: (k4_subset_1(u1_struct_0('#skF_1'), B_74, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_xboole_0(B_74, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_139, c_6])).
% 3.45/1.61  tff(c_8, plain, (![A_8, B_9, C_11]: (r1_tarski(k3_subset_1(A_8, k4_subset_1(A_8, B_9, C_11)), k3_subset_1(A_8, B_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.45/1.61  tff(c_937, plain, (![B_74]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0(B_74, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), B_74)) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_927, c_8])).
% 3.45/1.61  tff(c_1217, plain, (![B_77]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0(B_77, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), B_77)) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_937])).
% 3.45/1.61  tff(c_1223, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_432, c_1217])).
% 3.45/1.61  tff(c_1238, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_1223])).
% 3.45/1.61  tff(c_1246, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1238])).
% 3.45/1.61  tff(c_1251, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1246])).
% 3.45/1.61  tff(c_1254, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1251, c_10])).
% 3.45/1.61  tff(c_1257, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_138, c_1254])).
% 3.45/1.61  tff(c_1259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1257])).
% 3.45/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.61  
% 3.45/1.61  Inference rules
% 3.45/1.61  ----------------------
% 3.45/1.61  #Ref     : 0
% 3.45/1.61  #Sup     : 287
% 3.45/1.61  #Fact    : 0
% 3.45/1.61  #Define  : 0
% 3.45/1.61  #Split   : 5
% 3.45/1.61  #Chain   : 0
% 3.45/1.61  #Close   : 0
% 3.45/1.61  
% 3.45/1.61  Ordering : KBO
% 3.45/1.61  
% 3.45/1.61  Simplification rules
% 3.45/1.61  ----------------------
% 3.45/1.61  #Subsume      : 7
% 3.45/1.61  #Demod        : 230
% 3.45/1.61  #Tautology    : 111
% 3.45/1.61  #SimpNegUnit  : 1
% 3.45/1.61  #BackRed      : 2
% 3.45/1.61  
% 3.45/1.61  #Partial instantiations: 0
% 3.45/1.61  #Strategies tried      : 1
% 3.45/1.61  
% 3.45/1.61  Timing (in seconds)
% 3.45/1.61  ----------------------
% 3.45/1.61  Preprocessing        : 0.33
% 3.45/1.61  Parsing              : 0.18
% 3.45/1.61  CNF conversion       : 0.02
% 3.45/1.61  Main loop            : 0.49
% 3.45/1.61  Inferencing          : 0.17
% 3.45/1.61  Reduction            : 0.19
% 3.45/1.61  Demodulation         : 0.14
% 3.45/1.61  BG Simplification    : 0.02
% 3.45/1.61  Subsumption          : 0.08
% 3.45/1.61  Abstraction          : 0.03
% 3.45/1.61  MUC search           : 0.00
% 3.45/1.61  Cooper               : 0.00
% 3.45/1.61  Total                : 0.84
% 3.45/1.61  Index Insertion      : 0.00
% 3.45/1.61  Index Deletion       : 0.00
% 3.45/1.61  Index Matching       : 0.00
% 3.45/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

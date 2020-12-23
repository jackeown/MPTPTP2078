%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:18 EST 2020

% Result     : Theorem 8.20s
% Output     : CNFRefutation 8.35s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 253 expanded)
%              Number of leaves         :   51 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  181 ( 436 expanded)
%              Number of equality atoms :   86 ( 153 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_77,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_11509,plain,(
    ! [A_385,B_386,C_387] :
      ( k7_subset_1(A_385,B_386,C_387) = k4_xboole_0(B_386,C_387)
      | ~ m1_subset_1(B_386,k1_zfmisc_1(A_385)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_11534,plain,(
    ! [C_387] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_387) = k4_xboole_0('#skF_2',C_387) ),
    inference(resolution,[status(thm)],[c_58,c_11509])).

tff(c_64,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_121,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4131,plain,(
    ! [A_219,B_220] :
      ( k4_subset_1(u1_struct_0(A_219),B_220,k2_tops_1(A_219,B_220)) = k2_pre_topc(A_219,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4158,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_4131])).

tff(c_4172,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4158])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_210,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_70])).

tff(c_1773,plain,(
    ! [A_152,B_153,C_154] :
      ( k7_subset_1(A_152,B_153,C_154) = k4_xboole_0(B_153,C_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1903,plain,(
    ! [C_162] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_162) = k4_xboole_0('#skF_2',C_162) ),
    inference(resolution,[status(thm)],[c_58,c_1773])).

tff(c_1915,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_1903])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_423,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_447,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_423])).

tff(c_451,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_447])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_374,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_389,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_374])).

tff(c_452,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_389])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_199,plain,(
    ! [A_78,B_79] :
      ( k3_xboole_0(A_78,B_79) = A_78
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_966,plain,(
    ! [A_126,B_127] : k3_xboole_0(k4_xboole_0(A_126,B_127),A_126) = k4_xboole_0(A_126,B_127) ),
    inference(resolution,[status(thm)],[c_14,c_199])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_990,plain,(
    ! [A_126,B_127] : k5_xboole_0(k4_xboole_0(A_126,B_127),k4_xboole_0(A_126,B_127)) = k4_xboole_0(k4_xboole_0(A_126,B_127),A_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_4])).

tff(c_1030,plain,(
    ! [A_126,B_127] : k4_xboole_0(k4_xboole_0(A_126,B_127),A_126) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_990])).

tff(c_2608,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_1030])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2666,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2608,c_16])).

tff(c_2683,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2666])).

tff(c_215,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(A_82,B_83)
      | ~ m1_subset_1(A_82,k1_zfmisc_1(B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_233,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_215])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_237,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_233,c_10])).

tff(c_22,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_169,plain,(
    ! [A_74,B_75] : k1_setfam_1(k2_tarski(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_734,plain,(
    ! [B_114,A_115] : k1_setfam_1(k2_tarski(B_114,A_115)) = k3_xboole_0(A_115,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_169])).

tff(c_40,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_740,plain,(
    ! [B_114,A_115] : k3_xboole_0(B_114,A_115) = k3_xboole_0(A_115,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_40])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_642,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(A_104,C_105)
      | ~ r1_tarski(B_106,C_105)
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1718,plain,(
    ! [A_149,A_150,B_151] :
      ( r1_tarski(A_149,A_150)
      | ~ r1_tarski(A_149,k4_xboole_0(A_150,B_151)) ) ),
    inference(resolution,[status(thm)],[c_14,c_642])).

tff(c_1918,plain,(
    ! [A_163,B_164,B_165] : r1_tarski(k4_xboole_0(k4_xboole_0(A_163,B_164),B_165),A_163) ),
    inference(resolution,[status(thm)],[c_14,c_1718])).

tff(c_2135,plain,(
    ! [A_172,B_173,B_174] : r1_tarski(k4_xboole_0(k3_xboole_0(A_172,B_173),B_174),A_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1918])).

tff(c_2221,plain,(
    ! [A_177,B_178,B_179] : r1_tarski(k4_xboole_0(k3_xboole_0(A_177,B_178),B_179),B_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_2135])).

tff(c_2264,plain,(
    ! [B_179] : r1_tarski(k4_xboole_0('#skF_2',B_179),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_2221])).

tff(c_2587,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_2264])).

tff(c_44,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2849,plain,(
    ! [A_196,B_197,C_198] :
      ( k4_subset_1(A_196,B_197,C_198) = k2_xboole_0(B_197,C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(A_196))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9535,plain,(
    ! [B_290,B_291,A_292] :
      ( k4_subset_1(B_290,B_291,A_292) = k2_xboole_0(B_291,A_292)
      | ~ m1_subset_1(B_291,k1_zfmisc_1(B_290))
      | ~ r1_tarski(A_292,B_290) ) ),
    inference(resolution,[status(thm)],[c_44,c_2849])).

tff(c_9754,plain,(
    ! [A_297] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_297) = k2_xboole_0('#skF_2',A_297)
      | ~ r1_tarski(A_297,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_58,c_9535])).

tff(c_9781,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2587,c_9754])).

tff(c_9863,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4172,c_2683,c_9781])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2541,plain,(
    ! [A_189,B_190] :
      ( v4_pre_topc(k2_pre_topc(A_189,B_190),A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2568,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2541])).

tff(c_2582,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2568])).

tff(c_9891,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9863,c_2582])).

tff(c_9893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_9891])).

tff(c_9894,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_11637,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11534,c_9894])).

tff(c_9895,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_12815,plain,(
    ! [A_434,B_435] :
      ( r1_tarski(k2_tops_1(A_434,B_435),B_435)
      | ~ v4_pre_topc(B_435,A_434)
      | ~ m1_subset_1(B_435,k1_zfmisc_1(u1_struct_0(A_434)))
      | ~ l1_pre_topc(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_12842,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_12815])).

tff(c_12856,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_9895,c_12842])).

tff(c_13345,plain,(
    ! [A_442,B_443] :
      ( k7_subset_1(u1_struct_0(A_442),B_443,k2_tops_1(A_442,B_443)) = k1_tops_1(A_442,B_443)
      | ~ m1_subset_1(B_443,k1_zfmisc_1(u1_struct_0(A_442)))
      | ~ l1_pre_topc(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_13374,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_13345])).

tff(c_13393,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_11534,c_13374])).

tff(c_10854,plain,(
    ! [A_360,B_361] :
      ( k4_xboole_0(A_360,B_361) = k3_subset_1(A_360,B_361)
      | ~ m1_subset_1(B_361,k1_zfmisc_1(A_360)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13886,plain,(
    ! [B_453,A_454] :
      ( k4_xboole_0(B_453,A_454) = k3_subset_1(B_453,A_454)
      | ~ r1_tarski(A_454,B_453) ) ),
    inference(resolution,[status(thm)],[c_44,c_10854])).

tff(c_13922,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12856,c_13886])).

tff(c_13995,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13393,c_13922])).

tff(c_10625,plain,(
    ! [A_349,B_350] :
      ( k3_subset_1(A_349,k3_subset_1(A_349,B_350)) = B_350
      | ~ m1_subset_1(B_350,k1_zfmisc_1(A_349)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14505,plain,(
    ! [B_459,A_460] :
      ( k3_subset_1(B_459,k3_subset_1(B_459,A_460)) = A_460
      | ~ r1_tarski(A_460,B_459) ) ),
    inference(resolution,[status(thm)],[c_44,c_10625])).

tff(c_14526,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13995,c_14505])).

tff(c_14550,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12856,c_14526])).

tff(c_13441,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13393,c_14])).

tff(c_13477,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_13441,c_10])).

tff(c_9942,plain,(
    ! [A_304,B_305] : k1_setfam_1(k2_tarski(A_304,B_305)) = k3_xboole_0(A_304,B_305) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10440,plain,(
    ! [B_338,A_339] : k1_setfam_1(k2_tarski(B_338,A_339)) = k3_xboole_0(A_339,B_338) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_9942])).

tff(c_10446,plain,(
    ! [B_338,A_339] : k3_xboole_0(B_338,A_339) = k3_xboole_0(A_339,B_338) ),
    inference(superposition,[status(thm),theory(equality)],[c_10440,c_40])).

tff(c_36,plain,(
    ! [A_34,B_35] : k6_subset_1(A_34,B_35) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [A_27,B_28] : m1_subset_1(k6_subset_1(A_27,B_28),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,(
    ! [A_27,B_28] : m1_subset_1(k4_xboole_0(A_27,B_28),k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30])).

tff(c_10872,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_subset_1(A_27,k4_xboole_0(A_27,B_28)) ),
    inference(resolution,[status(thm)],[c_71,c_10854])).

tff(c_10884,plain,(
    ! [A_27,B_28] : k3_subset_1(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_10872])).

tff(c_14529,plain,(
    ! [A_27,B_28] :
      ( k3_subset_1(A_27,k3_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28)
      | ~ r1_tarski(k4_xboole_0(A_27,B_28),A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10884,c_14505])).

tff(c_14563,plain,(
    ! [A_461,B_462] : k3_subset_1(A_461,k3_xboole_0(A_461,B_462)) = k4_xboole_0(A_461,B_462) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14529])).

tff(c_14649,plain,(
    ! [B_463,A_464] : k3_subset_1(B_463,k3_xboole_0(A_464,B_463)) = k4_xboole_0(B_463,A_464) ),
    inference(superposition,[status(thm),theory(equality)],[c_10446,c_14563])).

tff(c_14672,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13477,c_14649])).

tff(c_14720,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14550,c_14672])).

tff(c_14722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11637,c_14720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:43:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.20/3.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/3.05  
% 8.20/3.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/3.05  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.20/3.05  
% 8.20/3.05  %Foreground sorts:
% 8.20/3.05  
% 8.20/3.05  
% 8.20/3.05  %Background operators:
% 8.20/3.05  
% 8.20/3.05  
% 8.20/3.05  %Foreground operators:
% 8.20/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.20/3.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.20/3.05  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.20/3.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.20/3.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.20/3.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.20/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.20/3.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.20/3.05  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.20/3.05  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.20/3.05  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.20/3.05  tff('#skF_2', type, '#skF_2': $i).
% 8.20/3.05  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.20/3.05  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.20/3.05  tff('#skF_1', type, '#skF_1': $i).
% 8.20/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.20/3.05  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.20/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.20/3.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.20/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.20/3.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.20/3.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.20/3.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.20/3.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.20/3.05  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.20/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.20/3.05  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.20/3.05  
% 8.35/3.07  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 8.35/3.07  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.35/3.07  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 8.35/3.07  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.35/3.07  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.35/3.07  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.35/3.07  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.35/3.07  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.35/3.07  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.35/3.07  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.35/3.07  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.35/3.07  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.35/3.07  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.35/3.07  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.35/3.07  tff(f_83, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.35/3.07  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.35/3.07  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.35/3.07  tff(f_101, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 8.35/3.07  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 8.35/3.07  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 8.35/3.07  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.35/3.07  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.35/3.07  tff(f_77, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.35/3.07  tff(f_65, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 8.35/3.07  tff(c_58, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.35/3.07  tff(c_11509, plain, (![A_385, B_386, C_387]: (k7_subset_1(A_385, B_386, C_387)=k4_xboole_0(B_386, C_387) | ~m1_subset_1(B_386, k1_zfmisc_1(A_385)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.35/3.07  tff(c_11534, plain, (![C_387]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_387)=k4_xboole_0('#skF_2', C_387))), inference(resolution, [status(thm)], [c_58, c_11509])).
% 8.35/3.07  tff(c_64, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.35/3.07  tff(c_121, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 8.35/3.07  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.35/3.07  tff(c_4131, plain, (![A_219, B_220]: (k4_subset_1(u1_struct_0(A_219), B_220, k2_tops_1(A_219, B_220))=k2_pre_topc(A_219, B_220) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.35/3.07  tff(c_4158, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_4131])).
% 8.35/3.07  tff(c_4172, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4158])).
% 8.35/3.07  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.35/3.07  tff(c_70, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.35/3.07  tff(c_210, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_121, c_70])).
% 8.35/3.07  tff(c_1773, plain, (![A_152, B_153, C_154]: (k7_subset_1(A_152, B_153, C_154)=k4_xboole_0(B_153, C_154) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.35/3.07  tff(c_1903, plain, (![C_162]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_162)=k4_xboole_0('#skF_2', C_162))), inference(resolution, [status(thm)], [c_58, c_1773])).
% 8.35/3.07  tff(c_1915, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_210, c_1903])).
% 8.35/3.07  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.35/3.07  tff(c_18, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.35/3.07  tff(c_423, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k3_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.35/3.07  tff(c_447, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_423])).
% 8.35/3.07  tff(c_451, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_447])).
% 8.35/3.07  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.35/3.07  tff(c_374, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.35/3.07  tff(c_389, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_374])).
% 8.35/3.07  tff(c_452, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_451, c_389])).
% 8.35/3.08  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.35/3.08  tff(c_199, plain, (![A_78, B_79]: (k3_xboole_0(A_78, B_79)=A_78 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.35/3.08  tff(c_966, plain, (![A_126, B_127]: (k3_xboole_0(k4_xboole_0(A_126, B_127), A_126)=k4_xboole_0(A_126, B_127))), inference(resolution, [status(thm)], [c_14, c_199])).
% 8.35/3.08  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.35/3.08  tff(c_990, plain, (![A_126, B_127]: (k5_xboole_0(k4_xboole_0(A_126, B_127), k4_xboole_0(A_126, B_127))=k4_xboole_0(k4_xboole_0(A_126, B_127), A_126))), inference(superposition, [status(thm), theory('equality')], [c_966, c_4])).
% 8.35/3.08  tff(c_1030, plain, (![A_126, B_127]: (k4_xboole_0(k4_xboole_0(A_126, B_127), A_126)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_452, c_990])).
% 8.35/3.08  tff(c_2608, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1915, c_1030])).
% 8.35/3.08  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.35/3.08  tff(c_2666, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2608, c_16])).
% 8.35/3.08  tff(c_2683, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2666])).
% 8.35/3.08  tff(c_215, plain, (![A_82, B_83]: (r1_tarski(A_82, B_83) | ~m1_subset_1(A_82, k1_zfmisc_1(B_83)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.35/3.08  tff(c_233, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_215])).
% 8.35/3.08  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.35/3.08  tff(c_237, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_233, c_10])).
% 8.35/3.08  tff(c_22, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.35/3.08  tff(c_169, plain, (![A_74, B_75]: (k1_setfam_1(k2_tarski(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.35/3.08  tff(c_734, plain, (![B_114, A_115]: (k1_setfam_1(k2_tarski(B_114, A_115))=k3_xboole_0(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_22, c_169])).
% 8.35/3.08  tff(c_40, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.35/3.08  tff(c_740, plain, (![B_114, A_115]: (k3_xboole_0(B_114, A_115)=k3_xboole_0(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_734, c_40])).
% 8.35/3.08  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.35/3.08  tff(c_642, plain, (![A_104, C_105, B_106]: (r1_tarski(A_104, C_105) | ~r1_tarski(B_106, C_105) | ~r1_tarski(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.35/3.08  tff(c_1718, plain, (![A_149, A_150, B_151]: (r1_tarski(A_149, A_150) | ~r1_tarski(A_149, k4_xboole_0(A_150, B_151)))), inference(resolution, [status(thm)], [c_14, c_642])).
% 8.35/3.08  tff(c_1918, plain, (![A_163, B_164, B_165]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_163, B_164), B_165), A_163))), inference(resolution, [status(thm)], [c_14, c_1718])).
% 8.35/3.08  tff(c_2135, plain, (![A_172, B_173, B_174]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_172, B_173), B_174), A_172))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1918])).
% 8.35/3.08  tff(c_2221, plain, (![A_177, B_178, B_179]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_177, B_178), B_179), B_178))), inference(superposition, [status(thm), theory('equality')], [c_740, c_2135])).
% 8.35/3.08  tff(c_2264, plain, (![B_179]: (r1_tarski(k4_xboole_0('#skF_2', B_179), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_237, c_2221])).
% 8.35/3.08  tff(c_2587, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1915, c_2264])).
% 8.35/3.08  tff(c_44, plain, (![A_41, B_42]: (m1_subset_1(A_41, k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.35/3.08  tff(c_2849, plain, (![A_196, B_197, C_198]: (k4_subset_1(A_196, B_197, C_198)=k2_xboole_0(B_197, C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(A_196)) | ~m1_subset_1(B_197, k1_zfmisc_1(A_196)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.35/3.08  tff(c_9535, plain, (![B_290, B_291, A_292]: (k4_subset_1(B_290, B_291, A_292)=k2_xboole_0(B_291, A_292) | ~m1_subset_1(B_291, k1_zfmisc_1(B_290)) | ~r1_tarski(A_292, B_290))), inference(resolution, [status(thm)], [c_44, c_2849])).
% 8.35/3.08  tff(c_9754, plain, (![A_297]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_297)=k2_xboole_0('#skF_2', A_297) | ~r1_tarski(A_297, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_58, c_9535])).
% 8.35/3.08  tff(c_9781, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2587, c_9754])).
% 8.35/3.08  tff(c_9863, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4172, c_2683, c_9781])).
% 8.35/3.08  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.35/3.08  tff(c_2541, plain, (![A_189, B_190]: (v4_pre_topc(k2_pre_topc(A_189, B_190), A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.35/3.08  tff(c_2568, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_2541])).
% 8.35/3.08  tff(c_2582, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2568])).
% 8.35/3.08  tff(c_9891, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9863, c_2582])).
% 8.35/3.08  tff(c_9893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_9891])).
% 8.35/3.08  tff(c_9894, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 8.35/3.08  tff(c_11637, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11534, c_9894])).
% 8.35/3.08  tff(c_9895, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 8.35/3.08  tff(c_12815, plain, (![A_434, B_435]: (r1_tarski(k2_tops_1(A_434, B_435), B_435) | ~v4_pre_topc(B_435, A_434) | ~m1_subset_1(B_435, k1_zfmisc_1(u1_struct_0(A_434))) | ~l1_pre_topc(A_434))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.35/3.08  tff(c_12842, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_12815])).
% 8.35/3.08  tff(c_12856, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_9895, c_12842])).
% 8.35/3.08  tff(c_13345, plain, (![A_442, B_443]: (k7_subset_1(u1_struct_0(A_442), B_443, k2_tops_1(A_442, B_443))=k1_tops_1(A_442, B_443) | ~m1_subset_1(B_443, k1_zfmisc_1(u1_struct_0(A_442))) | ~l1_pre_topc(A_442))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.35/3.08  tff(c_13374, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_13345])).
% 8.35/3.08  tff(c_13393, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_11534, c_13374])).
% 8.35/3.08  tff(c_10854, plain, (![A_360, B_361]: (k4_xboole_0(A_360, B_361)=k3_subset_1(A_360, B_361) | ~m1_subset_1(B_361, k1_zfmisc_1(A_360)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.35/3.08  tff(c_13886, plain, (![B_453, A_454]: (k4_xboole_0(B_453, A_454)=k3_subset_1(B_453, A_454) | ~r1_tarski(A_454, B_453))), inference(resolution, [status(thm)], [c_44, c_10854])).
% 8.35/3.08  tff(c_13922, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12856, c_13886])).
% 8.35/3.08  tff(c_13995, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13393, c_13922])).
% 8.35/3.08  tff(c_10625, plain, (![A_349, B_350]: (k3_subset_1(A_349, k3_subset_1(A_349, B_350))=B_350 | ~m1_subset_1(B_350, k1_zfmisc_1(A_349)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.35/3.08  tff(c_14505, plain, (![B_459, A_460]: (k3_subset_1(B_459, k3_subset_1(B_459, A_460))=A_460 | ~r1_tarski(A_460, B_459))), inference(resolution, [status(thm)], [c_44, c_10625])).
% 8.35/3.08  tff(c_14526, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13995, c_14505])).
% 8.35/3.08  tff(c_14550, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12856, c_14526])).
% 8.35/3.08  tff(c_13441, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13393, c_14])).
% 8.35/3.08  tff(c_13477, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_13441, c_10])).
% 8.35/3.08  tff(c_9942, plain, (![A_304, B_305]: (k1_setfam_1(k2_tarski(A_304, B_305))=k3_xboole_0(A_304, B_305))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.35/3.08  tff(c_10440, plain, (![B_338, A_339]: (k1_setfam_1(k2_tarski(B_338, A_339))=k3_xboole_0(A_339, B_338))), inference(superposition, [status(thm), theory('equality')], [c_22, c_9942])).
% 8.35/3.08  tff(c_10446, plain, (![B_338, A_339]: (k3_xboole_0(B_338, A_339)=k3_xboole_0(A_339, B_338))), inference(superposition, [status(thm), theory('equality')], [c_10440, c_40])).
% 8.35/3.08  tff(c_36, plain, (![A_34, B_35]: (k6_subset_1(A_34, B_35)=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.35/3.08  tff(c_30, plain, (![A_27, B_28]: (m1_subset_1(k6_subset_1(A_27, B_28), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.35/3.08  tff(c_71, plain, (![A_27, B_28]: (m1_subset_1(k4_xboole_0(A_27, B_28), k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30])).
% 8.35/3.08  tff(c_10872, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_subset_1(A_27, k4_xboole_0(A_27, B_28)))), inference(resolution, [status(thm)], [c_71, c_10854])).
% 8.35/3.08  tff(c_10884, plain, (![A_27, B_28]: (k3_subset_1(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_10872])).
% 8.35/3.08  tff(c_14529, plain, (![A_27, B_28]: (k3_subset_1(A_27, k3_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28) | ~r1_tarski(k4_xboole_0(A_27, B_28), A_27))), inference(superposition, [status(thm), theory('equality')], [c_10884, c_14505])).
% 8.35/3.08  tff(c_14563, plain, (![A_461, B_462]: (k3_subset_1(A_461, k3_xboole_0(A_461, B_462))=k4_xboole_0(A_461, B_462))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14529])).
% 8.35/3.08  tff(c_14649, plain, (![B_463, A_464]: (k3_subset_1(B_463, k3_xboole_0(A_464, B_463))=k4_xboole_0(B_463, A_464))), inference(superposition, [status(thm), theory('equality')], [c_10446, c_14563])).
% 8.35/3.08  tff(c_14672, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13477, c_14649])).
% 8.35/3.08  tff(c_14720, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14550, c_14672])).
% 8.35/3.08  tff(c_14722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11637, c_14720])).
% 8.35/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/3.08  
% 8.35/3.08  Inference rules
% 8.35/3.08  ----------------------
% 8.35/3.08  #Ref     : 0
% 8.35/3.08  #Sup     : 3560
% 8.35/3.08  #Fact    : 0
% 8.35/3.08  #Define  : 0
% 8.35/3.08  #Split   : 1
% 8.35/3.08  #Chain   : 0
% 8.35/3.08  #Close   : 0
% 8.35/3.08  
% 8.35/3.08  Ordering : KBO
% 8.35/3.08  
% 8.35/3.08  Simplification rules
% 8.35/3.08  ----------------------
% 8.35/3.08  #Subsume      : 135
% 8.35/3.08  #Demod        : 3116
% 8.35/3.08  #Tautology    : 2401
% 8.35/3.08  #SimpNegUnit  : 3
% 8.35/3.08  #BackRed      : 8
% 8.35/3.08  
% 8.35/3.08  #Partial instantiations: 0
% 8.35/3.08  #Strategies tried      : 1
% 8.35/3.08  
% 8.35/3.08  Timing (in seconds)
% 8.35/3.08  ----------------------
% 8.35/3.08  Preprocessing        : 0.37
% 8.35/3.08  Parsing              : 0.20
% 8.35/3.08  CNF conversion       : 0.02
% 8.35/3.08  Main loop            : 1.90
% 8.35/3.08  Inferencing          : 0.50
% 8.35/3.08  Reduction            : 0.90
% 8.35/3.08  Demodulation         : 0.73
% 8.35/3.08  BG Simplification    : 0.06
% 8.35/3.08  Subsumption          : 0.32
% 8.35/3.08  Abstraction          : 0.08
% 8.35/3.08  MUC search           : 0.00
% 8.35/3.08  Cooper               : 0.00
% 8.35/3.08  Total                : 2.31
% 8.35/3.08  Index Insertion      : 0.00
% 8.35/3.08  Index Deletion       : 0.00
% 8.35/3.08  Index Matching       : 0.00
% 8.35/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------

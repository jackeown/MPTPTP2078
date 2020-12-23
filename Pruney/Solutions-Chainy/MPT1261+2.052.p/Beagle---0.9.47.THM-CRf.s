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
% DateTime   : Thu Dec  3 10:21:19 EST 2020

% Result     : Theorem 14.40s
% Output     : CNFRefutation 14.54s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 355 expanded)
%              Number of leaves         :   50 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          :  218 ( 558 expanded)
%              Number of equality atoms :  105 ( 247 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_87,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_24468,plain,(
    ! [A_548,B_549,C_550] :
      ( k7_subset_1(A_548,B_549,C_550) = k4_xboole_0(B_549,C_550)
      | ~ m1_subset_1(B_549,k1_zfmisc_1(A_548)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24477,plain,(
    ! [C_550] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_550) = k4_xboole_0('#skF_2',C_550) ),
    inference(resolution,[status(thm)],[c_58,c_24468])).

tff(c_64,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_106,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_202,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_70])).

tff(c_1999,plain,(
    ! [A_160,B_161,C_162] :
      ( k7_subset_1(A_160,B_161,C_162) = k4_xboole_0(B_161,C_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2043,plain,(
    ! [C_164] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_164) = k4_xboole_0('#skF_2',C_164) ),
    inference(resolution,[status(thm)],[c_58,c_1999])).

tff(c_2055,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_2043])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_162,plain,(
    ! [A_76,B_77] : k1_setfam_1(k2_tarski(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_546,plain,(
    ! [B_108,A_109] : k1_setfam_1(k2_tarski(B_108,A_109)) = k3_xboole_0(A_109,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_162])).

tff(c_40,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_552,plain,(
    ! [B_108,A_109] : k3_xboole_0(B_108,A_109) = k3_xboole_0(A_109,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_40])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_835,plain,(
    ! [A_124,B_125,C_126] :
      ( r1_tarski(k4_xboole_0(A_124,B_125),C_126)
      | ~ r1_tarski(A_124,k2_xboole_0(B_125,C_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_339,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_348,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_339])).

tff(c_351,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_348])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_177,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_207,plain,(
    ! [B_84,A_85] : k3_tarski(k2_tarski(B_84,A_85)) = k2_xboole_0(A_85,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_177])).

tff(c_28,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_230,plain,(
    ! [B_86,A_87] : k2_xboole_0(B_86,A_87) = k2_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_28])).

tff(c_283,plain,(
    ! [A_88] : k2_xboole_0(k1_xboole_0,A_88) = A_88 ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_4])).

tff(c_383,plain,(
    ! [B_95] : k3_xboole_0(k1_xboole_0,B_95) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_283])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_391,plain,(
    ! [B_95] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_2])).

tff(c_410,plain,(
    ! [B_96] : k4_xboole_0(k1_xboole_0,B_96) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_391])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_418,plain,(
    ! [B_96] :
      ( k1_xboole_0 = B_96
      | ~ r1_tarski(B_96,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_14])).

tff(c_846,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(A_124,B_125) = k1_xboole_0
      | ~ r1_tarski(A_124,k2_xboole_0(B_125,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_835,c_418])).

tff(c_988,plain,(
    ! [A_135,B_136] :
      ( k4_xboole_0(A_135,B_136) = k1_xboole_0
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_846])).

tff(c_1278,plain,(
    ! [A_144,B_145] : k4_xboole_0(k4_xboole_0(A_144,B_145),A_144) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_988])).

tff(c_22,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1304,plain,(
    ! [A_144,B_145] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_144,B_145),A_144),k1_xboole_0) = k4_xboole_0(A_144,B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_22])).

tff(c_21366,plain,(
    ! [A_467,B_468] : k3_xboole_0(A_467,k4_xboole_0(A_467,B_468)) = k4_xboole_0(A_467,B_468) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_552,c_1304])).

tff(c_21883,plain,(
    ! [A_469,B_470] : k2_xboole_0(A_469,k4_xboole_0(A_469,B_470)) = A_469 ),
    inference(superposition,[status(thm),theory(equality)],[c_21366,c_8])).

tff(c_22253,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2055,c_21883])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_3694,plain,(
    ! [A_219,B_220] :
      ( k4_subset_1(u1_struct_0(A_219),B_220,k2_tops_1(A_219,B_220)) = k2_pre_topc(A_219,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3704,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_3694])).

tff(c_3710,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3704])).

tff(c_96,plain,(
    ! [A_65,B_66] : r1_tarski(k4_xboole_0(A_65,B_66),A_65) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [A_14] : r1_tarski(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_96])).

tff(c_2702,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2055,c_12])).

tff(c_192,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_196,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_192])).

tff(c_472,plain,(
    ! [A_101,C_102,B_103] :
      ( r1_tarski(A_101,C_102)
      | ~ r1_tarski(B_103,C_102)
      | ~ r1_tarski(A_101,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_520,plain,(
    ! [A_105] :
      ( r1_tarski(A_105,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_105,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_196,c_472])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_523,plain,(
    ! [A_4,A_105] :
      ( r1_tarski(A_4,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_4,A_105)
      | ~ r1_tarski(A_105,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_520,c_6])).

tff(c_2710,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2702,c_523])).

tff(c_2716,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_2710])).

tff(c_44,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,k1_zfmisc_1(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3007,plain,(
    ! [A_196,B_197,C_198] :
      ( k4_subset_1(A_196,B_197,C_198) = k2_xboole_0(B_197,C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(A_196))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9038,plain,(
    ! [B_333,B_334,A_335] :
      ( k4_subset_1(B_333,B_334,A_335) = k2_xboole_0(B_334,A_335)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(B_333))
      | ~ r1_tarski(A_335,B_333) ) ),
    inference(resolution,[status(thm)],[c_44,c_3007])).

tff(c_9186,plain,(
    ! [A_338] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_338) = k2_xboole_0('#skF_2',A_338)
      | ~ r1_tarski(A_338,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_58,c_9038])).

tff(c_9261,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2716,c_9186])).

tff(c_9346,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3710,c_9261])).

tff(c_22680,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22253,c_9346])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2119,plain,(
    ! [A_165,B_166] :
      ( v4_pre_topc(k2_pre_topc(A_165,B_166),A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2127,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2119])).

tff(c_2132,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2127])).

tff(c_22832,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22680,c_2132])).

tff(c_22851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_22832])).

tff(c_22852,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_24481,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24477,c_22852])).

tff(c_22853,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_25322,plain,(
    ! [A_588,B_589] :
      ( r1_tarski(k2_tops_1(A_588,B_589),B_589)
      | ~ v4_pre_topc(B_589,A_588)
      | ~ m1_subset_1(B_589,k1_zfmisc_1(u1_struct_0(A_588)))
      | ~ l1_pre_topc(A_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_25332,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_25322])).

tff(c_25338,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22853,c_25332])).

tff(c_26038,plain,(
    ! [A_612,B_613] :
      ( k7_subset_1(u1_struct_0(A_612),B_613,k2_tops_1(A_612,B_613)) = k1_tops_1(A_612,B_613)
      | ~ m1_subset_1(B_613,k1_zfmisc_1(u1_struct_0(A_612)))
      | ~ l1_pre_topc(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_26048,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_26038])).

tff(c_26054,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_24477,c_26048])).

tff(c_24135,plain,(
    ! [A_539,B_540] :
      ( k4_xboole_0(A_539,B_540) = k3_subset_1(A_539,B_540)
      | ~ m1_subset_1(B_540,k1_zfmisc_1(A_539)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_27140,plain,(
    ! [B_650,A_651] :
      ( k4_xboole_0(B_650,A_651) = k3_subset_1(B_650,A_651)
      | ~ r1_tarski(A_651,B_650) ) ),
    inference(resolution,[status(thm)],[c_44,c_24135])).

tff(c_27221,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_25338,c_27140])).

tff(c_27327,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26054,c_27221])).

tff(c_23566,plain,(
    ! [A_522,B_523] :
      ( k3_subset_1(A_522,k3_subset_1(A_522,B_523)) = B_523
      | ~ m1_subset_1(B_523,k1_zfmisc_1(A_522)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_23571,plain,(
    ! [B_44,A_43] :
      ( k3_subset_1(B_44,k3_subset_1(B_44,A_43)) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_44,c_23566])).

tff(c_27924,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27327,c_23571])).

tff(c_27934,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25338,c_27924])).

tff(c_22904,plain,(
    ! [A_475,B_476] : k1_setfam_1(k2_tarski(A_475,B_476)) = k3_xboole_0(A_475,B_476) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22950,plain,(
    ! [B_485,A_486] : k1_setfam_1(k2_tarski(B_485,A_486)) = k3_xboole_0(A_486,B_485) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_22904])).

tff(c_22956,plain,(
    ! [B_485,A_486] : k3_xboole_0(B_485,A_486) = k3_xboole_0(A_486,B_485) ),
    inference(superposition,[status(thm),theory(equality)],[c_22950,c_40])).

tff(c_26207,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26054,c_12])).

tff(c_23358,plain,(
    ! [A_510,B_511,C_512] :
      ( r1_tarski(k4_xboole_0(A_510,B_511),C_512)
      | ~ r1_tarski(A_510,k2_xboole_0(B_511,C_512)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_23063,plain,(
    ! [A_490,B_491] : k5_xboole_0(A_490,k3_xboole_0(A_490,B_491)) = k4_xboole_0(A_490,B_491) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_23081,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_23063])).

tff(c_23084,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_23081])).

tff(c_22973,plain,(
    ! [B_487,A_488] : k3_xboole_0(B_487,A_488) = k3_xboole_0(A_488,B_487) ),
    inference(superposition,[status(thm),theory(equality)],[c_22950,c_40])).

tff(c_22995,plain,(
    ! [A_488] : k3_xboole_0(k1_xboole_0,A_488) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22973,c_10])).

tff(c_23072,plain,(
    ! [A_488] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_488) ),
    inference(superposition,[status(thm),theory(equality)],[c_22995,c_23063])).

tff(c_23138,plain,(
    ! [A_495] : k4_xboole_0(k1_xboole_0,A_495) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23084,c_23072])).

tff(c_23143,plain,(
    ! [A_495] :
      ( k1_xboole_0 = A_495
      | ~ r1_tarski(A_495,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23138,c_14])).

tff(c_23365,plain,(
    ! [A_510,B_511] :
      ( k4_xboole_0(A_510,B_511) = k1_xboole_0
      | ~ r1_tarski(A_510,k2_xboole_0(B_511,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_23358,c_23143])).

tff(c_23381,plain,(
    ! [A_510,B_511] :
      ( k4_xboole_0(A_510,B_511) = k1_xboole_0
      | ~ r1_tarski(A_510,B_511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_23365])).

tff(c_26217,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26207,c_23381])).

tff(c_26240,plain,(
    k2_xboole_0(k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2'),k1_xboole_0) = k1_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26217,c_22])).

tff(c_26256,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_22956,c_26240])).

tff(c_23162,plain,(
    ! [A_496,B_497] : k2_xboole_0(k3_xboole_0(A_496,B_497),k4_xboole_0(A_496,B_497)) = A_496 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_23168,plain,(
    ! [A_496,B_497] : r1_tarski(k3_xboole_0(A_496,B_497),A_496) ),
    inference(superposition,[status(thm),theory(equality)],[c_23162,c_24])).

tff(c_23524,plain,(
    ! [A_520,B_521] :
      ( k4_xboole_0(A_520,B_521) = k1_xboole_0
      | ~ r1_tarski(A_520,B_521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_23365])).

tff(c_23749,plain,(
    ! [A_529,B_530] : k4_xboole_0(k3_xboole_0(A_529,B_530),A_529) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23168,c_23524])).

tff(c_23760,plain,(
    ! [A_529,B_530] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_529,B_530),A_529),k1_xboole_0) = k3_xboole_0(A_529,B_530) ),
    inference(superposition,[status(thm),theory(equality)],[c_23749,c_22])).

tff(c_34217,plain,(
    ! [A_750,B_751] : k3_xboole_0(A_750,k3_xboole_0(A_750,B_751)) = k3_xboole_0(A_750,B_751) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_22956,c_23760])).

tff(c_34343,plain,(
    ! [A_750,B_751] : k5_xboole_0(A_750,k3_xboole_0(A_750,B_751)) = k4_xboole_0(A_750,k3_xboole_0(A_750,B_751)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34217,c_2])).

tff(c_34438,plain,(
    ! [A_750,B_751] : k4_xboole_0(A_750,k3_xboole_0(A_750,B_751)) = k4_xboole_0(A_750,B_751) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34343])).

tff(c_27349,plain,(
    ! [A_496,B_497] : k4_xboole_0(A_496,k3_xboole_0(A_496,B_497)) = k3_subset_1(A_496,k3_xboole_0(A_496,B_497)) ),
    inference(resolution,[status(thm)],[c_23168,c_27140])).

tff(c_57473,plain,(
    ! [A_946,B_947] : k3_subset_1(A_946,k3_xboole_0(A_946,B_947)) = k4_xboole_0(A_946,B_947) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34438,c_27349])).

tff(c_57585,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26256,c_57473])).

tff(c_57665,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27934,c_57585])).

tff(c_57667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24481,c_57665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.40/7.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.40/7.26  
% 14.40/7.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.40/7.26  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 14.40/7.26  
% 14.40/7.26  %Foreground sorts:
% 14.40/7.26  
% 14.40/7.26  
% 14.40/7.26  %Background operators:
% 14.40/7.26  
% 14.40/7.26  
% 14.40/7.26  %Foreground operators:
% 14.40/7.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.40/7.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.40/7.26  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 14.40/7.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.40/7.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.40/7.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.40/7.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.40/7.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.40/7.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.40/7.26  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.40/7.26  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.40/7.26  tff('#skF_2', type, '#skF_2': $i).
% 14.40/7.26  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.40/7.26  tff('#skF_1', type, '#skF_1': $i).
% 14.40/7.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.40/7.26  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.40/7.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.40/7.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.40/7.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.40/7.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.40/7.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.40/7.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.40/7.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.40/7.26  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.40/7.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.40/7.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.40/7.26  
% 14.54/7.29  tff(f_147, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 14.54/7.29  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.54/7.29  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 14.54/7.29  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.54/7.29  tff(f_87, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.54/7.29  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.54/7.29  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 14.54/7.29  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 14.54/7.29  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 14.54/7.29  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.54/7.29  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 14.54/7.29  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 14.54/7.29  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 14.54/7.29  tff(f_57, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 14.54/7.29  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 14.54/7.29  tff(f_91, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.54/7.29  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.54/7.29  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.54/7.29  tff(f_105, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 14.54/7.29  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 14.54/7.29  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 14.54/7.29  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 14.54/7.29  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.54/7.29  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.54/7.29  tff(c_58, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.54/7.29  tff(c_24468, plain, (![A_548, B_549, C_550]: (k7_subset_1(A_548, B_549, C_550)=k4_xboole_0(B_549, C_550) | ~m1_subset_1(B_549, k1_zfmisc_1(A_548)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.54/7.29  tff(c_24477, plain, (![C_550]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_550)=k4_xboole_0('#skF_2', C_550))), inference(resolution, [status(thm)], [c_58, c_24468])).
% 14.54/7.29  tff(c_64, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.54/7.29  tff(c_106, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 14.54/7.29  tff(c_70, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.54/7.29  tff(c_202, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_106, c_70])).
% 14.54/7.29  tff(c_1999, plain, (![A_160, B_161, C_162]: (k7_subset_1(A_160, B_161, C_162)=k4_xboole_0(B_161, C_162) | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.54/7.29  tff(c_2043, plain, (![C_164]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_164)=k4_xboole_0('#skF_2', C_164))), inference(resolution, [status(thm)], [c_58, c_1999])).
% 14.54/7.29  tff(c_2055, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_202, c_2043])).
% 14.54/7.29  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.54/7.29  tff(c_26, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.54/7.29  tff(c_162, plain, (![A_76, B_77]: (k1_setfam_1(k2_tarski(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.54/7.29  tff(c_546, plain, (![B_108, A_109]: (k1_setfam_1(k2_tarski(B_108, A_109))=k3_xboole_0(A_109, B_108))), inference(superposition, [status(thm), theory('equality')], [c_26, c_162])).
% 14.54/7.29  tff(c_40, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.54/7.29  tff(c_552, plain, (![B_108, A_109]: (k3_xboole_0(B_108, A_109)=k3_xboole_0(A_109, B_108))), inference(superposition, [status(thm), theory('equality')], [c_546, c_40])).
% 14.54/7.29  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.54/7.29  tff(c_835, plain, (![A_124, B_125, C_126]: (r1_tarski(k4_xboole_0(A_124, B_125), C_126) | ~r1_tarski(A_124, k2_xboole_0(B_125, C_126)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.54/7.29  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.54/7.29  tff(c_10, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.54/7.29  tff(c_339, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.54/7.29  tff(c_348, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_339])).
% 14.54/7.29  tff(c_351, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_348])).
% 14.54/7.29  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.54/7.29  tff(c_177, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.54/7.29  tff(c_207, plain, (![B_84, A_85]: (k3_tarski(k2_tarski(B_84, A_85))=k2_xboole_0(A_85, B_84))), inference(superposition, [status(thm), theory('equality')], [c_26, c_177])).
% 14.54/7.29  tff(c_28, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.54/7.29  tff(c_230, plain, (![B_86, A_87]: (k2_xboole_0(B_86, A_87)=k2_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_207, c_28])).
% 14.54/7.29  tff(c_283, plain, (![A_88]: (k2_xboole_0(k1_xboole_0, A_88)=A_88)), inference(superposition, [status(thm), theory('equality')], [c_230, c_4])).
% 14.54/7.29  tff(c_383, plain, (![B_95]: (k3_xboole_0(k1_xboole_0, B_95)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_283])).
% 14.54/7.29  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.54/7.29  tff(c_391, plain, (![B_95]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_95))), inference(superposition, [status(thm), theory('equality')], [c_383, c_2])).
% 14.54/7.29  tff(c_410, plain, (![B_96]: (k4_xboole_0(k1_xboole_0, B_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_351, c_391])).
% 14.54/7.29  tff(c_14, plain, (![A_12, B_13]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k4_xboole_0(B_13, A_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.54/7.29  tff(c_418, plain, (![B_96]: (k1_xboole_0=B_96 | ~r1_tarski(B_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_410, c_14])).
% 14.54/7.29  tff(c_846, plain, (![A_124, B_125]: (k4_xboole_0(A_124, B_125)=k1_xboole_0 | ~r1_tarski(A_124, k2_xboole_0(B_125, k1_xboole_0)))), inference(resolution, [status(thm)], [c_835, c_418])).
% 14.54/7.29  tff(c_988, plain, (![A_135, B_136]: (k4_xboole_0(A_135, B_136)=k1_xboole_0 | ~r1_tarski(A_135, B_136))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_846])).
% 14.54/7.29  tff(c_1278, plain, (![A_144, B_145]: (k4_xboole_0(k4_xboole_0(A_144, B_145), A_144)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_988])).
% 14.54/7.29  tff(c_22, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.54/7.29  tff(c_1304, plain, (![A_144, B_145]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_144, B_145), A_144), k1_xboole_0)=k4_xboole_0(A_144, B_145))), inference(superposition, [status(thm), theory('equality')], [c_1278, c_22])).
% 14.54/7.29  tff(c_21366, plain, (![A_467, B_468]: (k3_xboole_0(A_467, k4_xboole_0(A_467, B_468))=k4_xboole_0(A_467, B_468))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_552, c_1304])).
% 14.54/7.29  tff(c_21883, plain, (![A_469, B_470]: (k2_xboole_0(A_469, k4_xboole_0(A_469, B_470))=A_469)), inference(superposition, [status(thm), theory('equality')], [c_21366, c_8])).
% 14.54/7.29  tff(c_22253, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2055, c_21883])).
% 14.54/7.29  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.54/7.29  tff(c_3694, plain, (![A_219, B_220]: (k4_subset_1(u1_struct_0(A_219), B_220, k2_tops_1(A_219, B_220))=k2_pre_topc(A_219, B_220) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_119])).
% 14.54/7.29  tff(c_3704, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_3694])).
% 14.54/7.29  tff(c_3710, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3704])).
% 14.54/7.29  tff(c_96, plain, (![A_65, B_66]: (r1_tarski(k4_xboole_0(A_65, B_66), A_65))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.54/7.29  tff(c_99, plain, (![A_14]: (r1_tarski(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_96])).
% 14.54/7.29  tff(c_2702, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2055, c_12])).
% 14.54/7.29  tff(c_192, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~m1_subset_1(A_80, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.54/7.29  tff(c_196, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_192])).
% 14.54/7.29  tff(c_472, plain, (![A_101, C_102, B_103]: (r1_tarski(A_101, C_102) | ~r1_tarski(B_103, C_102) | ~r1_tarski(A_101, B_103))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.54/7.29  tff(c_520, plain, (![A_105]: (r1_tarski(A_105, u1_struct_0('#skF_1')) | ~r1_tarski(A_105, '#skF_2'))), inference(resolution, [status(thm)], [c_196, c_472])).
% 14.54/7.29  tff(c_6, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(B_5, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.54/7.29  tff(c_523, plain, (![A_4, A_105]: (r1_tarski(A_4, u1_struct_0('#skF_1')) | ~r1_tarski(A_4, A_105) | ~r1_tarski(A_105, '#skF_2'))), inference(resolution, [status(thm)], [c_520, c_6])).
% 14.54/7.29  tff(c_2710, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2702, c_523])).
% 14.54/7.29  tff(c_2716, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_2710])).
% 14.54/7.29  tff(c_44, plain, (![A_43, B_44]: (m1_subset_1(A_43, k1_zfmisc_1(B_44)) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.54/7.29  tff(c_3007, plain, (![A_196, B_197, C_198]: (k4_subset_1(A_196, B_197, C_198)=k2_xboole_0(B_197, C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(A_196)) | ~m1_subset_1(B_197, k1_zfmisc_1(A_196)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.54/7.29  tff(c_9038, plain, (![B_333, B_334, A_335]: (k4_subset_1(B_333, B_334, A_335)=k2_xboole_0(B_334, A_335) | ~m1_subset_1(B_334, k1_zfmisc_1(B_333)) | ~r1_tarski(A_335, B_333))), inference(resolution, [status(thm)], [c_44, c_3007])).
% 14.54/7.29  tff(c_9186, plain, (![A_338]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_338)=k2_xboole_0('#skF_2', A_338) | ~r1_tarski(A_338, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_58, c_9038])).
% 14.54/7.29  tff(c_9261, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2716, c_9186])).
% 14.54/7.29  tff(c_9346, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3710, c_9261])).
% 14.54/7.29  tff(c_22680, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22253, c_9346])).
% 14.54/7.29  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.54/7.29  tff(c_2119, plain, (![A_165, B_166]: (v4_pre_topc(k2_pre_topc(A_165, B_166), A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.54/7.29  tff(c_2127, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_2119])).
% 14.54/7.29  tff(c_2132, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2127])).
% 14.54/7.29  tff(c_22832, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22680, c_2132])).
% 14.54/7.29  tff(c_22851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_22832])).
% 14.54/7.29  tff(c_22852, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 14.54/7.29  tff(c_24481, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24477, c_22852])).
% 14.54/7.29  tff(c_22853, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 14.54/7.29  tff(c_25322, plain, (![A_588, B_589]: (r1_tarski(k2_tops_1(A_588, B_589), B_589) | ~v4_pre_topc(B_589, A_588) | ~m1_subset_1(B_589, k1_zfmisc_1(u1_struct_0(A_588))) | ~l1_pre_topc(A_588))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.54/7.29  tff(c_25332, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_25322])).
% 14.54/7.29  tff(c_25338, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22853, c_25332])).
% 14.54/7.29  tff(c_26038, plain, (![A_612, B_613]: (k7_subset_1(u1_struct_0(A_612), B_613, k2_tops_1(A_612, B_613))=k1_tops_1(A_612, B_613) | ~m1_subset_1(B_613, k1_zfmisc_1(u1_struct_0(A_612))) | ~l1_pre_topc(A_612))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.54/7.29  tff(c_26048, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_26038])).
% 14.54/7.29  tff(c_26054, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_24477, c_26048])).
% 14.54/7.29  tff(c_24135, plain, (![A_539, B_540]: (k4_xboole_0(A_539, B_540)=k3_subset_1(A_539, B_540) | ~m1_subset_1(B_540, k1_zfmisc_1(A_539)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.54/7.29  tff(c_27140, plain, (![B_650, A_651]: (k4_xboole_0(B_650, A_651)=k3_subset_1(B_650, A_651) | ~r1_tarski(A_651, B_650))), inference(resolution, [status(thm)], [c_44, c_24135])).
% 14.54/7.29  tff(c_27221, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_25338, c_27140])).
% 14.54/7.29  tff(c_27327, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26054, c_27221])).
% 14.54/7.29  tff(c_23566, plain, (![A_522, B_523]: (k3_subset_1(A_522, k3_subset_1(A_522, B_523))=B_523 | ~m1_subset_1(B_523, k1_zfmisc_1(A_522)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.54/7.29  tff(c_23571, plain, (![B_44, A_43]: (k3_subset_1(B_44, k3_subset_1(B_44, A_43))=A_43 | ~r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_44, c_23566])).
% 14.54/7.29  tff(c_27924, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27327, c_23571])).
% 14.54/7.29  tff(c_27934, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25338, c_27924])).
% 14.54/7.29  tff(c_22904, plain, (![A_475, B_476]: (k1_setfam_1(k2_tarski(A_475, B_476))=k3_xboole_0(A_475, B_476))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.54/7.29  tff(c_22950, plain, (![B_485, A_486]: (k1_setfam_1(k2_tarski(B_485, A_486))=k3_xboole_0(A_486, B_485))), inference(superposition, [status(thm), theory('equality')], [c_26, c_22904])).
% 14.54/7.29  tff(c_22956, plain, (![B_485, A_486]: (k3_xboole_0(B_485, A_486)=k3_xboole_0(A_486, B_485))), inference(superposition, [status(thm), theory('equality')], [c_22950, c_40])).
% 14.54/7.29  tff(c_26207, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26054, c_12])).
% 14.54/7.29  tff(c_23358, plain, (![A_510, B_511, C_512]: (r1_tarski(k4_xboole_0(A_510, B_511), C_512) | ~r1_tarski(A_510, k2_xboole_0(B_511, C_512)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.54/7.29  tff(c_23063, plain, (![A_490, B_491]: (k5_xboole_0(A_490, k3_xboole_0(A_490, B_491))=k4_xboole_0(A_490, B_491))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.54/7.29  tff(c_23081, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_23063])).
% 14.54/7.29  tff(c_23084, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_23081])).
% 14.54/7.29  tff(c_22973, plain, (![B_487, A_488]: (k3_xboole_0(B_487, A_488)=k3_xboole_0(A_488, B_487))), inference(superposition, [status(thm), theory('equality')], [c_22950, c_40])).
% 14.54/7.29  tff(c_22995, plain, (![A_488]: (k3_xboole_0(k1_xboole_0, A_488)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22973, c_10])).
% 14.54/7.29  tff(c_23072, plain, (![A_488]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_488))), inference(superposition, [status(thm), theory('equality')], [c_22995, c_23063])).
% 14.54/7.29  tff(c_23138, plain, (![A_495]: (k4_xboole_0(k1_xboole_0, A_495)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_23084, c_23072])).
% 14.54/7.29  tff(c_23143, plain, (![A_495]: (k1_xboole_0=A_495 | ~r1_tarski(A_495, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_23138, c_14])).
% 14.54/7.29  tff(c_23365, plain, (![A_510, B_511]: (k4_xboole_0(A_510, B_511)=k1_xboole_0 | ~r1_tarski(A_510, k2_xboole_0(B_511, k1_xboole_0)))), inference(resolution, [status(thm)], [c_23358, c_23143])).
% 14.54/7.29  tff(c_23381, plain, (![A_510, B_511]: (k4_xboole_0(A_510, B_511)=k1_xboole_0 | ~r1_tarski(A_510, B_511))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_23365])).
% 14.54/7.29  tff(c_26217, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26207, c_23381])).
% 14.54/7.29  tff(c_26240, plain, (k2_xboole_0(k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2'), k1_xboole_0)=k1_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26217, c_22])).
% 14.54/7.29  tff(c_26256, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_22956, c_26240])).
% 14.54/7.29  tff(c_23162, plain, (![A_496, B_497]: (k2_xboole_0(k3_xboole_0(A_496, B_497), k4_xboole_0(A_496, B_497))=A_496)), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.54/7.29  tff(c_24, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.54/7.29  tff(c_23168, plain, (![A_496, B_497]: (r1_tarski(k3_xboole_0(A_496, B_497), A_496))), inference(superposition, [status(thm), theory('equality')], [c_23162, c_24])).
% 14.54/7.29  tff(c_23524, plain, (![A_520, B_521]: (k4_xboole_0(A_520, B_521)=k1_xboole_0 | ~r1_tarski(A_520, B_521))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_23365])).
% 14.54/7.29  tff(c_23749, plain, (![A_529, B_530]: (k4_xboole_0(k3_xboole_0(A_529, B_530), A_529)=k1_xboole_0)), inference(resolution, [status(thm)], [c_23168, c_23524])).
% 14.54/7.29  tff(c_23760, plain, (![A_529, B_530]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_529, B_530), A_529), k1_xboole_0)=k3_xboole_0(A_529, B_530))), inference(superposition, [status(thm), theory('equality')], [c_23749, c_22])).
% 14.54/7.29  tff(c_34217, plain, (![A_750, B_751]: (k3_xboole_0(A_750, k3_xboole_0(A_750, B_751))=k3_xboole_0(A_750, B_751))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_22956, c_23760])).
% 14.54/7.29  tff(c_34343, plain, (![A_750, B_751]: (k5_xboole_0(A_750, k3_xboole_0(A_750, B_751))=k4_xboole_0(A_750, k3_xboole_0(A_750, B_751)))), inference(superposition, [status(thm), theory('equality')], [c_34217, c_2])).
% 14.54/7.29  tff(c_34438, plain, (![A_750, B_751]: (k4_xboole_0(A_750, k3_xboole_0(A_750, B_751))=k4_xboole_0(A_750, B_751))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34343])).
% 14.54/7.29  tff(c_27349, plain, (![A_496, B_497]: (k4_xboole_0(A_496, k3_xboole_0(A_496, B_497))=k3_subset_1(A_496, k3_xboole_0(A_496, B_497)))), inference(resolution, [status(thm)], [c_23168, c_27140])).
% 14.54/7.29  tff(c_57473, plain, (![A_946, B_947]: (k3_subset_1(A_946, k3_xboole_0(A_946, B_947))=k4_xboole_0(A_946, B_947))), inference(demodulation, [status(thm), theory('equality')], [c_34438, c_27349])).
% 14.54/7.29  tff(c_57585, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26256, c_57473])).
% 14.54/7.29  tff(c_57665, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27934, c_57585])).
% 14.54/7.29  tff(c_57667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24481, c_57665])).
% 14.54/7.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.54/7.29  
% 14.54/7.29  Inference rules
% 14.54/7.29  ----------------------
% 14.54/7.29  #Ref     : 0
% 14.54/7.29  #Sup     : 14187
% 14.54/7.29  #Fact    : 0
% 14.54/7.29  #Define  : 0
% 14.54/7.29  #Split   : 5
% 14.54/7.29  #Chain   : 0
% 14.54/7.29  #Close   : 0
% 14.54/7.29  
% 14.54/7.29  Ordering : KBO
% 14.54/7.29  
% 14.54/7.29  Simplification rules
% 14.54/7.29  ----------------------
% 14.54/7.29  #Subsume      : 666
% 14.54/7.29  #Demod        : 12975
% 14.54/7.29  #Tautology    : 10383
% 14.54/7.29  #SimpNegUnit  : 3
% 14.54/7.29  #BackRed      : 31
% 14.54/7.29  
% 14.54/7.29  #Partial instantiations: 0
% 14.54/7.29  #Strategies tried      : 1
% 14.54/7.29  
% 14.54/7.29  Timing (in seconds)
% 14.54/7.29  ----------------------
% 14.54/7.29  Preprocessing        : 0.37
% 14.54/7.29  Parsing              : 0.21
% 14.54/7.29  CNF conversion       : 0.02
% 14.54/7.29  Main loop            : 6.06
% 14.54/7.29  Inferencing          : 1.05
% 14.54/7.29  Reduction            : 3.40
% 14.54/7.29  Demodulation         : 2.94
% 14.54/7.29  BG Simplification    : 0.10
% 14.54/7.29  Subsumption          : 1.20
% 14.54/7.29  Abstraction          : 0.17
% 14.54/7.29  MUC search           : 0.00
% 14.54/7.29  Cooper               : 0.00
% 14.54/7.29  Total                : 6.48
% 14.54/7.29  Index Insertion      : 0.00
% 14.54/7.29  Index Deletion       : 0.00
% 14.54/7.29  Index Matching       : 0.00
% 14.54/7.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

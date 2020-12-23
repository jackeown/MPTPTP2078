%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:19 EST 2020

% Result     : Theorem 8.60s
% Output     : CNFRefutation 8.71s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 292 expanded)
%              Number of leaves         :   47 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  188 ( 511 expanded)
%              Number of equality atoms :   95 ( 193 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_96,axiom,(
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

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_12626,plain,(
    ! [A_421,B_422,C_423] :
      ( k7_subset_1(A_421,B_422,C_423) = k4_xboole_0(B_422,C_423)
      | ~ m1_subset_1(B_422,k1_zfmisc_1(A_421)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12635,plain,(
    ! [C_423] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_423) = k4_xboole_0('#skF_2',C_423) ),
    inference(resolution,[status(thm)],[c_54,c_12626])).

tff(c_66,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_111,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_219,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3606,plain,(
    ! [B_208,A_209] :
      ( v4_pre_topc(B_208,A_209)
      | k2_pre_topc(A_209,B_208) != B_208
      | ~ v2_pre_topc(A_209)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3620,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_3606])).

tff(c_3626,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_3620])).

tff(c_3627,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_3626])).

tff(c_3910,plain,(
    ! [A_219,B_220] :
      ( k4_subset_1(u1_struct_0(A_219),B_220,k2_tops_1(A_219,B_220)) = k2_pre_topc(A_219,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3920,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_3910])).

tff(c_3926,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3920])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k2_xboole_0(A_61,B_62)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_86])).

tff(c_454,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k4_xboole_0(B_92,A_91)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_469,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_454])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_61] : r1_tarski(k1_xboole_0,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_12])).

tff(c_150,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [A_61] : k3_xboole_0(k1_xboole_0,A_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_150])).

tff(c_551,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_580,plain,(
    ! [A_61] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_551])).

tff(c_623,plain,(
    ! [A_99] : k4_xboole_0(k1_xboole_0,A_99) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_469,c_580])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_631,plain,(
    ! [A_99] : k5_xboole_0(A_99,k1_xboole_0) = k2_xboole_0(A_99,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_18])).

tff(c_673,plain,(
    ! [A_99] : k5_xboole_0(A_99,k1_xboole_0) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_631])).

tff(c_1771,plain,(
    ! [A_142,B_143,C_144] :
      ( k7_subset_1(A_142,B_143,C_144) = k4_xboole_0(B_143,C_144)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1868,plain,(
    ! [C_147] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_147) = k4_xboole_0('#skF_2',C_147) ),
    inference(resolution,[status(thm)],[c_54,c_1771])).

tff(c_1874,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1868,c_111])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_583,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_551])).

tff(c_590,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_583])).

tff(c_1305,plain,(
    ! [A_130,B_131] : k3_xboole_0(k4_xboole_0(A_130,B_131),A_130) = k4_xboole_0(A_130,B_131) ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1311,plain,(
    ! [A_130,B_131] : k5_xboole_0(k4_xboole_0(A_130,B_131),k4_xboole_0(A_130,B_131)) = k4_xboole_0(k4_xboole_0(A_130,B_131),A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_4])).

tff(c_1368,plain,(
    ! [A_130,B_131] : k4_xboole_0(k4_xboole_0(A_130,B_131),A_130) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_1311])).

tff(c_2285,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1874,c_1368])).

tff(c_2334,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2285,c_18])).

tff(c_2349,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_2334])).

tff(c_145,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_149,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_145])).

tff(c_160,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_149,c_150])).

tff(c_20,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_189,plain,(
    ! [A_74,B_75] : k1_setfam_1(k2_tarski(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_220,plain,(
    ! [A_78,B_79] : k1_setfam_1(k2_tarski(A_78,B_79)) = k3_xboole_0(B_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_189])).

tff(c_34,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_226,plain,(
    ! [B_79,A_78] : k3_xboole_0(B_79,A_78) = k3_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_34])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_720,plain,(
    ! [A_101,C_102,B_103] :
      ( r1_tarski(A_101,C_102)
      | ~ r1_tarski(B_103,C_102)
      | ~ r1_tarski(A_101,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1930,plain,(
    ! [A_148,A_149,B_150] :
      ( r1_tarski(A_148,A_149)
      | ~ r1_tarski(A_148,k4_xboole_0(A_149,B_150)) ) ),
    inference(resolution,[status(thm)],[c_12,c_720])).

tff(c_2097,plain,(
    ! [A_156,B_157,B_158] : r1_tarski(k4_xboole_0(k4_xboole_0(A_156,B_157),B_158),A_156) ),
    inference(resolution,[status(thm)],[c_12,c_1930])).

tff(c_2482,plain,(
    ! [A_167,B_168,B_169] : r1_tarski(k4_xboole_0(k3_xboole_0(A_167,B_168),B_169),A_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2097])).

tff(c_2709,plain,(
    ! [A_175,B_176,B_177] : r1_tarski(k4_xboole_0(k3_xboole_0(A_175,B_176),B_177),B_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_2482])).

tff(c_2789,plain,(
    ! [B_178] : r1_tarski(k4_xboole_0('#skF_2',B_178),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_2709])).

tff(c_2796,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1874,c_2789])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3044,plain,(
    ! [A_186,B_187,C_188] :
      ( k4_subset_1(A_186,B_187,C_188) = k2_xboole_0(B_187,C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(A_186))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(A_186)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10505,plain,(
    ! [B_314,B_315,A_316] :
      ( k4_subset_1(B_314,B_315,A_316) = k2_xboole_0(B_315,A_316)
      | ~ m1_subset_1(B_315,k1_zfmisc_1(B_314))
      | ~ r1_tarski(A_316,B_314) ) ),
    inference(resolution,[status(thm)],[c_38,c_3044])).

tff(c_10522,plain,(
    ! [A_317] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_317) = k2_xboole_0('#skF_2',A_317)
      | ~ r1_tarski(A_317,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_54,c_10505])).

tff(c_10560,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2796,c_10522])).

tff(c_10639,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3926,c_2349,c_10560])).

tff(c_10641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3627,c_10639])).

tff(c_10642,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_11021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_10642])).

tff(c_11022,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_11117,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_60])).

tff(c_12775,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12635,c_11117])).

tff(c_13400,plain,(
    ! [A_459,B_460] :
      ( r1_tarski(k2_tops_1(A_459,B_460),B_460)
      | ~ v4_pre_topc(B_460,A_459)
      | ~ m1_subset_1(B_460,k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ l1_pre_topc(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_13410,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_13400])).

tff(c_13416,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11022,c_13410])).

tff(c_14190,plain,(
    ! [A_490,B_491] :
      ( k7_subset_1(u1_struct_0(A_490),B_491,k2_tops_1(A_490,B_491)) = k1_tops_1(A_490,B_491)
      | ~ m1_subset_1(B_491,k1_zfmisc_1(u1_struct_0(A_490)))
      | ~ l1_pre_topc(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14200,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_14190])).

tff(c_14206,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12635,c_14200])).

tff(c_12235,plain,(
    ! [A_404,B_405] :
      ( k4_xboole_0(A_404,B_405) = k3_subset_1(A_404,B_405)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(A_404)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_15828,plain,(
    ! [B_517,A_518] :
      ( k4_xboole_0(B_517,A_518) = k3_subset_1(B_517,A_518)
      | ~ r1_tarski(A_518,B_517) ) ),
    inference(resolution,[status(thm)],[c_38,c_12235])).

tff(c_15876,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_13416,c_15828])).

tff(c_15983,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14206,c_15876])).

tff(c_12003,plain,(
    ! [A_394,B_395] :
      ( k3_subset_1(A_394,k3_subset_1(A_394,B_395)) = B_395
      | ~ m1_subset_1(B_395,k1_zfmisc_1(A_394)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12011,plain,(
    ! [B_38,A_37] :
      ( k3_subset_1(B_38,k3_subset_1(B_38,A_37)) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_38,c_12003])).

tff(c_16191,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15983,c_12011])).

tff(c_16201,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13416,c_16191])).

tff(c_11101,plain,(
    ! [A_345,B_346] : k1_setfam_1(k2_tarski(A_345,B_346)) = k3_xboole_0(A_345,B_346) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11133,plain,(
    ! [A_349,B_350] : k1_setfam_1(k2_tarski(A_349,B_350)) = k3_xboole_0(B_350,A_349) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_11101])).

tff(c_11139,plain,(
    ! [B_350,A_349] : k3_xboole_0(B_350,A_349) = k3_xboole_0(A_349,B_350) ),
    inference(superposition,[status(thm),theory(equality)],[c_11133,c_34])).

tff(c_11062,plain,(
    ! [A_340,B_341] :
      ( k3_xboole_0(A_340,B_341) = A_340
      | ~ r1_tarski(A_340,B_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11074,plain,(
    ! [A_11,B_12] : k3_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k4_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_12,c_11062])).

tff(c_14366,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14206,c_11074])).

tff(c_14398,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14206,c_11139,c_14366])).

tff(c_15966,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_12,c_15828])).

tff(c_16105,plain,(
    ! [A_522,B_523] : k3_subset_1(A_522,k4_xboole_0(A_522,B_523)) = k3_xboole_0(A_522,B_523) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_15966])).

tff(c_16111,plain,(
    ! [A_522,B_523] :
      ( k3_subset_1(A_522,k3_xboole_0(A_522,B_523)) = k4_xboole_0(A_522,B_523)
      | ~ r1_tarski(k4_xboole_0(A_522,B_523),A_522) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16105,c_12011])).

tff(c_20505,plain,(
    ! [A_578,B_579] : k3_subset_1(A_578,k3_xboole_0(A_578,B_579)) = k4_xboole_0(A_578,B_579) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16111])).

tff(c_20547,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14398,c_20505])).

tff(c_20603,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16201,c_20547])).

tff(c_20605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12775,c_20603])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.60/3.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.60/3.47  
% 8.60/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.47  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.71/3.47  
% 8.71/3.47  %Foreground sorts:
% 8.71/3.47  
% 8.71/3.47  
% 8.71/3.47  %Background operators:
% 8.71/3.47  
% 8.71/3.47  
% 8.71/3.47  %Foreground operators:
% 8.71/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.71/3.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.71/3.47  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.71/3.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.71/3.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.71/3.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.71/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.71/3.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.71/3.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.71/3.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.71/3.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.71/3.47  tff('#skF_2', type, '#skF_2': $i).
% 8.71/3.47  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.71/3.47  tff('#skF_1', type, '#skF_1': $i).
% 8.71/3.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.71/3.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.71/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.71/3.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.71/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.71/3.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.71/3.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.71/3.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.71/3.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.71/3.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.71/3.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.71/3.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.71/3.47  
% 8.71/3.50  tff(f_144, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 8.71/3.50  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.71/3.50  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.71/3.50  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 8.71/3.50  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.71/3.50  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.71/3.50  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.71/3.50  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.71/3.50  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.71/3.50  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.71/3.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.71/3.50  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.71/3.50  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.71/3.50  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.71/3.50  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.71/3.50  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.71/3.50  tff(f_71, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.71/3.50  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 8.71/3.50  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 8.71/3.50  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.71/3.50  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.71/3.50  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.71/3.50  tff(c_12626, plain, (![A_421, B_422, C_423]: (k7_subset_1(A_421, B_422, C_423)=k4_xboole_0(B_422, C_423) | ~m1_subset_1(B_422, k1_zfmisc_1(A_421)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.71/3.50  tff(c_12635, plain, (![C_423]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_423)=k4_xboole_0('#skF_2', C_423))), inference(resolution, [status(thm)], [c_54, c_12626])).
% 8.71/3.50  tff(c_66, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.71/3.50  tff(c_111, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_66])).
% 8.71/3.50  tff(c_60, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.71/3.50  tff(c_219, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_60])).
% 8.71/3.50  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.71/3.50  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.71/3.50  tff(c_3606, plain, (![B_208, A_209]: (v4_pre_topc(B_208, A_209) | k2_pre_topc(A_209, B_208)!=B_208 | ~v2_pre_topc(A_209) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.71/3.50  tff(c_3620, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_3606])).
% 8.71/3.50  tff(c_3626, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_3620])).
% 8.71/3.50  tff(c_3627, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_219, c_3626])).
% 8.71/3.50  tff(c_3910, plain, (![A_219, B_220]: (k4_subset_1(u1_struct_0(A_219), B_220, k2_tops_1(A_219, B_220))=k2_pre_topc(A_219, B_220) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.71/3.50  tff(c_3920, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_3910])).
% 8.71/3.50  tff(c_3926, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3920])).
% 8.71/3.50  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.71/3.50  tff(c_86, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k2_xboole_0(A_61, B_62))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.71/3.50  tff(c_96, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_86])).
% 8.71/3.50  tff(c_454, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k4_xboole_0(B_92, A_91))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.71/3.50  tff(c_469, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_96, c_454])).
% 8.71/3.50  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.71/3.50  tff(c_91, plain, (![A_61]: (r1_tarski(k1_xboole_0, A_61))), inference(superposition, [status(thm), theory('equality')], [c_86, c_12])).
% 8.71/3.50  tff(c_150, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.71/3.50  tff(c_161, plain, (![A_61]: (k3_xboole_0(k1_xboole_0, A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_150])).
% 8.71/3.50  tff(c_551, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.71/3.50  tff(c_580, plain, (![A_61]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_61))), inference(superposition, [status(thm), theory('equality')], [c_161, c_551])).
% 8.71/3.50  tff(c_623, plain, (![A_99]: (k4_xboole_0(k1_xboole_0, A_99)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_469, c_580])).
% 8.71/3.50  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.71/3.50  tff(c_631, plain, (![A_99]: (k5_xboole_0(A_99, k1_xboole_0)=k2_xboole_0(A_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_623, c_18])).
% 8.71/3.50  tff(c_673, plain, (![A_99]: (k5_xboole_0(A_99, k1_xboole_0)=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_631])).
% 8.71/3.50  tff(c_1771, plain, (![A_142, B_143, C_144]: (k7_subset_1(A_142, B_143, C_144)=k4_xboole_0(B_143, C_144) | ~m1_subset_1(B_143, k1_zfmisc_1(A_142)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.71/3.50  tff(c_1868, plain, (![C_147]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_147)=k4_xboole_0('#skF_2', C_147))), inference(resolution, [status(thm)], [c_54, c_1771])).
% 8.71/3.50  tff(c_1874, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1868, c_111])).
% 8.71/3.50  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.71/3.50  tff(c_583, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_551])).
% 8.71/3.50  tff(c_590, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_583])).
% 8.71/3.50  tff(c_1305, plain, (![A_130, B_131]: (k3_xboole_0(k4_xboole_0(A_130, B_131), A_130)=k4_xboole_0(A_130, B_131))), inference(resolution, [status(thm)], [c_12, c_150])).
% 8.71/3.50  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.71/3.50  tff(c_1311, plain, (![A_130, B_131]: (k5_xboole_0(k4_xboole_0(A_130, B_131), k4_xboole_0(A_130, B_131))=k4_xboole_0(k4_xboole_0(A_130, B_131), A_130))), inference(superposition, [status(thm), theory('equality')], [c_1305, c_4])).
% 8.71/3.50  tff(c_1368, plain, (![A_130, B_131]: (k4_xboole_0(k4_xboole_0(A_130, B_131), A_130)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_590, c_1311])).
% 8.71/3.50  tff(c_2285, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1874, c_1368])).
% 8.71/3.50  tff(c_2334, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2285, c_18])).
% 8.71/3.50  tff(c_2349, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_673, c_2334])).
% 8.71/3.50  tff(c_145, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.71/3.50  tff(c_149, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_145])).
% 8.71/3.50  tff(c_160, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_149, c_150])).
% 8.71/3.50  tff(c_20, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.71/3.50  tff(c_189, plain, (![A_74, B_75]: (k1_setfam_1(k2_tarski(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.71/3.50  tff(c_220, plain, (![A_78, B_79]: (k1_setfam_1(k2_tarski(A_78, B_79))=k3_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_20, c_189])).
% 8.71/3.50  tff(c_34, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.71/3.50  tff(c_226, plain, (![B_79, A_78]: (k3_xboole_0(B_79, A_78)=k3_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_220, c_34])).
% 8.71/3.50  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.71/3.50  tff(c_720, plain, (![A_101, C_102, B_103]: (r1_tarski(A_101, C_102) | ~r1_tarski(B_103, C_102) | ~r1_tarski(A_101, B_103))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.71/3.50  tff(c_1930, plain, (![A_148, A_149, B_150]: (r1_tarski(A_148, A_149) | ~r1_tarski(A_148, k4_xboole_0(A_149, B_150)))), inference(resolution, [status(thm)], [c_12, c_720])).
% 8.71/3.50  tff(c_2097, plain, (![A_156, B_157, B_158]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_156, B_157), B_158), A_156))), inference(resolution, [status(thm)], [c_12, c_1930])).
% 8.71/3.50  tff(c_2482, plain, (![A_167, B_168, B_169]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_167, B_168), B_169), A_167))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2097])).
% 8.71/3.50  tff(c_2709, plain, (![A_175, B_176, B_177]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_175, B_176), B_177), B_176))), inference(superposition, [status(thm), theory('equality')], [c_226, c_2482])).
% 8.71/3.50  tff(c_2789, plain, (![B_178]: (r1_tarski(k4_xboole_0('#skF_2', B_178), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_160, c_2709])).
% 8.71/3.50  tff(c_2796, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1874, c_2789])).
% 8.71/3.50  tff(c_38, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.71/3.50  tff(c_3044, plain, (![A_186, B_187, C_188]: (k4_subset_1(A_186, B_187, C_188)=k2_xboole_0(B_187, C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(A_186)) | ~m1_subset_1(B_187, k1_zfmisc_1(A_186)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.71/3.50  tff(c_10505, plain, (![B_314, B_315, A_316]: (k4_subset_1(B_314, B_315, A_316)=k2_xboole_0(B_315, A_316) | ~m1_subset_1(B_315, k1_zfmisc_1(B_314)) | ~r1_tarski(A_316, B_314))), inference(resolution, [status(thm)], [c_38, c_3044])).
% 8.71/3.50  tff(c_10522, plain, (![A_317]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_317)=k2_xboole_0('#skF_2', A_317) | ~r1_tarski(A_317, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_10505])).
% 8.71/3.50  tff(c_10560, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2796, c_10522])).
% 8.71/3.50  tff(c_10639, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3926, c_2349, c_10560])).
% 8.71/3.50  tff(c_10641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3627, c_10639])).
% 8.71/3.50  tff(c_10642, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 8.71/3.50  tff(c_11021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_10642])).
% 8.71/3.50  tff(c_11022, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 8.71/3.50  tff(c_11117, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_60])).
% 8.71/3.50  tff(c_12775, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12635, c_11117])).
% 8.71/3.50  tff(c_13400, plain, (![A_459, B_460]: (r1_tarski(k2_tops_1(A_459, B_460), B_460) | ~v4_pre_topc(B_460, A_459) | ~m1_subset_1(B_460, k1_zfmisc_1(u1_struct_0(A_459))) | ~l1_pre_topc(A_459))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.71/3.50  tff(c_13410, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_13400])).
% 8.71/3.50  tff(c_13416, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_11022, c_13410])).
% 8.71/3.50  tff(c_14190, plain, (![A_490, B_491]: (k7_subset_1(u1_struct_0(A_490), B_491, k2_tops_1(A_490, B_491))=k1_tops_1(A_490, B_491) | ~m1_subset_1(B_491, k1_zfmisc_1(u1_struct_0(A_490))) | ~l1_pre_topc(A_490))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.71/3.50  tff(c_14200, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_14190])).
% 8.71/3.50  tff(c_14206, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12635, c_14200])).
% 8.71/3.50  tff(c_12235, plain, (![A_404, B_405]: (k4_xboole_0(A_404, B_405)=k3_subset_1(A_404, B_405) | ~m1_subset_1(B_405, k1_zfmisc_1(A_404)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.71/3.50  tff(c_15828, plain, (![B_517, A_518]: (k4_xboole_0(B_517, A_518)=k3_subset_1(B_517, A_518) | ~r1_tarski(A_518, B_517))), inference(resolution, [status(thm)], [c_38, c_12235])).
% 8.71/3.50  tff(c_15876, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_13416, c_15828])).
% 8.71/3.50  tff(c_15983, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14206, c_15876])).
% 8.71/3.50  tff(c_12003, plain, (![A_394, B_395]: (k3_subset_1(A_394, k3_subset_1(A_394, B_395))=B_395 | ~m1_subset_1(B_395, k1_zfmisc_1(A_394)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.71/3.50  tff(c_12011, plain, (![B_38, A_37]: (k3_subset_1(B_38, k3_subset_1(B_38, A_37))=A_37 | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_38, c_12003])).
% 8.71/3.50  tff(c_16191, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15983, c_12011])).
% 8.71/3.50  tff(c_16201, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13416, c_16191])).
% 8.71/3.50  tff(c_11101, plain, (![A_345, B_346]: (k1_setfam_1(k2_tarski(A_345, B_346))=k3_xboole_0(A_345, B_346))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.71/3.50  tff(c_11133, plain, (![A_349, B_350]: (k1_setfam_1(k2_tarski(A_349, B_350))=k3_xboole_0(B_350, A_349))), inference(superposition, [status(thm), theory('equality')], [c_20, c_11101])).
% 8.71/3.50  tff(c_11139, plain, (![B_350, A_349]: (k3_xboole_0(B_350, A_349)=k3_xboole_0(A_349, B_350))), inference(superposition, [status(thm), theory('equality')], [c_11133, c_34])).
% 8.71/3.50  tff(c_11062, plain, (![A_340, B_341]: (k3_xboole_0(A_340, B_341)=A_340 | ~r1_tarski(A_340, B_341))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.71/3.50  tff(c_11074, plain, (![A_11, B_12]: (k3_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k4_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_12, c_11062])).
% 8.71/3.50  tff(c_14366, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14206, c_11074])).
% 8.71/3.50  tff(c_14398, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14206, c_11139, c_14366])).
% 8.71/3.50  tff(c_15966, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_subset_1(A_11, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_12, c_15828])).
% 8.71/3.50  tff(c_16105, plain, (![A_522, B_523]: (k3_subset_1(A_522, k4_xboole_0(A_522, B_523))=k3_xboole_0(A_522, B_523))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_15966])).
% 8.71/3.50  tff(c_16111, plain, (![A_522, B_523]: (k3_subset_1(A_522, k3_xboole_0(A_522, B_523))=k4_xboole_0(A_522, B_523) | ~r1_tarski(k4_xboole_0(A_522, B_523), A_522))), inference(superposition, [status(thm), theory('equality')], [c_16105, c_12011])).
% 8.71/3.50  tff(c_20505, plain, (![A_578, B_579]: (k3_subset_1(A_578, k3_xboole_0(A_578, B_579))=k4_xboole_0(A_578, B_579))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16111])).
% 8.71/3.50  tff(c_20547, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14398, c_20505])).
% 8.71/3.50  tff(c_20603, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16201, c_20547])).
% 8.71/3.50  tff(c_20605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12775, c_20603])).
% 8.71/3.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.50  
% 8.71/3.50  Inference rules
% 8.71/3.50  ----------------------
% 8.71/3.50  #Ref     : 0
% 8.71/3.50  #Sup     : 4999
% 8.71/3.50  #Fact    : 0
% 8.71/3.50  #Define  : 0
% 8.71/3.50  #Split   : 2
% 8.71/3.50  #Chain   : 0
% 8.71/3.50  #Close   : 0
% 8.71/3.50  
% 8.71/3.50  Ordering : KBO
% 8.71/3.50  
% 8.71/3.50  Simplification rules
% 8.71/3.50  ----------------------
% 8.71/3.50  #Subsume      : 116
% 8.71/3.50  #Demod        : 4055
% 8.71/3.50  #Tautology    : 3503
% 8.71/3.50  #SimpNegUnit  : 4
% 8.71/3.50  #BackRed      : 8
% 8.71/3.50  
% 8.71/3.50  #Partial instantiations: 0
% 8.71/3.50  #Strategies tried      : 1
% 8.71/3.50  
% 8.71/3.50  Timing (in seconds)
% 8.71/3.50  ----------------------
% 8.71/3.50  Preprocessing        : 0.36
% 8.71/3.50  Parsing              : 0.20
% 8.71/3.50  CNF conversion       : 0.02
% 8.71/3.50  Main loop            : 2.33
% 8.71/3.50  Inferencing          : 0.55
% 8.71/3.50  Reduction            : 1.18
% 8.71/3.50  Demodulation         : 0.98
% 8.71/3.50  BG Simplification    : 0.06
% 8.71/3.50  Subsumption          : 0.39
% 8.71/3.50  Abstraction          : 0.09
% 8.71/3.50  MUC search           : 0.00
% 8.71/3.50  Cooper               : 0.00
% 8.71/3.50  Total                : 2.76
% 8.71/3.50  Index Insertion      : 0.00
% 8.71/3.50  Index Deletion       : 0.00
% 8.71/3.50  Index Matching       : 0.00
% 8.71/3.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

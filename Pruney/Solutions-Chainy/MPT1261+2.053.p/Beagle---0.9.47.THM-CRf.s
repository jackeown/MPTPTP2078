%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:19 EST 2020

% Result     : Theorem 10.72s
% Output     : CNFRefutation 10.96s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 439 expanded)
%              Number of leaves         :   47 ( 164 expanded)
%              Depth                    :   17
%              Number of atoms          :  232 ( 677 expanded)
%              Number of equality atoms :  100 ( 292 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_14190,plain,(
    ! [A_464,B_465,C_466] :
      ( k7_subset_1(A_464,B_465,C_466) = k4_xboole_0(B_465,C_466)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(A_464)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14199,plain,(
    ! [C_466] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_466) = k4_xboole_0('#skF_2',C_466) ),
    inference(resolution,[status(thm)],[c_54,c_14190])).

tff(c_60,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_287,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1987,plain,(
    ! [A_173,B_174,C_175] :
      ( k7_subset_1(A_173,B_174,C_175) = k4_xboole_0(B_174,C_175)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2078,plain,(
    ! [C_177] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_177) = k4_xboole_0('#skF_2',C_177) ),
    inference(resolution,[status(thm)],[c_54,c_1987])).

tff(c_66,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_127,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_2084,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2078,c_127])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2503,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_8])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(k4_xboole_0(A_13,B_14),C_15)
      | ~ r1_tarski(A_13,k2_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [B_24,A_23] : k2_tarski(B_24,A_23) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_111,plain,(
    ! [A_67,B_68] : k1_setfam_1(k2_tarski(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_152,plain,(
    ! [B_75,A_76] : k1_setfam_1(k2_tarski(B_75,A_76)) = k3_xboole_0(A_76,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_111])).

tff(c_36,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_158,plain,(
    ! [B_75,A_76] : k3_xboole_0(B_75,A_76) = k3_xboole_0(A_76,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_36])).

tff(c_465,plain,(
    ! [A_92,B_93] : k4_xboole_0(A_92,k4_xboole_0(A_92,B_93)) = k3_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_496,plain,(
    ! [A_94,B_95] : r1_tarski(k3_xboole_0(A_94,B_95),A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_8])).

tff(c_502,plain,(
    ! [B_75,A_76] : r1_tarski(k3_xboole_0(B_75,A_76),A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_496])).

tff(c_1208,plain,(
    ! [A_151,B_152,C_153] :
      ( r1_tarski(A_151,k2_xboole_0(B_152,C_153))
      | ~ r1_tarski(k4_xboole_0(A_151,B_152),C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1250,plain,(
    ! [A_154,B_155] : r1_tarski(A_154,k2_xboole_0(B_155,A_154)) ),
    inference(resolution,[status(thm)],[c_8,c_1208])).

tff(c_1302,plain,(
    ! [A_156] : r1_tarski(k1_xboole_0,A_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1250])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1430,plain,(
    ! [A_161,A_162] :
      ( r1_tarski(A_161,A_162)
      | ~ r1_tarski(A_161,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1302,c_6])).

tff(c_1494,plain,(
    ! [B_163,A_164] : r1_tarski(k3_xboole_0(B_163,k1_xboole_0),A_164) ),
    inference(resolution,[status(thm)],[c_502,c_1430])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1537,plain,(
    ! [B_163] : k3_xboole_0(B_163,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1494,c_10])).

tff(c_137,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_217,plain,(
    ! [B_81,A_82] : k3_tarski(k2_tarski(B_81,A_82)) = k2_xboole_0(A_82,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_137])).

tff(c_24,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_240,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,A_84) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_24])).

tff(c_278,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_240])).

tff(c_288,plain,(
    ! [A_85] : k2_xboole_0(k1_xboole_0,A_85) = A_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_240])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_301,plain,(
    ! [B_12] : k4_xboole_0(B_12,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_12])).

tff(c_328,plain,(
    ! [B_12] : k4_xboole_0(B_12,k1_xboole_0) = B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_301])).

tff(c_544,plain,(
    ! [B_100] : k4_xboole_0(B_100,B_100) = k3_xboole_0(B_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_465])).

tff(c_563,plain,(
    ! [B_100] :
      ( k1_xboole_0 = B_100
      | ~ r1_tarski(B_100,k3_xboole_0(B_100,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_10])).

tff(c_2097,plain,(
    ! [B_178] :
      ( k1_xboole_0 = B_178
      | ~ r1_tarski(B_178,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1537,c_563])).

tff(c_2141,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,k2_xboole_0(B_14,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2097])).

tff(c_4307,plain,(
    ! [A_264,B_265] :
      ( k4_xboole_0(A_264,B_265) = k1_xboole_0
      | ~ r1_tarski(A_264,B_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2141])).

tff(c_4488,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2503,c_4307])).

tff(c_5540,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4488,c_12])).

tff(c_5563,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_5540])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2910,plain,(
    ! [A_215,B_216] :
      ( k4_subset_1(u1_struct_0(A_215),B_216,k2_tops_1(A_215,B_216)) = k2_pre_topc(A_215,B_216)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2920,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_2910])).

tff(c_2926,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2920])).

tff(c_353,plain,(
    ! [B_88] : k4_xboole_0(B_88,k1_xboole_0) = B_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_301])).

tff(c_368,plain,(
    ! [B_88] : r1_tarski(B_88,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_8])).

tff(c_128,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_136,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_128])).

tff(c_667,plain,(
    ! [A_103,C_104,B_105] :
      ( r1_tarski(A_103,C_104)
      | ~ r1_tarski(B_105,C_104)
      | ~ r1_tarski(A_103,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_686,plain,(
    ! [A_106] :
      ( r1_tarski(A_106,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_106,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_136,c_667])).

tff(c_689,plain,(
    ! [A_4,A_106] :
      ( r1_tarski(A_4,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_4,A_106)
      | ~ r1_tarski(A_106,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_686,c_6])).

tff(c_2509,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2503,c_689])).

tff(c_2514,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_2509])).

tff(c_40,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2625,plain,(
    ! [A_199,B_200,C_201] :
      ( k4_subset_1(A_199,B_200,C_201) = k2_xboole_0(B_200,C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(A_199))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11904,plain,(
    ! [B_364,B_365,A_366] :
      ( k4_subset_1(B_364,B_365,A_366) = k2_xboole_0(B_365,A_366)
      | ~ m1_subset_1(B_365,k1_zfmisc_1(B_364))
      | ~ r1_tarski(A_366,B_364) ) ),
    inference(resolution,[status(thm)],[c_40,c_2625])).

tff(c_12219,plain,(
    ! [A_373] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_373) = k2_xboole_0('#skF_2',A_373)
      | ~ r1_tarski(A_373,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_54,c_11904])).

tff(c_12275,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2514,c_12219])).

tff(c_12372,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5563,c_2926,c_12275])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2215,plain,(
    ! [A_181,B_182] :
      ( v4_pre_topc(k2_pre_topc(A_181,B_182),A_181)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2225,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_2215])).

tff(c_2231,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2225])).

tff(c_12397,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12372,c_2231])).

tff(c_12399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_12397])).

tff(c_12400,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_12600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12400,c_127])).

tff(c_12601,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_12716,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12601,c_60])).

tff(c_14441,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14199,c_12716])).

tff(c_15586,plain,(
    ! [A_503,B_504] :
      ( r1_tarski(k2_tops_1(A_503,B_504),B_504)
      | ~ v4_pre_topc(B_504,A_503)
      | ~ m1_subset_1(B_504,k1_zfmisc_1(u1_struct_0(A_503)))
      | ~ l1_pre_topc(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_15596,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_15586])).

tff(c_15602,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12601,c_15596])).

tff(c_16492,plain,(
    ! [A_526,B_527] :
      ( k7_subset_1(u1_struct_0(A_526),B_527,k2_tops_1(A_526,B_527)) = k1_tops_1(A_526,B_527)
      | ~ m1_subset_1(B_527,k1_zfmisc_1(u1_struct_0(A_526)))
      | ~ l1_pre_topc(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_16502,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_16492])).

tff(c_16508,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14199,c_16502])).

tff(c_13486,plain,(
    ! [A_438,B_439] :
      ( k4_xboole_0(A_438,B_439) = k3_subset_1(A_438,B_439)
      | ~ m1_subset_1(B_439,k1_zfmisc_1(A_438)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18153,plain,(
    ! [B_570,A_571] :
      ( k4_xboole_0(B_570,A_571) = k3_subset_1(B_570,A_571)
      | ~ r1_tarski(A_571,B_570) ) ),
    inference(resolution,[status(thm)],[c_40,c_13486])).

tff(c_18243,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_15602,c_18153])).

tff(c_18325,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16508,c_18243])).

tff(c_14001,plain,(
    ! [A_458,B_459] :
      ( k3_subset_1(A_458,k3_subset_1(A_458,B_459)) = B_459
      | ~ m1_subset_1(B_459,k1_zfmisc_1(A_458)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14009,plain,(
    ! [B_42,A_41] :
      ( k3_subset_1(B_42,k3_subset_1(B_42,A_41)) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_40,c_14001])).

tff(c_21845,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18325,c_14009])).

tff(c_21855,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15602,c_21845])).

tff(c_12603,plain,(
    ! [A_386,B_387] : k3_tarski(k2_tarski(A_386,B_387)) = k2_xboole_0(A_386,B_387) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12692,plain,(
    ! [A_396,B_397] : k3_tarski(k2_tarski(A_396,B_397)) = k2_xboole_0(B_397,A_396) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_12603])).

tff(c_12717,plain,(
    ! [B_398,A_399] : k2_xboole_0(B_398,A_399) = k2_xboole_0(A_399,B_398) ),
    inference(superposition,[status(thm),theory(equality)],[c_12692,c_24])).

tff(c_12733,plain,(
    ! [A_399] : k2_xboole_0(k1_xboole_0,A_399) = A_399 ),
    inference(superposition,[status(thm),theory(equality)],[c_12717,c_4])).

tff(c_12764,plain,(
    ! [A_400] : k2_xboole_0(k1_xboole_0,A_400) = A_400 ),
    inference(superposition,[status(thm),theory(equality)],[c_12717,c_4])).

tff(c_12777,plain,(
    ! [B_12] : k4_xboole_0(B_12,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_12764,c_12])).

tff(c_12804,plain,(
    ! [B_12] : k4_xboole_0(B_12,k1_xboole_0) = B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12733,c_12777])).

tff(c_13209,plain,(
    ! [A_423,B_424,C_425] :
      ( r1_tarski(A_423,k2_xboole_0(B_424,C_425))
      | ~ r1_tarski(k4_xboole_0(A_423,B_424),C_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_13235,plain,(
    ! [A_426,B_427] : r1_tarski(A_426,k2_xboole_0(B_427,A_426)) ),
    inference(resolution,[status(thm)],[c_8,c_13209])).

tff(c_13274,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_13235])).

tff(c_18273,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = k3_subset_1(A_3,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13274,c_18153])).

tff(c_18337,plain,(
    ! [A_3] : k3_subset_1(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12804,c_18273])).

tff(c_16697,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16508,c_8])).

tff(c_13797,plain,(
    ! [A_449,B_450,C_451] :
      ( r1_tarski(k4_xboole_0(A_449,B_450),C_451)
      | ~ r1_tarski(A_449,k2_xboole_0(B_450,C_451)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12627,plain,(
    ! [A_390,B_391] : k1_setfam_1(k2_tarski(A_390,B_391)) = k3_xboole_0(B_391,A_390) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_111])).

tff(c_12633,plain,(
    ! [B_391,A_390] : k3_xboole_0(B_391,A_390) = k3_xboole_0(A_390,B_391) ),
    inference(superposition,[status(thm),theory(equality)],[c_12627,c_36])).

tff(c_12937,plain,(
    ! [A_407,B_408] : k4_xboole_0(A_407,k4_xboole_0(A_407,B_408)) = k3_xboole_0(A_407,B_408) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12968,plain,(
    ! [A_409,B_410] : r1_tarski(k3_xboole_0(A_409,B_410),A_409) ),
    inference(superposition,[status(thm),theory(equality)],[c_12937,c_8])).

tff(c_12974,plain,(
    ! [B_391,A_390] : r1_tarski(k3_xboole_0(B_391,A_390),A_390) ),
    inference(superposition,[status(thm),theory(equality)],[c_12633,c_12968])).

tff(c_13284,plain,(
    ! [A_428] : r1_tarski(k1_xboole_0,A_428) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_13235])).

tff(c_13379,plain,(
    ! [A_433,A_434] :
      ( r1_tarski(A_433,A_434)
      | ~ r1_tarski(A_433,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13284,c_6])).

tff(c_13402,plain,(
    ! [B_435,A_436] : r1_tarski(k3_xboole_0(B_435,k1_xboole_0),A_436) ),
    inference(resolution,[status(thm)],[c_12974,c_13379])).

tff(c_13429,plain,(
    ! [B_435] : k3_xboole_0(B_435,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13402,c_10])).

tff(c_12964,plain,(
    ! [B_12] : k4_xboole_0(B_12,B_12) = k3_xboole_0(B_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12804,c_12937])).

tff(c_13495,plain,(
    ! [B_440] : k4_xboole_0(B_440,B_440) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13429,c_12964])).

tff(c_13516,plain,(
    ! [B_440] :
      ( k1_xboole_0 = B_440
      | ~ r1_tarski(B_440,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13495,c_10])).

tff(c_13801,plain,(
    ! [A_449,B_450] :
      ( k4_xboole_0(A_449,B_450) = k1_xboole_0
      | ~ r1_tarski(A_449,k2_xboole_0(B_450,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_13797,c_13516])).

tff(c_13832,plain,(
    ! [A_449,B_450] :
      ( k4_xboole_0(A_449,B_450) = k1_xboole_0
      | ~ r1_tarski(A_449,B_450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_13801])).

tff(c_16710,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16697,c_13832])).

tff(c_18,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18294,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_8,c_18153])).

tff(c_21611,plain,(
    ! [A_627,B_628] : k3_subset_1(A_627,k4_xboole_0(A_627,B_628)) = k3_xboole_0(A_627,B_628) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18294])).

tff(c_21647,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16710,c_21611])).

tff(c_21706,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18337,c_21647])).

tff(c_21617,plain,(
    ! [A_627,B_628] :
      ( k3_subset_1(A_627,k3_xboole_0(A_627,B_628)) = k4_xboole_0(A_627,B_628)
      | ~ r1_tarski(k4_xboole_0(A_627,B_628),A_627) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21611,c_14009])).

tff(c_22866,plain,(
    ! [A_645,B_646] : k3_subset_1(A_645,k3_xboole_0(A_645,B_646)) = k4_xboole_0(A_645,B_646) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_21617])).

tff(c_22911,plain,(
    ! [B_391,A_390] : k3_subset_1(B_391,k3_xboole_0(A_390,B_391)) = k4_xboole_0(B_391,A_390) ),
    inference(superposition,[status(thm),theory(equality)],[c_12633,c_22866])).

tff(c_32357,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21706,c_22911])).

tff(c_32467,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21855,c_32357])).

tff(c_32469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14441,c_32467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.72/4.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.72/4.65  
% 10.72/4.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.72/4.65  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.72/4.65  
% 10.72/4.65  %Foreground sorts:
% 10.72/4.65  
% 10.72/4.65  
% 10.72/4.65  %Background operators:
% 10.72/4.65  
% 10.72/4.65  
% 10.72/4.65  %Foreground operators:
% 10.72/4.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.72/4.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.72/4.65  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.72/4.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.72/4.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.72/4.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.72/4.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.72/4.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.72/4.65  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.72/4.65  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.72/4.65  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.72/4.65  tff('#skF_2', type, '#skF_2': $i).
% 10.72/4.65  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.72/4.65  tff('#skF_1', type, '#skF_1': $i).
% 10.72/4.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.72/4.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.72/4.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.72/4.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.72/4.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.72/4.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.72/4.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.72/4.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.72/4.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.72/4.65  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.72/4.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.72/4.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.72/4.65  
% 10.96/4.68  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 10.96/4.68  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.96/4.68  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.96/4.68  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.96/4.68  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 10.96/4.68  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.96/4.68  tff(f_83, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.96/4.68  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.96/4.68  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 10.96/4.68  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.96/4.68  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 10.96/4.68  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.96/4.68  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.96/4.68  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.96/4.68  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.96/4.68  tff(f_77, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.96/4.68  tff(f_101, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 10.96/4.68  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 10.96/4.68  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 10.96/4.68  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.96/4.68  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.96/4.68  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.96/4.68  tff(c_14190, plain, (![A_464, B_465, C_466]: (k7_subset_1(A_464, B_465, C_466)=k4_xboole_0(B_465, C_466) | ~m1_subset_1(B_465, k1_zfmisc_1(A_464)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.96/4.68  tff(c_14199, plain, (![C_466]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_466)=k4_xboole_0('#skF_2', C_466))), inference(resolution, [status(thm)], [c_54, c_14190])).
% 10.96/4.68  tff(c_60, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.96/4.68  tff(c_287, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_60])).
% 10.96/4.68  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.96/4.68  tff(c_1987, plain, (![A_173, B_174, C_175]: (k7_subset_1(A_173, B_174, C_175)=k4_xboole_0(B_174, C_175) | ~m1_subset_1(B_174, k1_zfmisc_1(A_173)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.96/4.68  tff(c_2078, plain, (![C_177]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_177)=k4_xboole_0('#skF_2', C_177))), inference(resolution, [status(thm)], [c_54, c_1987])).
% 10.96/4.68  tff(c_66, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.96/4.68  tff(c_127, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_66])).
% 10.96/4.68  tff(c_2084, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2078, c_127])).
% 10.96/4.68  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.96/4.68  tff(c_2503, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2084, c_8])).
% 10.96/4.68  tff(c_14, plain, (![A_13, B_14, C_15]: (r1_tarski(k4_xboole_0(A_13, B_14), C_15) | ~r1_tarski(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.96/4.68  tff(c_22, plain, (![B_24, A_23]: (k2_tarski(B_24, A_23)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.96/4.68  tff(c_111, plain, (![A_67, B_68]: (k1_setfam_1(k2_tarski(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.96/4.68  tff(c_152, plain, (![B_75, A_76]: (k1_setfam_1(k2_tarski(B_75, A_76))=k3_xboole_0(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_22, c_111])).
% 10.96/4.68  tff(c_36, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.96/4.68  tff(c_158, plain, (![B_75, A_76]: (k3_xboole_0(B_75, A_76)=k3_xboole_0(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_152, c_36])).
% 10.96/4.68  tff(c_465, plain, (![A_92, B_93]: (k4_xboole_0(A_92, k4_xboole_0(A_92, B_93))=k3_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.96/4.68  tff(c_496, plain, (![A_94, B_95]: (r1_tarski(k3_xboole_0(A_94, B_95), A_94))), inference(superposition, [status(thm), theory('equality')], [c_465, c_8])).
% 10.96/4.68  tff(c_502, plain, (![B_75, A_76]: (r1_tarski(k3_xboole_0(B_75, A_76), A_76))), inference(superposition, [status(thm), theory('equality')], [c_158, c_496])).
% 10.96/4.68  tff(c_1208, plain, (![A_151, B_152, C_153]: (r1_tarski(A_151, k2_xboole_0(B_152, C_153)) | ~r1_tarski(k4_xboole_0(A_151, B_152), C_153))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.96/4.68  tff(c_1250, plain, (![A_154, B_155]: (r1_tarski(A_154, k2_xboole_0(B_155, A_154)))), inference(resolution, [status(thm)], [c_8, c_1208])).
% 10.96/4.68  tff(c_1302, plain, (![A_156]: (r1_tarski(k1_xboole_0, A_156))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1250])).
% 10.96/4.68  tff(c_6, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(B_5, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.96/4.68  tff(c_1430, plain, (![A_161, A_162]: (r1_tarski(A_161, A_162) | ~r1_tarski(A_161, k1_xboole_0))), inference(resolution, [status(thm)], [c_1302, c_6])).
% 10.96/4.68  tff(c_1494, plain, (![B_163, A_164]: (r1_tarski(k3_xboole_0(B_163, k1_xboole_0), A_164))), inference(resolution, [status(thm)], [c_502, c_1430])).
% 10.96/4.68  tff(c_10, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k4_xboole_0(B_10, A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.96/4.68  tff(c_1537, plain, (![B_163]: (k3_xboole_0(B_163, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1494, c_10])).
% 10.96/4.68  tff(c_137, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.96/4.68  tff(c_217, plain, (![B_81, A_82]: (k3_tarski(k2_tarski(B_81, A_82))=k2_xboole_0(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_22, c_137])).
% 10.96/4.68  tff(c_24, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.96/4.68  tff(c_240, plain, (![B_83, A_84]: (k2_xboole_0(B_83, A_84)=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_217, c_24])).
% 10.96/4.68  tff(c_278, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_240])).
% 10.96/4.68  tff(c_288, plain, (![A_85]: (k2_xboole_0(k1_xboole_0, A_85)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_4, c_240])).
% 10.96/4.68  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.96/4.68  tff(c_301, plain, (![B_12]: (k4_xboole_0(B_12, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_12))), inference(superposition, [status(thm), theory('equality')], [c_288, c_12])).
% 10.96/4.68  tff(c_328, plain, (![B_12]: (k4_xboole_0(B_12, k1_xboole_0)=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_278, c_301])).
% 10.96/4.68  tff(c_544, plain, (![B_100]: (k4_xboole_0(B_100, B_100)=k3_xboole_0(B_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_328, c_465])).
% 10.96/4.68  tff(c_563, plain, (![B_100]: (k1_xboole_0=B_100 | ~r1_tarski(B_100, k3_xboole_0(B_100, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_544, c_10])).
% 10.96/4.68  tff(c_2097, plain, (![B_178]: (k1_xboole_0=B_178 | ~r1_tarski(B_178, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1537, c_563])).
% 10.96/4.68  tff(c_2141, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_tarski(A_13, k2_xboole_0(B_14, k1_xboole_0)))), inference(resolution, [status(thm)], [c_14, c_2097])).
% 10.96/4.68  tff(c_4307, plain, (![A_264, B_265]: (k4_xboole_0(A_264, B_265)=k1_xboole_0 | ~r1_tarski(A_264, B_265))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2141])).
% 10.96/4.68  tff(c_4488, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2503, c_4307])).
% 10.96/4.68  tff(c_5540, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4488, c_12])).
% 10.96/4.68  tff(c_5563, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_5540])).
% 10.96/4.68  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.96/4.68  tff(c_2910, plain, (![A_215, B_216]: (k4_subset_1(u1_struct_0(A_215), B_216, k2_tops_1(A_215, B_216))=k2_pre_topc(A_215, B_216) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.96/4.68  tff(c_2920, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_2910])).
% 10.96/4.68  tff(c_2926, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2920])).
% 10.96/4.68  tff(c_353, plain, (![B_88]: (k4_xboole_0(B_88, k1_xboole_0)=B_88)), inference(demodulation, [status(thm), theory('equality')], [c_278, c_301])).
% 10.96/4.68  tff(c_368, plain, (![B_88]: (r1_tarski(B_88, B_88))), inference(superposition, [status(thm), theory('equality')], [c_353, c_8])).
% 10.96/4.68  tff(c_128, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.96/4.68  tff(c_136, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_128])).
% 10.96/4.68  tff(c_667, plain, (![A_103, C_104, B_105]: (r1_tarski(A_103, C_104) | ~r1_tarski(B_105, C_104) | ~r1_tarski(A_103, B_105))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.96/4.68  tff(c_686, plain, (![A_106]: (r1_tarski(A_106, u1_struct_0('#skF_1')) | ~r1_tarski(A_106, '#skF_2'))), inference(resolution, [status(thm)], [c_136, c_667])).
% 10.96/4.68  tff(c_689, plain, (![A_4, A_106]: (r1_tarski(A_4, u1_struct_0('#skF_1')) | ~r1_tarski(A_4, A_106) | ~r1_tarski(A_106, '#skF_2'))), inference(resolution, [status(thm)], [c_686, c_6])).
% 10.96/4.68  tff(c_2509, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2503, c_689])).
% 10.96/4.68  tff(c_2514, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_2509])).
% 10.96/4.68  tff(c_40, plain, (![A_41, B_42]: (m1_subset_1(A_41, k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.96/4.68  tff(c_2625, plain, (![A_199, B_200, C_201]: (k4_subset_1(A_199, B_200, C_201)=k2_xboole_0(B_200, C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(A_199)) | ~m1_subset_1(B_200, k1_zfmisc_1(A_199)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.96/4.68  tff(c_11904, plain, (![B_364, B_365, A_366]: (k4_subset_1(B_364, B_365, A_366)=k2_xboole_0(B_365, A_366) | ~m1_subset_1(B_365, k1_zfmisc_1(B_364)) | ~r1_tarski(A_366, B_364))), inference(resolution, [status(thm)], [c_40, c_2625])).
% 10.96/4.68  tff(c_12219, plain, (![A_373]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_373)=k2_xboole_0('#skF_2', A_373) | ~r1_tarski(A_373, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_11904])).
% 10.96/4.68  tff(c_12275, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2514, c_12219])).
% 10.96/4.68  tff(c_12372, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5563, c_2926, c_12275])).
% 10.96/4.68  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.96/4.68  tff(c_2215, plain, (![A_181, B_182]: (v4_pre_topc(k2_pre_topc(A_181, B_182), A_181) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.96/4.68  tff(c_2225, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_2215])).
% 10.96/4.68  tff(c_2231, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2225])).
% 10.96/4.68  tff(c_12397, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12372, c_2231])).
% 10.96/4.68  tff(c_12399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_12397])).
% 10.96/4.68  tff(c_12400, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 10.96/4.68  tff(c_12600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12400, c_127])).
% 10.96/4.68  tff(c_12601, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 10.96/4.68  tff(c_12716, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12601, c_60])).
% 10.96/4.68  tff(c_14441, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14199, c_12716])).
% 10.96/4.68  tff(c_15586, plain, (![A_503, B_504]: (r1_tarski(k2_tops_1(A_503, B_504), B_504) | ~v4_pre_topc(B_504, A_503) | ~m1_subset_1(B_504, k1_zfmisc_1(u1_struct_0(A_503))) | ~l1_pre_topc(A_503))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.96/4.68  tff(c_15596, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_15586])).
% 10.96/4.68  tff(c_15602, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12601, c_15596])).
% 10.96/4.68  tff(c_16492, plain, (![A_526, B_527]: (k7_subset_1(u1_struct_0(A_526), B_527, k2_tops_1(A_526, B_527))=k1_tops_1(A_526, B_527) | ~m1_subset_1(B_527, k1_zfmisc_1(u1_struct_0(A_526))) | ~l1_pre_topc(A_526))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.96/4.68  tff(c_16502, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_16492])).
% 10.96/4.68  tff(c_16508, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_14199, c_16502])).
% 10.96/4.68  tff(c_13486, plain, (![A_438, B_439]: (k4_xboole_0(A_438, B_439)=k3_subset_1(A_438, B_439) | ~m1_subset_1(B_439, k1_zfmisc_1(A_438)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.96/4.68  tff(c_18153, plain, (![B_570, A_571]: (k4_xboole_0(B_570, A_571)=k3_subset_1(B_570, A_571) | ~r1_tarski(A_571, B_570))), inference(resolution, [status(thm)], [c_40, c_13486])).
% 10.96/4.68  tff(c_18243, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_15602, c_18153])).
% 10.96/4.68  tff(c_18325, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16508, c_18243])).
% 10.96/4.68  tff(c_14001, plain, (![A_458, B_459]: (k3_subset_1(A_458, k3_subset_1(A_458, B_459))=B_459 | ~m1_subset_1(B_459, k1_zfmisc_1(A_458)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.96/4.68  tff(c_14009, plain, (![B_42, A_41]: (k3_subset_1(B_42, k3_subset_1(B_42, A_41))=A_41 | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_40, c_14001])).
% 10.96/4.68  tff(c_21845, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18325, c_14009])).
% 10.96/4.68  tff(c_21855, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15602, c_21845])).
% 10.96/4.68  tff(c_12603, plain, (![A_386, B_387]: (k3_tarski(k2_tarski(A_386, B_387))=k2_xboole_0(A_386, B_387))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.96/4.68  tff(c_12692, plain, (![A_396, B_397]: (k3_tarski(k2_tarski(A_396, B_397))=k2_xboole_0(B_397, A_396))), inference(superposition, [status(thm), theory('equality')], [c_22, c_12603])).
% 10.96/4.68  tff(c_12717, plain, (![B_398, A_399]: (k2_xboole_0(B_398, A_399)=k2_xboole_0(A_399, B_398))), inference(superposition, [status(thm), theory('equality')], [c_12692, c_24])).
% 10.96/4.68  tff(c_12733, plain, (![A_399]: (k2_xboole_0(k1_xboole_0, A_399)=A_399)), inference(superposition, [status(thm), theory('equality')], [c_12717, c_4])).
% 10.96/4.68  tff(c_12764, plain, (![A_400]: (k2_xboole_0(k1_xboole_0, A_400)=A_400)), inference(superposition, [status(thm), theory('equality')], [c_12717, c_4])).
% 10.96/4.68  tff(c_12777, plain, (![B_12]: (k4_xboole_0(B_12, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_12))), inference(superposition, [status(thm), theory('equality')], [c_12764, c_12])).
% 10.96/4.68  tff(c_12804, plain, (![B_12]: (k4_xboole_0(B_12, k1_xboole_0)=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_12733, c_12777])).
% 10.96/4.68  tff(c_13209, plain, (![A_423, B_424, C_425]: (r1_tarski(A_423, k2_xboole_0(B_424, C_425)) | ~r1_tarski(k4_xboole_0(A_423, B_424), C_425))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.96/4.68  tff(c_13235, plain, (![A_426, B_427]: (r1_tarski(A_426, k2_xboole_0(B_427, A_426)))), inference(resolution, [status(thm)], [c_8, c_13209])).
% 10.96/4.68  tff(c_13274, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_13235])).
% 10.96/4.68  tff(c_18273, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=k3_subset_1(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_13274, c_18153])).
% 10.96/4.68  tff(c_18337, plain, (![A_3]: (k3_subset_1(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_12804, c_18273])).
% 10.96/4.68  tff(c_16697, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16508, c_8])).
% 10.96/4.68  tff(c_13797, plain, (![A_449, B_450, C_451]: (r1_tarski(k4_xboole_0(A_449, B_450), C_451) | ~r1_tarski(A_449, k2_xboole_0(B_450, C_451)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.96/4.68  tff(c_12627, plain, (![A_390, B_391]: (k1_setfam_1(k2_tarski(A_390, B_391))=k3_xboole_0(B_391, A_390))), inference(superposition, [status(thm), theory('equality')], [c_22, c_111])).
% 10.96/4.68  tff(c_12633, plain, (![B_391, A_390]: (k3_xboole_0(B_391, A_390)=k3_xboole_0(A_390, B_391))), inference(superposition, [status(thm), theory('equality')], [c_12627, c_36])).
% 10.96/4.68  tff(c_12937, plain, (![A_407, B_408]: (k4_xboole_0(A_407, k4_xboole_0(A_407, B_408))=k3_xboole_0(A_407, B_408))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.96/4.68  tff(c_12968, plain, (![A_409, B_410]: (r1_tarski(k3_xboole_0(A_409, B_410), A_409))), inference(superposition, [status(thm), theory('equality')], [c_12937, c_8])).
% 10.96/4.68  tff(c_12974, plain, (![B_391, A_390]: (r1_tarski(k3_xboole_0(B_391, A_390), A_390))), inference(superposition, [status(thm), theory('equality')], [c_12633, c_12968])).
% 10.96/4.68  tff(c_13284, plain, (![A_428]: (r1_tarski(k1_xboole_0, A_428))), inference(superposition, [status(thm), theory('equality')], [c_4, c_13235])).
% 10.96/4.68  tff(c_13379, plain, (![A_433, A_434]: (r1_tarski(A_433, A_434) | ~r1_tarski(A_433, k1_xboole_0))), inference(resolution, [status(thm)], [c_13284, c_6])).
% 10.96/4.68  tff(c_13402, plain, (![B_435, A_436]: (r1_tarski(k3_xboole_0(B_435, k1_xboole_0), A_436))), inference(resolution, [status(thm)], [c_12974, c_13379])).
% 10.96/4.68  tff(c_13429, plain, (![B_435]: (k3_xboole_0(B_435, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_13402, c_10])).
% 10.96/4.68  tff(c_12964, plain, (![B_12]: (k4_xboole_0(B_12, B_12)=k3_xboole_0(B_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12804, c_12937])).
% 10.96/4.68  tff(c_13495, plain, (![B_440]: (k4_xboole_0(B_440, B_440)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13429, c_12964])).
% 10.96/4.68  tff(c_13516, plain, (![B_440]: (k1_xboole_0=B_440 | ~r1_tarski(B_440, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13495, c_10])).
% 10.96/4.68  tff(c_13801, plain, (![A_449, B_450]: (k4_xboole_0(A_449, B_450)=k1_xboole_0 | ~r1_tarski(A_449, k2_xboole_0(B_450, k1_xboole_0)))), inference(resolution, [status(thm)], [c_13797, c_13516])).
% 10.96/4.68  tff(c_13832, plain, (![A_449, B_450]: (k4_xboole_0(A_449, B_450)=k1_xboole_0 | ~r1_tarski(A_449, B_450))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_13801])).
% 10.96/4.68  tff(c_16710, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16697, c_13832])).
% 10.96/4.68  tff(c_18, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.96/4.68  tff(c_18294, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_subset_1(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_8, c_18153])).
% 10.96/4.68  tff(c_21611, plain, (![A_627, B_628]: (k3_subset_1(A_627, k4_xboole_0(A_627, B_628))=k3_xboole_0(A_627, B_628))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18294])).
% 10.96/4.68  tff(c_21647, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16710, c_21611])).
% 10.96/4.68  tff(c_21706, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18337, c_21647])).
% 10.96/4.68  tff(c_21617, plain, (![A_627, B_628]: (k3_subset_1(A_627, k3_xboole_0(A_627, B_628))=k4_xboole_0(A_627, B_628) | ~r1_tarski(k4_xboole_0(A_627, B_628), A_627))), inference(superposition, [status(thm), theory('equality')], [c_21611, c_14009])).
% 10.96/4.68  tff(c_22866, plain, (![A_645, B_646]: (k3_subset_1(A_645, k3_xboole_0(A_645, B_646))=k4_xboole_0(A_645, B_646))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_21617])).
% 10.96/4.68  tff(c_22911, plain, (![B_391, A_390]: (k3_subset_1(B_391, k3_xboole_0(A_390, B_391))=k4_xboole_0(B_391, A_390))), inference(superposition, [status(thm), theory('equality')], [c_12633, c_22866])).
% 10.96/4.68  tff(c_32357, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_21706, c_22911])).
% 10.96/4.68  tff(c_32467, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21855, c_32357])).
% 10.96/4.68  tff(c_32469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14441, c_32467])).
% 10.96/4.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.96/4.68  
% 10.96/4.68  Inference rules
% 10.96/4.68  ----------------------
% 10.96/4.68  #Ref     : 0
% 10.96/4.68  #Sup     : 7890
% 10.96/4.68  #Fact    : 0
% 10.96/4.68  #Define  : 0
% 10.96/4.68  #Split   : 6
% 10.96/4.68  #Chain   : 0
% 10.96/4.68  #Close   : 0
% 10.96/4.68  
% 10.96/4.68  Ordering : KBO
% 10.96/4.68  
% 10.96/4.68  Simplification rules
% 10.96/4.68  ----------------------
% 10.96/4.68  #Subsume      : 442
% 10.96/4.68  #Demod        : 6597
% 10.96/4.68  #Tautology    : 4861
% 10.96/4.68  #SimpNegUnit  : 3
% 10.96/4.68  #BackRed      : 19
% 10.96/4.68  
% 10.96/4.68  #Partial instantiations: 0
% 10.96/4.68  #Strategies tried      : 1
% 10.96/4.68  
% 10.96/4.68  Timing (in seconds)
% 10.96/4.68  ----------------------
% 10.96/4.68  Preprocessing        : 0.38
% 10.96/4.68  Parsing              : 0.21
% 10.96/4.68  CNF conversion       : 0.03
% 10.96/4.68  Main loop            : 3.46
% 10.96/4.68  Inferencing          : 0.68
% 10.96/4.68  Reduction            : 1.83
% 10.96/4.68  Demodulation         : 1.57
% 10.96/4.68  BG Simplification    : 0.08
% 10.96/4.68  Subsumption          : 0.65
% 10.96/4.68  Abstraction          : 0.11
% 10.96/4.68  MUC search           : 0.00
% 10.96/4.68  Cooper               : 0.00
% 10.96/4.68  Total                : 3.90
% 10.96/4.68  Index Insertion      : 0.00
% 10.96/4.68  Index Deletion       : 0.00
% 10.96/4.68  Index Matching       : 0.00
% 10.96/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------

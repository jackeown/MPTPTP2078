%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:22 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 232 expanded)
%              Number of leaves         :   43 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :  152 ( 373 expanded)
%              Number of equality atoms :   81 ( 172 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4225,plain,(
    ! [A_222,B_223,C_224] :
      ( k7_subset_1(A_222,B_223,C_224) = k4_xboole_0(B_223,C_224)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(A_222)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4228,plain,(
    ! [C_224] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_224) = k4_xboole_0('#skF_2',C_224) ),
    inference(resolution,[status(thm)],[c_40,c_4225])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_94,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1134,plain,(
    ! [B_109,A_110] :
      ( v4_pre_topc(B_109,A_110)
      | k2_pre_topc(A_110,B_109) != B_109
      | ~ v2_pre_topc(A_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1140,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1134])).

tff(c_1144,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1140])).

tff(c_1145,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1144])).

tff(c_1362,plain,(
    ! [A_117,B_118] :
      ( k4_subset_1(u1_struct_0(A_117),B_118,k2_tops_1(A_117,B_118)) = k2_pre_topc(A_117,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1366,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1362])).

tff(c_1370,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1366])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_tops_1(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1037,plain,(
    ! [A_103,B_104,C_105] :
      ( k4_subset_1(A_103,B_104,C_105) = k2_xboole_0(B_104,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3068,plain,(
    ! [A_161,B_162,B_163] :
      ( k4_subset_1(u1_struct_0(A_161),B_162,k2_tops_1(A_161,B_163)) = k2_xboole_0(B_162,k2_tops_1(A_161,B_163))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_34,c_1037])).

tff(c_3072,plain,(
    ! [B_163] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_163)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_163))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_3068])).

tff(c_3080,plain,(
    ! [B_164] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_164)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_164))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3072])).

tff(c_3087,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_3080])).

tff(c_3092,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1370,c_3087])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_356,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_382,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_356])).

tff(c_385,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_382])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_254,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_52])).

tff(c_506,plain,(
    ! [A_80,B_81,C_82] :
      ( k7_subset_1(A_80,B_81,C_82) = k4_xboole_0(B_81,C_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_579,plain,(
    ! [C_84] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_84) = k4_xboole_0('#skF_2',C_84) ),
    inference(resolution,[status(thm)],[c_40,c_506])).

tff(c_591,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_579])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_163,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_834,plain,(
    ! [A_95,B_96] : k3_xboole_0(k4_xboole_0(A_95,B_96),A_95) = k4_xboole_0(A_95,B_96) ),
    inference(resolution,[status(thm)],[c_10,c_163])).

tff(c_20,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_148,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_333,plain,(
    ! [B_72,A_73] : k1_setfam_1(k2_tarski(B_72,A_73)) = k3_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_148])).

tff(c_28,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_339,plain,(
    ! [B_72,A_73] : k3_xboole_0(B_72,A_73) = k3_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_28])).

tff(c_994,plain,(
    ! [A_101,B_102] : k3_xboole_0(A_101,k4_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_339])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1207,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k4_xboole_0(A_113,B_114)) = k4_xboole_0(A_113,k4_xboole_0(A_113,B_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_4])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1218,plain,(
    ! [B_114] : k4_xboole_0(B_114,k4_xboole_0(B_114,B_114)) = k2_xboole_0(B_114,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_18])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_176,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(resolution,[status(thm)],[c_16,c_163])).

tff(c_1254,plain,(
    ! [B_115] : k4_xboole_0(B_115,k4_xboole_0(B_115,B_115)) = k2_xboole_0(B_115,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_18])).

tff(c_843,plain,(
    ! [A_95,B_96] : k3_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_339])).

tff(c_1263,plain,(
    ! [B_115] : k4_xboole_0(B_115,k4_xboole_0(B_115,B_115)) = k3_xboole_0(B_115,k2_xboole_0(B_115,B_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1254,c_843])).

tff(c_1296,plain,(
    ! [B_115] : k2_xboole_0(B_115,B_115) = B_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_176,c_1263])).

tff(c_1381,plain,(
    ! [B_119] : k4_xboole_0(B_119,k4_xboole_0(B_119,B_119)) = B_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_1218])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1403,plain,(
    ! [B_119] :
      ( k4_xboole_0(B_119,B_119) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(B_119,B_119),B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_12])).

tff(c_1429,plain,(
    ! [B_119] : k4_xboole_0(B_119,B_119) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1403])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_379,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_356])).

tff(c_1438,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1429,c_379])).

tff(c_846,plain,(
    ! [A_95,B_96] : k5_xboole_0(k4_xboole_0(A_95,B_96),k4_xboole_0(A_95,B_96)) = k4_xboole_0(k4_xboole_0(A_95,B_96),A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_4])).

tff(c_3219,plain,(
    ! [A_165,B_166] : k4_xboole_0(k4_xboole_0(A_165,B_166),A_165) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_846])).

tff(c_3269,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_3219])).

tff(c_3455,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3269,c_18])).

tff(c_3469,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_385,c_3455])).

tff(c_3471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1145,c_3469])).

tff(c_3472,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3474,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_3773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3472,c_3474])).

tff(c_3775,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4351,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4228,c_3775])).

tff(c_3473,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4289,plain,(
    ! [A_227,B_228] :
      ( k2_pre_topc(A_227,B_228) = B_228
      | ~ v4_pre_topc(B_228,A_227)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4292,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_4289])).

tff(c_4295,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3473,c_4292])).

tff(c_5215,plain,(
    ! [A_266,B_267] :
      ( k7_subset_1(u1_struct_0(A_266),k2_pre_topc(A_266,B_267),k1_tops_1(A_266,B_267)) = k2_tops_1(A_266,B_267)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5224,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4295,c_5215])).

tff(c_5228,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4228,c_5224])).

tff(c_5230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4351,c_5228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.94  
% 4.84/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.95  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.84/1.95  
% 4.84/1.95  %Foreground sorts:
% 4.84/1.95  
% 4.84/1.95  
% 4.84/1.95  %Background operators:
% 4.84/1.95  
% 4.84/1.95  
% 4.84/1.95  %Foreground operators:
% 4.84/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.84/1.95  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.84/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/1.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.84/1.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.84/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.84/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.84/1.95  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.84/1.95  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.84/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.84/1.95  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.84/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.84/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/1.95  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.84/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/1.95  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.84/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/1.95  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.84/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.84/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.84/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.84/1.95  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.84/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/1.95  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.84/1.95  
% 4.84/1.97  tff(f_110, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 4.84/1.97  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.84/1.97  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.84/1.97  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 4.84/1.97  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.84/1.97  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.84/1.97  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.84/1.97  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.84/1.97  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.84/1.97  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.84/1.97  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.84/1.97  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.84/1.97  tff(f_63, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.84/1.97  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.84/1.97  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.84/1.97  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.84/1.97  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.84/1.97  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.84/1.97  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.84/1.97  tff(c_4225, plain, (![A_222, B_223, C_224]: (k7_subset_1(A_222, B_223, C_224)=k4_xboole_0(B_223, C_224) | ~m1_subset_1(B_223, k1_zfmisc_1(A_222)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.84/1.97  tff(c_4228, plain, (![C_224]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_224)=k4_xboole_0('#skF_2', C_224))), inference(resolution, [status(thm)], [c_40, c_4225])).
% 4.84/1.97  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.84/1.97  tff(c_94, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.84/1.97  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.84/1.97  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.84/1.97  tff(c_1134, plain, (![B_109, A_110]: (v4_pre_topc(B_109, A_110) | k2_pre_topc(A_110, B_109)!=B_109 | ~v2_pre_topc(A_110) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.84/1.97  tff(c_1140, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1134])).
% 4.84/1.97  tff(c_1144, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1140])).
% 4.84/1.97  tff(c_1145, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_94, c_1144])).
% 4.84/1.97  tff(c_1362, plain, (![A_117, B_118]: (k4_subset_1(u1_struct_0(A_117), B_118, k2_tops_1(A_117, B_118))=k2_pre_topc(A_117, B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.84/1.97  tff(c_1366, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1362])).
% 4.84/1.97  tff(c_1370, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1366])).
% 4.84/1.97  tff(c_34, plain, (![A_32, B_33]: (m1_subset_1(k2_tops_1(A_32, B_33), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.84/1.97  tff(c_1037, plain, (![A_103, B_104, C_105]: (k4_subset_1(A_103, B_104, C_105)=k2_xboole_0(B_104, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.84/1.97  tff(c_3068, plain, (![A_161, B_162, B_163]: (k4_subset_1(u1_struct_0(A_161), B_162, k2_tops_1(A_161, B_163))=k2_xboole_0(B_162, k2_tops_1(A_161, B_163)) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_34, c_1037])).
% 4.84/1.97  tff(c_3072, plain, (![B_163]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_163))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_163)) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_3068])).
% 4.84/1.97  tff(c_3080, plain, (![B_164]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_164))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_164)) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3072])).
% 4.84/1.97  tff(c_3087, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_3080])).
% 4.84/1.97  tff(c_3092, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1370, c_3087])).
% 4.84/1.97  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.84/1.97  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.84/1.97  tff(c_356, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.84/1.97  tff(c_382, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_356])).
% 4.84/1.97  tff(c_385, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_382])).
% 4.84/1.97  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.84/1.97  tff(c_254, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_94, c_52])).
% 4.84/1.97  tff(c_506, plain, (![A_80, B_81, C_82]: (k7_subset_1(A_80, B_81, C_82)=k4_xboole_0(B_81, C_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.84/1.97  tff(c_579, plain, (![C_84]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_84)=k4_xboole_0('#skF_2', C_84))), inference(resolution, [status(thm)], [c_40, c_506])).
% 4.84/1.97  tff(c_591, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_254, c_579])).
% 4.84/1.97  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.84/1.97  tff(c_163, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.84/1.97  tff(c_834, plain, (![A_95, B_96]: (k3_xboole_0(k4_xboole_0(A_95, B_96), A_95)=k4_xboole_0(A_95, B_96))), inference(resolution, [status(thm)], [c_10, c_163])).
% 4.84/1.97  tff(c_20, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.84/1.97  tff(c_148, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.84/1.97  tff(c_333, plain, (![B_72, A_73]: (k1_setfam_1(k2_tarski(B_72, A_73))=k3_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_20, c_148])).
% 4.84/1.97  tff(c_28, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.84/1.97  tff(c_339, plain, (![B_72, A_73]: (k3_xboole_0(B_72, A_73)=k3_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_333, c_28])).
% 4.84/1.97  tff(c_994, plain, (![A_101, B_102]: (k3_xboole_0(A_101, k4_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_834, c_339])).
% 4.84/1.97  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.84/1.97  tff(c_1207, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k4_xboole_0(A_113, B_114))=k4_xboole_0(A_113, k4_xboole_0(A_113, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_994, c_4])).
% 4.84/1.97  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.97  tff(c_1218, plain, (![B_114]: (k4_xboole_0(B_114, k4_xboole_0(B_114, B_114))=k2_xboole_0(B_114, B_114))), inference(superposition, [status(thm), theory('equality')], [c_1207, c_18])).
% 4.84/1.97  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.84/1.97  tff(c_176, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(resolution, [status(thm)], [c_16, c_163])).
% 4.84/1.97  tff(c_1254, plain, (![B_115]: (k4_xboole_0(B_115, k4_xboole_0(B_115, B_115))=k2_xboole_0(B_115, B_115))), inference(superposition, [status(thm), theory('equality')], [c_1207, c_18])).
% 4.84/1.97  tff(c_843, plain, (![A_95, B_96]: (k3_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(superposition, [status(thm), theory('equality')], [c_834, c_339])).
% 4.84/1.97  tff(c_1263, plain, (![B_115]: (k4_xboole_0(B_115, k4_xboole_0(B_115, B_115))=k3_xboole_0(B_115, k2_xboole_0(B_115, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_1254, c_843])).
% 4.84/1.97  tff(c_1296, plain, (![B_115]: (k2_xboole_0(B_115, B_115)=B_115)), inference(demodulation, [status(thm), theory('equality')], [c_1218, c_176, c_1263])).
% 4.84/1.97  tff(c_1381, plain, (![B_119]: (k4_xboole_0(B_119, k4_xboole_0(B_119, B_119))=B_119)), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_1218])).
% 4.84/1.97  tff(c_12, plain, (![A_10, B_11]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k4_xboole_0(B_11, A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.84/1.97  tff(c_1403, plain, (![B_119]: (k4_xboole_0(B_119, B_119)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(B_119, B_119), B_119))), inference(superposition, [status(thm), theory('equality')], [c_1381, c_12])).
% 4.84/1.97  tff(c_1429, plain, (![B_119]: (k4_xboole_0(B_119, B_119)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1403])).
% 4.84/1.97  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.84/1.97  tff(c_379, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_356])).
% 4.84/1.97  tff(c_1438, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1429, c_379])).
% 4.84/1.97  tff(c_846, plain, (![A_95, B_96]: (k5_xboole_0(k4_xboole_0(A_95, B_96), k4_xboole_0(A_95, B_96))=k4_xboole_0(k4_xboole_0(A_95, B_96), A_95))), inference(superposition, [status(thm), theory('equality')], [c_834, c_4])).
% 4.84/1.97  tff(c_3219, plain, (![A_165, B_166]: (k4_xboole_0(k4_xboole_0(A_165, B_166), A_165)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1438, c_846])).
% 4.84/1.97  tff(c_3269, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_591, c_3219])).
% 4.84/1.97  tff(c_3455, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3269, c_18])).
% 4.84/1.97  tff(c_3469, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_385, c_3455])).
% 4.84/1.97  tff(c_3471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1145, c_3469])).
% 4.84/1.97  tff(c_3472, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.84/1.97  tff(c_3474, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 4.84/1.97  tff(c_3773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3472, c_3474])).
% 4.84/1.97  tff(c_3775, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 4.84/1.97  tff(c_4351, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4228, c_3775])).
% 4.84/1.97  tff(c_3473, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.84/1.97  tff(c_4289, plain, (![A_227, B_228]: (k2_pre_topc(A_227, B_228)=B_228 | ~v4_pre_topc(B_228, A_227) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.84/1.97  tff(c_4292, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_4289])).
% 4.84/1.97  tff(c_4295, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3473, c_4292])).
% 4.84/1.97  tff(c_5215, plain, (![A_266, B_267]: (k7_subset_1(u1_struct_0(A_266), k2_pre_topc(A_266, B_267), k1_tops_1(A_266, B_267))=k2_tops_1(A_266, B_267) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.84/1.97  tff(c_5224, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4295, c_5215])).
% 4.84/1.97  tff(c_5228, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_4228, c_5224])).
% 4.84/1.97  tff(c_5230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4351, c_5228])).
% 4.84/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.97  
% 4.84/1.97  Inference rules
% 4.84/1.97  ----------------------
% 4.84/1.97  #Ref     : 0
% 4.84/1.97  #Sup     : 1245
% 4.84/1.97  #Fact    : 0
% 4.84/1.97  #Define  : 0
% 4.84/1.97  #Split   : 4
% 4.84/1.97  #Chain   : 0
% 4.84/1.97  #Close   : 0
% 4.84/1.97  
% 4.84/1.97  Ordering : KBO
% 4.84/1.97  
% 4.84/1.97  Simplification rules
% 4.84/1.97  ----------------------
% 4.84/1.97  #Subsume      : 49
% 4.84/1.97  #Demod        : 1149
% 4.84/1.97  #Tautology    : 994
% 4.84/1.97  #SimpNegUnit  : 5
% 4.84/1.97  #BackRed      : 16
% 4.84/1.97  
% 4.84/1.97  #Partial instantiations: 0
% 4.84/1.97  #Strategies tried      : 1
% 4.84/1.97  
% 4.84/1.97  Timing (in seconds)
% 4.84/1.97  ----------------------
% 5.16/1.97  Preprocessing        : 0.34
% 5.16/1.97  Parsing              : 0.19
% 5.16/1.97  CNF conversion       : 0.02
% 5.16/1.97  Main loop            : 0.84
% 5.16/1.97  Inferencing          : 0.28
% 5.16/1.97  Reduction            : 0.36
% 5.16/1.97  Demodulation         : 0.29
% 5.16/1.97  BG Simplification    : 0.03
% 5.16/1.97  Subsumption          : 0.11
% 5.16/1.97  Abstraction          : 0.04
% 5.16/1.97  MUC search           : 0.00
% 5.16/1.97  Cooper               : 0.00
% 5.16/1.97  Total                : 1.23
% 5.16/1.97  Index Insertion      : 0.00
% 5.16/1.97  Index Deletion       : 0.00
% 5.16/1.97  Index Matching       : 0.00
% 5.16/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------

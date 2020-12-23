%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:18 EST 2020

% Result     : Theorem 11.58s
% Output     : CNFRefutation 11.58s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 239 expanded)
%              Number of leaves         :   51 (  99 expanded)
%              Depth                    :   11
%              Number of atoms          :  201 ( 419 expanded)
%              Number of equality atoms :   85 ( 145 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_75,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_63,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_17671,plain,(
    ! [A_464,B_465,C_466] :
      ( k7_subset_1(A_464,B_465,C_466) = k4_xboole_0(B_465,C_466)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(A_464)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_17693,plain,(
    ! [C_466] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_466) = k4_xboole_0('#skF_2',C_466) ),
    inference(resolution,[status(thm)],[c_56,c_17671])).

tff(c_62,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_114,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4112,plain,(
    ! [A_219,B_220] :
      ( k4_subset_1(u1_struct_0(A_219),B_220,k2_tops_1(A_219,B_220)) = k2_pre_topc(A_219,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4139,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_4112])).

tff(c_4153,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4139])).

tff(c_1922,plain,(
    ! [A_153,B_154,C_155] :
      ( k7_subset_1(A_153,B_154,C_155) = k4_xboole_0(B_154,C_155)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1954,plain,(
    ! [C_158] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_158) = k4_xboole_0('#skF_2',C_158) ),
    inference(resolution,[status(thm)],[c_56,c_1922])).

tff(c_68,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_192,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_68])).

tff(c_1960,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1954,c_192])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_172,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_236,plain,(
    ! [B_85,A_86] : k3_tarski(k2_tarski(B_85,A_86)) = k2_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_172])).

tff(c_22,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_355,plain,(
    ! [B_95,A_96] : k2_xboole_0(B_95,A_96) = k2_xboole_0(A_96,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_22])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_987,plain,(
    ! [A_122,B_123] : k4_xboole_0(A_122,k2_xboole_0(B_123,A_122)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_14])).

tff(c_1209,plain,(
    ! [A_129,B_130] : k4_xboole_0(k4_xboole_0(A_129,B_130),A_129) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_987])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1221,plain,(
    ! [A_129,B_130] : k2_xboole_0(A_129,k4_xboole_0(A_129,B_130)) = k2_xboole_0(A_129,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_12])).

tff(c_1270,plain,(
    ! [A_129,B_130] : k2_xboole_0(A_129,k4_xboole_0(A_129,B_130)) = A_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1221])).

tff(c_3587,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1960,c_1270])).

tff(c_157,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_171,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_157])).

tff(c_197,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_207,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_171,c_197])).

tff(c_221,plain,(
    ! [A_83,B_84] : k1_setfam_1(k2_tarski(A_83,B_84)) = k3_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1535,plain,(
    ! [A_139,B_140] : k1_setfam_1(k2_tarski(A_139,B_140)) = k3_xboole_0(B_140,A_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_221])).

tff(c_38,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1541,plain,(
    ! [B_140,A_139] : k3_xboole_0(B_140,A_139) = k3_xboole_0(A_139,B_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_1535,c_38])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_882,plain,(
    ! [A_113,C_114,B_115] :
      ( r1_tarski(A_113,C_114)
      | ~ r1_tarski(B_115,C_114)
      | ~ r1_tarski(A_113,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2954,plain,(
    ! [A_186,A_187,B_188] :
      ( r1_tarski(A_186,A_187)
      | ~ r1_tarski(A_186,k4_xboole_0(A_187,B_188)) ) ),
    inference(resolution,[status(thm)],[c_10,c_882])).

tff(c_3082,plain,(
    ! [A_190,B_191,B_192] : r1_tarski(k4_xboole_0(k4_xboole_0(A_190,B_191),B_192),A_190) ),
    inference(resolution,[status(thm)],[c_10,c_2954])).

tff(c_3263,plain,(
    ! [A_196,B_197,B_198] : r1_tarski(k4_xboole_0(k3_xboole_0(A_196,B_197),B_198),A_196) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3082])).

tff(c_3944,plain,(
    ! [B_214,A_215,B_216] : r1_tarski(k4_xboole_0(k3_xboole_0(B_214,A_215),B_216),A_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_1541,c_3263])).

tff(c_4027,plain,(
    ! [B_217] : r1_tarski(k4_xboole_0('#skF_2',B_217),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_3944])).

tff(c_4034,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1960,c_4027])).

tff(c_42,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2788,plain,(
    ! [A_181,B_182,C_183] :
      ( k4_subset_1(A_181,B_182,C_183) = k2_xboole_0(B_182,C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(A_181))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_15178,plain,(
    ! [B_369,B_370,A_371] :
      ( k4_subset_1(B_369,B_370,A_371) = k2_xboole_0(B_370,A_371)
      | ~ m1_subset_1(B_370,k1_zfmisc_1(B_369))
      | ~ r1_tarski(A_371,B_369) ) ),
    inference(resolution,[status(thm)],[c_42,c_2788])).

tff(c_15463,plain,(
    ! [A_376] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_376) = k2_xboole_0('#skF_2',A_376)
      | ~ r1_tarski(A_376,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_56,c_15178])).

tff(c_15498,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4034,c_15463])).

tff(c_15575,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4153,c_3587,c_15498])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2386,plain,(
    ! [A_171,B_172] :
      ( v4_pre_topc(k2_pre_topc(A_171,B_172),A_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2411,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_2386])).

tff(c_2422,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2411])).

tff(c_15600,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15575,c_2422])).

tff(c_15602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_15600])).

tff(c_15603,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_17751,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17693,c_15603])).

tff(c_15604,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_19030,plain,(
    ! [A_515,B_516] :
      ( r1_tarski(k2_tops_1(A_515,B_516),B_516)
      | ~ v4_pre_topc(B_516,A_515)
      | ~ m1_subset_1(B_516,k1_zfmisc_1(u1_struct_0(A_515)))
      | ~ l1_pre_topc(A_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_19055,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_19030])).

tff(c_19066,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_15604,c_19055])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19073,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_19066,c_8])).

tff(c_15662,plain,(
    ! [A_384,B_385] : k1_setfam_1(k2_tarski(A_384,B_385)) = k3_xboole_0(A_384,B_385) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17173,plain,(
    ! [A_448,B_449] : k1_setfam_1(k2_tarski(A_448,B_449)) = k3_xboole_0(B_449,A_448) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_15662])).

tff(c_17196,plain,(
    ! [B_450,A_451] : k3_xboole_0(B_450,A_451) = k3_xboole_0(A_451,B_450) ),
    inference(superposition,[status(thm),theory(equality)],[c_17173,c_38])).

tff(c_15931,plain,(
    ! [A_401,B_402] : k2_xboole_0(k3_xboole_0(A_401,B_402),k4_xboole_0(A_401,B_402)) = A_401 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_15937,plain,(
    ! [A_401,B_402] : k4_xboole_0(k3_xboole_0(A_401,B_402),A_401) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15931,c_14])).

tff(c_16126,plain,(
    ! [A_409,B_410] : k2_xboole_0(A_409,k4_xboole_0(B_410,A_409)) = k2_xboole_0(A_409,B_410) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16138,plain,(
    ! [A_401,B_402] : k2_xboole_0(A_401,k3_xboole_0(A_401,B_402)) = k2_xboole_0(A_401,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15937,c_16126])).

tff(c_16160,plain,(
    ! [A_401,B_402] : k2_xboole_0(A_401,k3_xboole_0(A_401,B_402)) = A_401 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16138])).

tff(c_17219,plain,(
    ! [A_451,B_450] : k2_xboole_0(A_451,k3_xboole_0(B_450,A_451)) = A_451 ),
    inference(superposition,[status(thm),theory(equality)],[c_17196,c_16160])).

tff(c_22285,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_19073,c_17219])).

tff(c_19751,plain,(
    ! [A_538,B_539] :
      ( k4_subset_1(u1_struct_0(A_538),B_539,k2_tops_1(A_538,B_539)) = k2_pre_topc(A_538,B_539)
      | ~ m1_subset_1(B_539,k1_zfmisc_1(u1_struct_0(A_538)))
      | ~ l1_pre_topc(A_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_19778,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_19751])).

tff(c_19792,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_19778])).

tff(c_17076,plain,(
    ! [A_444,B_445] :
      ( k4_xboole_0(A_444,B_445) = k3_subset_1(A_444,B_445)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(A_444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_17107,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_17076])).

tff(c_34,plain,(
    ! [A_34,B_35] : k6_subset_1(A_34,B_35) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [A_27,B_28] : m1_subset_1(k6_subset_1(A_27,B_28),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,(
    ! [A_27,B_28] : m1_subset_1(k4_xboole_0(A_27,B_28),k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28])).

tff(c_17163,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17107,c_69])).

tff(c_19297,plain,(
    ! [A_524,B_525] :
      ( k2_tops_1(A_524,k3_subset_1(u1_struct_0(A_524),B_525)) = k2_tops_1(A_524,B_525)
      | ~ m1_subset_1(B_525,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ l1_pre_topc(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_19324,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_19297])).

tff(c_19340,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_19324])).

tff(c_44,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k2_tops_1(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_19881,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19340,c_44])).

tff(c_19885,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_17163,c_19881])).

tff(c_40,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19929,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_19885,c_40])).

tff(c_18613,plain,(
    ! [A_500,B_501,C_502] :
      ( k4_subset_1(A_500,B_501,C_502) = k2_xboole_0(B_501,C_502)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(A_500))
      | ~ m1_subset_1(B_501,k1_zfmisc_1(A_500)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_31236,plain,(
    ! [B_679,B_680,A_681] :
      ( k4_subset_1(B_679,B_680,A_681) = k2_xboole_0(B_680,A_681)
      | ~ m1_subset_1(B_680,k1_zfmisc_1(B_679))
      | ~ r1_tarski(A_681,B_679) ) ),
    inference(resolution,[status(thm)],[c_42,c_18613])).

tff(c_31339,plain,(
    ! [A_683] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_683) = k2_xboole_0('#skF_2',A_683)
      | ~ r1_tarski(A_683,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_56,c_31236])).

tff(c_31363,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_19929,c_31339])).

tff(c_31447,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22285,c_19792,c_31363])).

tff(c_48,plain,(
    ! [A_47,B_49] :
      ( k7_subset_1(u1_struct_0(A_47),k2_pre_topc(A_47,B_49),k1_tops_1(A_47,B_49)) = k2_tops_1(A_47,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_31484,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31447,c_48])).

tff(c_31490,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_17693,c_31484])).

tff(c_31492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17751,c_31490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.58/4.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.58/4.68  
% 11.58/4.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.58/4.68  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.58/4.68  
% 11.58/4.68  %Foreground sorts:
% 11.58/4.68  
% 11.58/4.68  
% 11.58/4.68  %Background operators:
% 11.58/4.68  
% 11.58/4.68  
% 11.58/4.68  %Foreground operators:
% 11.58/4.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.58/4.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.58/4.68  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.58/4.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.58/4.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.58/4.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.58/4.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.58/4.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.58/4.68  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.58/4.68  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.58/4.68  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.58/4.68  tff('#skF_2', type, '#skF_2': $i).
% 11.58/4.68  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.58/4.68  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.58/4.68  tff('#skF_1', type, '#skF_1': $i).
% 11.58/4.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.58/4.68  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.58/4.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.58/4.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.58/4.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.58/4.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.58/4.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.58/4.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.58/4.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.58/4.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.58/4.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.58/4.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.58/4.68  
% 11.58/4.71  tff(f_141, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 11.58/4.71  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.58/4.71  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 11.58/4.71  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 11.58/4.71  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.58/4.71  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.58/4.71  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.58/4.71  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 11.58/4.71  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.58/4.71  tff(f_85, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.58/4.71  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.58/4.71  tff(f_81, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.58/4.71  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.58/4.71  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.58/4.71  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.58/4.71  tff(f_73, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.58/4.71  tff(f_99, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 11.58/4.71  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 11.58/4.71  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.58/4.71  tff(f_75, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.58/4.71  tff(f_63, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 11.58/4.71  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 11.58/4.71  tff(f_91, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 11.58/4.71  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 11.58/4.71  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.58/4.71  tff(c_17671, plain, (![A_464, B_465, C_466]: (k7_subset_1(A_464, B_465, C_466)=k4_xboole_0(B_465, C_466) | ~m1_subset_1(B_465, k1_zfmisc_1(A_464)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.58/4.71  tff(c_17693, plain, (![C_466]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_466)=k4_xboole_0('#skF_2', C_466))), inference(resolution, [status(thm)], [c_56, c_17671])).
% 11.58/4.71  tff(c_62, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.58/4.71  tff(c_114, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_62])).
% 11.58/4.71  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.58/4.71  tff(c_4112, plain, (![A_219, B_220]: (k4_subset_1(u1_struct_0(A_219), B_220, k2_tops_1(A_219, B_220))=k2_pre_topc(A_219, B_220) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.58/4.71  tff(c_4139, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_4112])).
% 11.58/4.71  tff(c_4153, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4139])).
% 11.58/4.71  tff(c_1922, plain, (![A_153, B_154, C_155]: (k7_subset_1(A_153, B_154, C_155)=k4_xboole_0(B_154, C_155) | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.58/4.71  tff(c_1954, plain, (![C_158]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_158)=k4_xboole_0('#skF_2', C_158))), inference(resolution, [status(thm)], [c_56, c_1922])).
% 11.58/4.71  tff(c_68, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.58/4.71  tff(c_192, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_114, c_68])).
% 11.58/4.71  tff(c_1960, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1954, c_192])).
% 11.58/4.71  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.58/4.71  tff(c_18, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.58/4.71  tff(c_20, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.58/4.71  tff(c_172, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.58/4.71  tff(c_236, plain, (![B_85, A_86]: (k3_tarski(k2_tarski(B_85, A_86))=k2_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_20, c_172])).
% 11.58/4.71  tff(c_22, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.58/4.71  tff(c_355, plain, (![B_95, A_96]: (k2_xboole_0(B_95, A_96)=k2_xboole_0(A_96, B_95))), inference(superposition, [status(thm), theory('equality')], [c_236, c_22])).
% 11.58/4.71  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.58/4.71  tff(c_987, plain, (![A_122, B_123]: (k4_xboole_0(A_122, k2_xboole_0(B_123, A_122))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_355, c_14])).
% 11.58/4.71  tff(c_1209, plain, (![A_129, B_130]: (k4_xboole_0(k4_xboole_0(A_129, B_130), A_129)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_987])).
% 11.58/4.71  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.58/4.71  tff(c_1221, plain, (![A_129, B_130]: (k2_xboole_0(A_129, k4_xboole_0(A_129, B_130))=k2_xboole_0(A_129, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1209, c_12])).
% 11.58/4.71  tff(c_1270, plain, (![A_129, B_130]: (k2_xboole_0(A_129, k4_xboole_0(A_129, B_130))=A_129)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1221])).
% 11.58/4.71  tff(c_3587, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1960, c_1270])).
% 11.58/4.71  tff(c_157, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | ~m1_subset_1(A_74, k1_zfmisc_1(B_75)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.58/4.71  tff(c_171, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_157])).
% 11.58/4.71  tff(c_197, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.58/4.71  tff(c_207, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_171, c_197])).
% 11.58/4.71  tff(c_221, plain, (![A_83, B_84]: (k1_setfam_1(k2_tarski(A_83, B_84))=k3_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.58/4.71  tff(c_1535, plain, (![A_139, B_140]: (k1_setfam_1(k2_tarski(A_139, B_140))=k3_xboole_0(B_140, A_139))), inference(superposition, [status(thm), theory('equality')], [c_20, c_221])).
% 11.58/4.71  tff(c_38, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.58/4.71  tff(c_1541, plain, (![B_140, A_139]: (k3_xboole_0(B_140, A_139)=k3_xboole_0(A_139, B_140))), inference(superposition, [status(thm), theory('equality')], [c_1535, c_38])).
% 11.58/4.71  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.58/4.71  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.58/4.71  tff(c_882, plain, (![A_113, C_114, B_115]: (r1_tarski(A_113, C_114) | ~r1_tarski(B_115, C_114) | ~r1_tarski(A_113, B_115))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.58/4.71  tff(c_2954, plain, (![A_186, A_187, B_188]: (r1_tarski(A_186, A_187) | ~r1_tarski(A_186, k4_xboole_0(A_187, B_188)))), inference(resolution, [status(thm)], [c_10, c_882])).
% 11.58/4.71  tff(c_3082, plain, (![A_190, B_191, B_192]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_190, B_191), B_192), A_190))), inference(resolution, [status(thm)], [c_10, c_2954])).
% 11.58/4.71  tff(c_3263, plain, (![A_196, B_197, B_198]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_196, B_197), B_198), A_196))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3082])).
% 11.58/4.71  tff(c_3944, plain, (![B_214, A_215, B_216]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_214, A_215), B_216), A_215))), inference(superposition, [status(thm), theory('equality')], [c_1541, c_3263])).
% 11.58/4.71  tff(c_4027, plain, (![B_217]: (r1_tarski(k4_xboole_0('#skF_2', B_217), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_207, c_3944])).
% 11.58/4.71  tff(c_4034, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1960, c_4027])).
% 11.58/4.71  tff(c_42, plain, (![A_41, B_42]: (m1_subset_1(A_41, k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.58/4.71  tff(c_2788, plain, (![A_181, B_182, C_183]: (k4_subset_1(A_181, B_182, C_183)=k2_xboole_0(B_182, C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(A_181)) | ~m1_subset_1(B_182, k1_zfmisc_1(A_181)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.58/4.71  tff(c_15178, plain, (![B_369, B_370, A_371]: (k4_subset_1(B_369, B_370, A_371)=k2_xboole_0(B_370, A_371) | ~m1_subset_1(B_370, k1_zfmisc_1(B_369)) | ~r1_tarski(A_371, B_369))), inference(resolution, [status(thm)], [c_42, c_2788])).
% 11.58/4.71  tff(c_15463, plain, (![A_376]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_376)=k2_xboole_0('#skF_2', A_376) | ~r1_tarski(A_376, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_56, c_15178])).
% 11.58/4.71  tff(c_15498, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4034, c_15463])).
% 11.58/4.71  tff(c_15575, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4153, c_3587, c_15498])).
% 11.58/4.71  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.58/4.71  tff(c_2386, plain, (![A_171, B_172]: (v4_pre_topc(k2_pre_topc(A_171, B_172), A_171) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.58/4.71  tff(c_2411, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_2386])).
% 11.58/4.71  tff(c_2422, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2411])).
% 11.58/4.71  tff(c_15600, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15575, c_2422])).
% 11.58/4.71  tff(c_15602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_15600])).
% 11.58/4.71  tff(c_15603, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 11.58/4.71  tff(c_17751, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17693, c_15603])).
% 11.58/4.71  tff(c_15604, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 11.58/4.71  tff(c_19030, plain, (![A_515, B_516]: (r1_tarski(k2_tops_1(A_515, B_516), B_516) | ~v4_pre_topc(B_516, A_515) | ~m1_subset_1(B_516, k1_zfmisc_1(u1_struct_0(A_515))) | ~l1_pre_topc(A_515))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.58/4.71  tff(c_19055, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_19030])).
% 11.58/4.71  tff(c_19066, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_15604, c_19055])).
% 11.58/4.71  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.58/4.71  tff(c_19073, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_19066, c_8])).
% 11.58/4.71  tff(c_15662, plain, (![A_384, B_385]: (k1_setfam_1(k2_tarski(A_384, B_385))=k3_xboole_0(A_384, B_385))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.58/4.71  tff(c_17173, plain, (![A_448, B_449]: (k1_setfam_1(k2_tarski(A_448, B_449))=k3_xboole_0(B_449, A_448))), inference(superposition, [status(thm), theory('equality')], [c_20, c_15662])).
% 11.58/4.71  tff(c_17196, plain, (![B_450, A_451]: (k3_xboole_0(B_450, A_451)=k3_xboole_0(A_451, B_450))), inference(superposition, [status(thm), theory('equality')], [c_17173, c_38])).
% 11.58/4.71  tff(c_15931, plain, (![A_401, B_402]: (k2_xboole_0(k3_xboole_0(A_401, B_402), k4_xboole_0(A_401, B_402))=A_401)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.58/4.71  tff(c_15937, plain, (![A_401, B_402]: (k4_xboole_0(k3_xboole_0(A_401, B_402), A_401)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15931, c_14])).
% 11.58/4.71  tff(c_16126, plain, (![A_409, B_410]: (k2_xboole_0(A_409, k4_xboole_0(B_410, A_409))=k2_xboole_0(A_409, B_410))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.58/4.71  tff(c_16138, plain, (![A_401, B_402]: (k2_xboole_0(A_401, k3_xboole_0(A_401, B_402))=k2_xboole_0(A_401, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15937, c_16126])).
% 11.58/4.71  tff(c_16160, plain, (![A_401, B_402]: (k2_xboole_0(A_401, k3_xboole_0(A_401, B_402))=A_401)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16138])).
% 11.58/4.71  tff(c_17219, plain, (![A_451, B_450]: (k2_xboole_0(A_451, k3_xboole_0(B_450, A_451))=A_451)), inference(superposition, [status(thm), theory('equality')], [c_17196, c_16160])).
% 11.58/4.71  tff(c_22285, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_19073, c_17219])).
% 11.58/4.71  tff(c_19751, plain, (![A_538, B_539]: (k4_subset_1(u1_struct_0(A_538), B_539, k2_tops_1(A_538, B_539))=k2_pre_topc(A_538, B_539) | ~m1_subset_1(B_539, k1_zfmisc_1(u1_struct_0(A_538))) | ~l1_pre_topc(A_538))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.58/4.71  tff(c_19778, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_19751])).
% 11.58/4.71  tff(c_19792, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_19778])).
% 11.58/4.71  tff(c_17076, plain, (![A_444, B_445]: (k4_xboole_0(A_444, B_445)=k3_subset_1(A_444, B_445) | ~m1_subset_1(B_445, k1_zfmisc_1(A_444)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.58/4.71  tff(c_17107, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_56, c_17076])).
% 11.58/4.71  tff(c_34, plain, (![A_34, B_35]: (k6_subset_1(A_34, B_35)=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.58/4.71  tff(c_28, plain, (![A_27, B_28]: (m1_subset_1(k6_subset_1(A_27, B_28), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.58/4.71  tff(c_69, plain, (![A_27, B_28]: (m1_subset_1(k4_xboole_0(A_27, B_28), k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28])).
% 11.58/4.71  tff(c_17163, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_17107, c_69])).
% 11.58/4.71  tff(c_19297, plain, (![A_524, B_525]: (k2_tops_1(A_524, k3_subset_1(u1_struct_0(A_524), B_525))=k2_tops_1(A_524, B_525) | ~m1_subset_1(B_525, k1_zfmisc_1(u1_struct_0(A_524))) | ~l1_pre_topc(A_524))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.58/4.71  tff(c_19324, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_19297])).
% 11.58/4.71  tff(c_19340, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_19324])).
% 11.58/4.71  tff(c_44, plain, (![A_43, B_44]: (m1_subset_1(k2_tops_1(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.58/4.71  tff(c_19881, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_19340, c_44])).
% 11.58/4.71  tff(c_19885, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_17163, c_19881])).
% 11.58/4.71  tff(c_40, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.58/4.71  tff(c_19929, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_19885, c_40])).
% 11.58/4.71  tff(c_18613, plain, (![A_500, B_501, C_502]: (k4_subset_1(A_500, B_501, C_502)=k2_xboole_0(B_501, C_502) | ~m1_subset_1(C_502, k1_zfmisc_1(A_500)) | ~m1_subset_1(B_501, k1_zfmisc_1(A_500)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.58/4.71  tff(c_31236, plain, (![B_679, B_680, A_681]: (k4_subset_1(B_679, B_680, A_681)=k2_xboole_0(B_680, A_681) | ~m1_subset_1(B_680, k1_zfmisc_1(B_679)) | ~r1_tarski(A_681, B_679))), inference(resolution, [status(thm)], [c_42, c_18613])).
% 11.58/4.71  tff(c_31339, plain, (![A_683]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_683)=k2_xboole_0('#skF_2', A_683) | ~r1_tarski(A_683, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_56, c_31236])).
% 11.58/4.71  tff(c_31363, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_19929, c_31339])).
% 11.58/4.71  tff(c_31447, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22285, c_19792, c_31363])).
% 11.58/4.71  tff(c_48, plain, (![A_47, B_49]: (k7_subset_1(u1_struct_0(A_47), k2_pre_topc(A_47, B_49), k1_tops_1(A_47, B_49))=k2_tops_1(A_47, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.58/4.71  tff(c_31484, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31447, c_48])).
% 11.58/4.71  tff(c_31490, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_17693, c_31484])).
% 11.58/4.71  tff(c_31492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17751, c_31490])).
% 11.58/4.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.58/4.71  
% 11.58/4.71  Inference rules
% 11.58/4.71  ----------------------
% 11.58/4.71  #Ref     : 0
% 11.58/4.71  #Sup     : 7729
% 11.58/4.71  #Fact    : 0
% 11.58/4.71  #Define  : 0
% 11.58/4.71  #Split   : 1
% 11.58/4.71  #Chain   : 0
% 11.58/4.71  #Close   : 0
% 11.58/4.71  
% 11.58/4.71  Ordering : KBO
% 11.58/4.71  
% 11.58/4.71  Simplification rules
% 11.58/4.71  ----------------------
% 11.58/4.71  #Subsume      : 177
% 11.58/4.71  #Demod        : 7738
% 11.58/4.71  #Tautology    : 5753
% 11.58/4.71  #SimpNegUnit  : 3
% 11.58/4.71  #BackRed      : 15
% 11.58/4.71  
% 11.58/4.71  #Partial instantiations: 0
% 11.58/4.71  #Strategies tried      : 1
% 11.58/4.71  
% 11.58/4.71  Timing (in seconds)
% 11.58/4.71  ----------------------
% 11.58/4.71  Preprocessing        : 0.36
% 11.58/4.71  Parsing              : 0.19
% 11.58/4.71  CNF conversion       : 0.02
% 11.58/4.71  Main loop            : 3.56
% 11.58/4.71  Inferencing          : 0.73
% 11.58/4.71  Reduction            : 1.90
% 11.58/4.71  Demodulation         : 1.63
% 11.58/4.71  BG Simplification    : 0.08
% 11.58/4.71  Subsumption          : 0.62
% 11.58/4.71  Abstraction          : 0.14
% 11.58/4.71  MUC search           : 0.00
% 11.58/4.71  Cooper               : 0.00
% 11.58/4.71  Total                : 3.98
% 11.58/4.71  Index Insertion      : 0.00
% 11.58/4.71  Index Deletion       : 0.00
% 11.58/4.71  Index Matching       : 0.00
% 11.58/4.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------

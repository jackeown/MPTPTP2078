%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:30 EST 2020

% Result     : Theorem 8.56s
% Output     : CNFRefutation 8.67s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 283 expanded)
%              Number of leaves         :   46 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  189 ( 509 expanded)
%              Number of equality atoms :   89 ( 180 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_139,negated_conjecture,(
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

tff(f_98,axiom,(
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

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_11480,plain,(
    ! [A_374,B_375,C_376] :
      ( k7_subset_1(A_374,B_375,C_376) = k4_xboole_0(B_375,C_376)
      | ~ m1_subset_1(B_375,k1_zfmisc_1(A_374)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11486,plain,(
    ! [C_376] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_376) = k4_xboole_0('#skF_2',C_376) ),
    inference(resolution,[status(thm)],[c_54,c_11480])).

tff(c_66,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_134,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_228,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3576,plain,(
    ! [B_187,A_188] :
      ( v4_pre_topc(B_187,A_188)
      | k2_pre_topc(A_188,B_187) != B_187
      | ~ v2_pre_topc(A_188)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3586,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_3576])).

tff(c_3591,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_3586])).

tff(c_3592,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_3591])).

tff(c_4442,plain,(
    ! [A_200,B_201] :
      ( k4_subset_1(u1_struct_0(A_200),B_201,k2_tops_1(A_200,B_201)) = k2_pre_topc(A_200,B_201)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4449,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_4442])).

tff(c_4454,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4449])).

tff(c_2098,plain,(
    ! [A_145,B_146,C_147] :
      ( k7_subset_1(A_145,B_146,C_147) = k4_xboole_0(B_146,C_147)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2185,plain,(
    ! [C_150] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_150) = k4_xboole_0('#skF_2',C_150) ),
    inference(resolution,[status(thm)],[c_54,c_2098])).

tff(c_2197,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_2185])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_255,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_135,plain,(
    ! [A_60,B_61] :
      ( k2_xboole_0(A_60,B_61) = B_61
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_163,plain,(
    ! [A_63,B_64] : k2_xboole_0(k4_xboole_0(A_63,B_64),A_63) = A_63 ),
    inference(resolution,[status(thm)],[c_20,c_135])).

tff(c_170,plain,(
    ! [B_64] : k4_xboole_0(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_14])).

tff(c_312,plain,(
    ! [B_77] : k3_xboole_0(k1_xboole_0,B_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_170])).

tff(c_338,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_312])).

tff(c_24,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_287,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_255])).

tff(c_562,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_287])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_229,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_241,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_229])).

tff(c_645,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_663,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_645])).

tff(c_674,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_663])).

tff(c_976,plain,(
    ! [A_106,B_107] : k3_xboole_0(k4_xboole_0(A_106,B_107),A_106) = k4_xboole_0(A_106,B_107) ),
    inference(resolution,[status(thm)],[c_20,c_229])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_992,plain,(
    ! [A_106,B_107] : k5_xboole_0(k4_xboole_0(A_106,B_107),k4_xboole_0(A_106,B_107)) = k4_xboole_0(k4_xboole_0(A_106,B_107),A_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_10])).

tff(c_1063,plain,(
    ! [A_108,B_109] : k4_xboole_0(k4_xboole_0(A_108,B_109),A_108) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_992])).

tff(c_22,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1077,plain,(
    ! [A_108,B_109] : k2_xboole_0(A_108,k4_xboole_0(A_108,B_109)) = k2_xboole_0(A_108,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_22])).

tff(c_1119,plain,(
    ! [A_108,B_109] : k2_xboole_0(A_108,k4_xboole_0(A_108,B_109)) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1077])).

tff(c_2523,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2197,c_1119])).

tff(c_240,plain,(
    ! [A_15,B_16] : k3_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k4_xboole_0(A_15,B_16) ),
    inference(resolution,[status(thm)],[c_20,c_229])).

tff(c_211,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(A_68,B_69)
      | ~ m1_subset_1(A_68,k1_zfmisc_1(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_219,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_211])).

tff(c_239,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_219,c_229])).

tff(c_26,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_271,plain,(
    ! [A_73,B_74] : r1_tarski(k3_xboole_0(A_73,B_74),A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_20])).

tff(c_787,plain,(
    ! [A_97,C_98,B_99] :
      ( r1_tarski(A_97,C_98)
      | ~ r1_tarski(B_99,C_98)
      | ~ r1_tarski(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1474,plain,(
    ! [A_122,A_123,B_124] :
      ( r1_tarski(A_122,A_123)
      | ~ r1_tarski(A_122,k4_xboole_0(A_123,B_124)) ) ),
    inference(resolution,[status(thm)],[c_20,c_787])).

tff(c_1526,plain,(
    ! [A_125,B_126,B_127] : r1_tarski(k3_xboole_0(k4_xboole_0(A_125,B_126),B_127),A_125) ),
    inference(resolution,[status(thm)],[c_271,c_1474])).

tff(c_1848,plain,(
    ! [A_136,B_137,B_138] : r1_tarski(k3_xboole_0(k3_xboole_0(A_136,B_137),B_138),A_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1526])).

tff(c_2015,plain,(
    ! [B_142,A_143,B_144] : r1_tarski(k3_xboole_0(k3_xboole_0(B_142,A_143),B_144),A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1848])).

tff(c_2105,plain,(
    ! [B_148] : r1_tarski(k3_xboole_0('#skF_2',B_148),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_2015])).

tff(c_2146,plain,(
    ! [B_149] : r1_tarski(k3_xboole_0(B_149,'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2105])).

tff(c_2160,plain,(
    ! [B_16] : r1_tarski(k4_xboole_0('#skF_2',B_16),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_2146])).

tff(c_2508,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2197,c_2160])).

tff(c_40,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3161,plain,(
    ! [A_176,B_177,C_178] :
      ( k4_subset_1(A_176,B_177,C_178) = k2_xboole_0(B_177,C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(A_176))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(A_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9140,plain,(
    ! [B_269,B_270,A_271] :
      ( k4_subset_1(B_269,B_270,A_271) = k2_xboole_0(B_270,A_271)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(B_269))
      | ~ r1_tarski(A_271,B_269) ) ),
    inference(resolution,[status(thm)],[c_40,c_3161])).

tff(c_9153,plain,(
    ! [A_272] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_272) = k2_xboole_0('#skF_2',A_272)
      | ~ r1_tarski(A_272,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_54,c_9140])).

tff(c_9172,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2508,c_9153])).

tff(c_9256,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4454,c_2523,c_9172])).

tff(c_9258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3592,c_9256])).

tff(c_9259,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_9562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_9259])).

tff(c_9563,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_9664,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_60])).

tff(c_11568,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11486,c_9664])).

tff(c_12544,plain,(
    ! [A_406,B_407] :
      ( r1_tarski(k2_tops_1(A_406,B_407),B_407)
      | ~ v4_pre_topc(B_407,A_406)
      | ~ m1_subset_1(B_407,k1_zfmisc_1(u1_struct_0(A_406)))
      | ~ l1_pre_topc(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12551,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_12544])).

tff(c_12556,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9563,c_12551])).

tff(c_13203,plain,(
    ! [A_421,B_422] :
      ( k7_subset_1(u1_struct_0(A_421),B_422,k2_tops_1(A_421,B_422)) = k1_tops_1(A_421,B_422)
      | ~ m1_subset_1(B_422,k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ l1_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_13210,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_13203])).

tff(c_13215,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11486,c_13210])).

tff(c_10673,plain,(
    ! [A_344,B_345] :
      ( k4_xboole_0(A_344,B_345) = k3_subset_1(A_344,B_345)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(A_344)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13632,plain,(
    ! [B_429,A_430] :
      ( k4_xboole_0(B_429,A_430) = k3_subset_1(B_429,A_430)
      | ~ r1_tarski(A_430,B_429) ) ),
    inference(resolution,[status(thm)],[c_40,c_10673])).

tff(c_13668,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12556,c_13632])).

tff(c_13741,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13215,c_13668])).

tff(c_11017,plain,(
    ! [A_356,B_357] :
      ( k3_subset_1(A_356,k3_subset_1(A_356,B_357)) = B_357
      | ~ m1_subset_1(B_357,k1_zfmisc_1(A_356)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14294,plain,(
    ! [B_442,A_443] :
      ( k3_subset_1(B_442,k3_subset_1(B_442,A_443)) = A_443
      | ~ r1_tarski(A_443,B_442) ) ),
    inference(resolution,[status(thm)],[c_40,c_11017])).

tff(c_14315,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13741,c_14294])).

tff(c_14338,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12556,c_14315])).

tff(c_9639,plain,(
    ! [A_296,B_297] :
      ( k3_xboole_0(A_296,B_297) = A_296
      | ~ r1_tarski(A_296,B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9646,plain,(
    ! [A_15,B_16] : k3_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k4_xboole_0(A_15,B_16) ),
    inference(resolution,[status(thm)],[c_20,c_9639])).

tff(c_13251,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13215,c_9646])).

tff(c_13268,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13215,c_2,c_13251])).

tff(c_13725,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_subset_1(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(resolution,[status(thm)],[c_20,c_13632])).

tff(c_13764,plain,(
    ! [A_15,B_16] : k3_subset_1(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_13725])).

tff(c_14312,plain,(
    ! [A_15,B_16] :
      ( k3_subset_1(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16)
      | ~ r1_tarski(k4_xboole_0(A_15,B_16),A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13764,c_14294])).

tff(c_14964,plain,(
    ! [A_450,B_451] : k3_subset_1(A_450,k3_xboole_0(A_450,B_451)) = k4_xboole_0(A_450,B_451) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14312])).

tff(c_14985,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13268,c_14964])).

tff(c_15026,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14338,c_14985])).

tff(c_15028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11568,c_15026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.56/2.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.56/2.92  
% 8.56/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.56/2.92  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.56/2.92  
% 8.56/2.92  %Foreground sorts:
% 8.56/2.92  
% 8.56/2.92  
% 8.56/2.92  %Background operators:
% 8.56/2.92  
% 8.56/2.92  
% 8.56/2.92  %Foreground operators:
% 8.56/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.56/2.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.56/2.92  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.56/2.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.56/2.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.56/2.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.56/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.56/2.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.56/2.92  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.56/2.92  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.56/2.92  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.56/2.92  tff('#skF_2', type, '#skF_2': $i).
% 8.56/2.92  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.56/2.92  tff('#skF_1', type, '#skF_1': $i).
% 8.56/2.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.56/2.92  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.56/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.56/2.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.56/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.56/2.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.56/2.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.56/2.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.56/2.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.56/2.92  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.56/2.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.56/2.92  
% 8.67/2.94  tff(f_139, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 8.67/2.94  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.67/2.94  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.67/2.94  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 8.67/2.94  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.67/2.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.67/2.94  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.67/2.94  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.67/2.94  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.67/2.94  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.67/2.94  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.67/2.94  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.67/2.94  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.67/2.94  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.67/2.94  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.67/2.94  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.67/2.94  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.67/2.94  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 8.67/2.94  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 8.67/2.94  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 8.67/2.94  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.67/2.94  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.94  tff(c_11480, plain, (![A_374, B_375, C_376]: (k7_subset_1(A_374, B_375, C_376)=k4_xboole_0(B_375, C_376) | ~m1_subset_1(B_375, k1_zfmisc_1(A_374)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.67/2.94  tff(c_11486, plain, (![C_376]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_376)=k4_xboole_0('#skF_2', C_376))), inference(resolution, [status(thm)], [c_54, c_11480])).
% 8.67/2.94  tff(c_66, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.94  tff(c_134, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_66])).
% 8.67/2.94  tff(c_60, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.94  tff(c_228, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_60])).
% 8.67/2.94  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.94  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.94  tff(c_3576, plain, (![B_187, A_188]: (v4_pre_topc(B_187, A_188) | k2_pre_topc(A_188, B_187)!=B_187 | ~v2_pre_topc(A_188) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.67/2.94  tff(c_3586, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_3576])).
% 8.67/2.94  tff(c_3591, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_3586])).
% 8.67/2.94  tff(c_3592, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_228, c_3591])).
% 8.67/2.94  tff(c_4442, plain, (![A_200, B_201]: (k4_subset_1(u1_struct_0(A_200), B_201, k2_tops_1(A_200, B_201))=k2_pre_topc(A_200, B_201) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.67/2.94  tff(c_4449, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_4442])).
% 8.67/2.94  tff(c_4454, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4449])).
% 8.67/2.94  tff(c_2098, plain, (![A_145, B_146, C_147]: (k7_subset_1(A_145, B_146, C_147)=k4_xboole_0(B_146, C_147) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.67/2.94  tff(c_2185, plain, (![C_150]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_150)=k4_xboole_0('#skF_2', C_150))), inference(resolution, [status(thm)], [c_54, c_2098])).
% 8.67/2.94  tff(c_2197, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_134, c_2185])).
% 8.67/2.94  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.67/2.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.67/2.94  tff(c_255, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.67/2.94  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.67/2.94  tff(c_135, plain, (![A_60, B_61]: (k2_xboole_0(A_60, B_61)=B_61 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.67/2.94  tff(c_163, plain, (![A_63, B_64]: (k2_xboole_0(k4_xboole_0(A_63, B_64), A_63)=A_63)), inference(resolution, [status(thm)], [c_20, c_135])).
% 8.67/2.94  tff(c_170, plain, (![B_64]: (k4_xboole_0(k1_xboole_0, B_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_163, c_14])).
% 8.67/2.94  tff(c_312, plain, (![B_77]: (k3_xboole_0(k1_xboole_0, B_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_255, c_170])).
% 8.67/2.94  tff(c_338, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_312])).
% 8.67/2.94  tff(c_24, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.67/2.94  tff(c_287, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_255])).
% 8.67/2.94  tff(c_562, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_338, c_287])).
% 8.67/2.94  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.67/2.94  tff(c_229, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.67/2.94  tff(c_241, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_229])).
% 8.67/2.94  tff(c_645, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.67/2.94  tff(c_663, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_241, c_645])).
% 8.67/2.94  tff(c_674, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_562, c_663])).
% 8.67/2.94  tff(c_976, plain, (![A_106, B_107]: (k3_xboole_0(k4_xboole_0(A_106, B_107), A_106)=k4_xboole_0(A_106, B_107))), inference(resolution, [status(thm)], [c_20, c_229])).
% 8.67/2.94  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.67/2.94  tff(c_992, plain, (![A_106, B_107]: (k5_xboole_0(k4_xboole_0(A_106, B_107), k4_xboole_0(A_106, B_107))=k4_xboole_0(k4_xboole_0(A_106, B_107), A_106))), inference(superposition, [status(thm), theory('equality')], [c_976, c_10])).
% 8.67/2.94  tff(c_1063, plain, (![A_108, B_109]: (k4_xboole_0(k4_xboole_0(A_108, B_109), A_108)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_674, c_992])).
% 8.67/2.94  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.67/2.94  tff(c_1077, plain, (![A_108, B_109]: (k2_xboole_0(A_108, k4_xboole_0(A_108, B_109))=k2_xboole_0(A_108, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1063, c_22])).
% 8.67/2.94  tff(c_1119, plain, (![A_108, B_109]: (k2_xboole_0(A_108, k4_xboole_0(A_108, B_109))=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1077])).
% 8.67/2.94  tff(c_2523, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2197, c_1119])).
% 8.67/2.94  tff(c_240, plain, (![A_15, B_16]: (k3_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k4_xboole_0(A_15, B_16))), inference(resolution, [status(thm)], [c_20, c_229])).
% 8.67/2.94  tff(c_211, plain, (![A_68, B_69]: (r1_tarski(A_68, B_69) | ~m1_subset_1(A_68, k1_zfmisc_1(B_69)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.67/2.94  tff(c_219, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_211])).
% 8.67/2.94  tff(c_239, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_219, c_229])).
% 8.67/2.94  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.67/2.94  tff(c_271, plain, (![A_73, B_74]: (r1_tarski(k3_xboole_0(A_73, B_74), A_73))), inference(superposition, [status(thm), theory('equality')], [c_255, c_20])).
% 8.67/2.94  tff(c_787, plain, (![A_97, C_98, B_99]: (r1_tarski(A_97, C_98) | ~r1_tarski(B_99, C_98) | ~r1_tarski(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.67/2.94  tff(c_1474, plain, (![A_122, A_123, B_124]: (r1_tarski(A_122, A_123) | ~r1_tarski(A_122, k4_xboole_0(A_123, B_124)))), inference(resolution, [status(thm)], [c_20, c_787])).
% 8.67/2.94  tff(c_1526, plain, (![A_125, B_126, B_127]: (r1_tarski(k3_xboole_0(k4_xboole_0(A_125, B_126), B_127), A_125))), inference(resolution, [status(thm)], [c_271, c_1474])).
% 8.67/2.94  tff(c_1848, plain, (![A_136, B_137, B_138]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_136, B_137), B_138), A_136))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1526])).
% 8.67/2.94  tff(c_2015, plain, (![B_142, A_143, B_144]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_142, A_143), B_144), A_143))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1848])).
% 8.67/2.94  tff(c_2105, plain, (![B_148]: (r1_tarski(k3_xboole_0('#skF_2', B_148), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_239, c_2015])).
% 8.67/2.94  tff(c_2146, plain, (![B_149]: (r1_tarski(k3_xboole_0(B_149, '#skF_2'), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2105])).
% 8.67/2.94  tff(c_2160, plain, (![B_16]: (r1_tarski(k4_xboole_0('#skF_2', B_16), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_240, c_2146])).
% 8.67/2.94  tff(c_2508, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2197, c_2160])).
% 8.67/2.94  tff(c_40, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.67/2.94  tff(c_3161, plain, (![A_176, B_177, C_178]: (k4_subset_1(A_176, B_177, C_178)=k2_xboole_0(B_177, C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(A_176)) | ~m1_subset_1(B_177, k1_zfmisc_1(A_176)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.67/2.94  tff(c_9140, plain, (![B_269, B_270, A_271]: (k4_subset_1(B_269, B_270, A_271)=k2_xboole_0(B_270, A_271) | ~m1_subset_1(B_270, k1_zfmisc_1(B_269)) | ~r1_tarski(A_271, B_269))), inference(resolution, [status(thm)], [c_40, c_3161])).
% 8.67/2.94  tff(c_9153, plain, (![A_272]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_272)=k2_xboole_0('#skF_2', A_272) | ~r1_tarski(A_272, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_9140])).
% 8.67/2.94  tff(c_9172, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2508, c_9153])).
% 8.67/2.94  tff(c_9256, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4454, c_2523, c_9172])).
% 8.67/2.94  tff(c_9258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3592, c_9256])).
% 8.67/2.94  tff(c_9259, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 8.67/2.94  tff(c_9562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_9259])).
% 8.67/2.94  tff(c_9563, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 8.67/2.94  tff(c_9664, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_60])).
% 8.67/2.94  tff(c_11568, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11486, c_9664])).
% 8.67/2.94  tff(c_12544, plain, (![A_406, B_407]: (r1_tarski(k2_tops_1(A_406, B_407), B_407) | ~v4_pre_topc(B_407, A_406) | ~m1_subset_1(B_407, k1_zfmisc_1(u1_struct_0(A_406))) | ~l1_pre_topc(A_406))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.67/2.94  tff(c_12551, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_12544])).
% 8.67/2.94  tff(c_12556, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_9563, c_12551])).
% 8.67/2.94  tff(c_13203, plain, (![A_421, B_422]: (k7_subset_1(u1_struct_0(A_421), B_422, k2_tops_1(A_421, B_422))=k1_tops_1(A_421, B_422) | ~m1_subset_1(B_422, k1_zfmisc_1(u1_struct_0(A_421))) | ~l1_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.67/2.94  tff(c_13210, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_13203])).
% 8.67/2.94  tff(c_13215, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_11486, c_13210])).
% 8.67/2.94  tff(c_10673, plain, (![A_344, B_345]: (k4_xboole_0(A_344, B_345)=k3_subset_1(A_344, B_345) | ~m1_subset_1(B_345, k1_zfmisc_1(A_344)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.67/2.94  tff(c_13632, plain, (![B_429, A_430]: (k4_xboole_0(B_429, A_430)=k3_subset_1(B_429, A_430) | ~r1_tarski(A_430, B_429))), inference(resolution, [status(thm)], [c_40, c_10673])).
% 8.67/2.94  tff(c_13668, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12556, c_13632])).
% 8.67/2.94  tff(c_13741, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13215, c_13668])).
% 8.67/2.94  tff(c_11017, plain, (![A_356, B_357]: (k3_subset_1(A_356, k3_subset_1(A_356, B_357))=B_357 | ~m1_subset_1(B_357, k1_zfmisc_1(A_356)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.67/2.94  tff(c_14294, plain, (![B_442, A_443]: (k3_subset_1(B_442, k3_subset_1(B_442, A_443))=A_443 | ~r1_tarski(A_443, B_442))), inference(resolution, [status(thm)], [c_40, c_11017])).
% 8.67/2.94  tff(c_14315, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13741, c_14294])).
% 8.67/2.94  tff(c_14338, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12556, c_14315])).
% 8.67/2.94  tff(c_9639, plain, (![A_296, B_297]: (k3_xboole_0(A_296, B_297)=A_296 | ~r1_tarski(A_296, B_297))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.67/2.94  tff(c_9646, plain, (![A_15, B_16]: (k3_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k4_xboole_0(A_15, B_16))), inference(resolution, [status(thm)], [c_20, c_9639])).
% 8.67/2.94  tff(c_13251, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13215, c_9646])).
% 8.67/2.94  tff(c_13268, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13215, c_2, c_13251])).
% 8.67/2.94  tff(c_13725, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_subset_1(A_15, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_20, c_13632])).
% 8.67/2.94  tff(c_13764, plain, (![A_15, B_16]: (k3_subset_1(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_13725])).
% 8.67/2.94  tff(c_14312, plain, (![A_15, B_16]: (k3_subset_1(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16) | ~r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_13764, c_14294])).
% 8.67/2.94  tff(c_14964, plain, (![A_450, B_451]: (k3_subset_1(A_450, k3_xboole_0(A_450, B_451))=k4_xboole_0(A_450, B_451))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14312])).
% 8.67/2.94  tff(c_14985, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13268, c_14964])).
% 8.67/2.94  tff(c_15026, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14338, c_14985])).
% 8.67/2.94  tff(c_15028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11568, c_15026])).
% 8.67/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.67/2.94  
% 8.67/2.94  Inference rules
% 8.67/2.94  ----------------------
% 8.67/2.94  #Ref     : 0
% 8.67/2.94  #Sup     : 3656
% 8.67/2.94  #Fact    : 0
% 8.67/2.94  #Define  : 0
% 8.67/2.94  #Split   : 4
% 8.67/2.94  #Chain   : 0
% 8.67/2.94  #Close   : 0
% 8.67/2.94  
% 8.67/2.94  Ordering : KBO
% 8.67/2.94  
% 8.67/2.94  Simplification rules
% 8.67/2.94  ----------------------
% 8.67/2.94  #Subsume      : 128
% 8.67/2.94  #Demod        : 2971
% 8.67/2.94  #Tautology    : 2421
% 8.67/2.94  #SimpNegUnit  : 4
% 8.67/2.94  #BackRed      : 1
% 8.67/2.94  
% 8.67/2.94  #Partial instantiations: 0
% 8.67/2.94  #Strategies tried      : 1
% 8.67/2.94  
% 8.67/2.94  Timing (in seconds)
% 8.67/2.94  ----------------------
% 8.67/2.95  Preprocessing        : 0.36
% 8.67/2.95  Parsing              : 0.20
% 8.67/2.95  CNF conversion       : 0.02
% 8.67/2.95  Main loop            : 1.76
% 8.67/2.95  Inferencing          : 0.48
% 8.67/2.95  Reduction            : 0.80
% 8.67/2.95  Demodulation         : 0.66
% 8.67/2.95  BG Simplification    : 0.05
% 8.67/2.95  Subsumption          : 0.29
% 8.67/2.95  Abstraction          : 0.08
% 8.67/2.95  MUC search           : 0.00
% 8.67/2.95  Cooper               : 0.00
% 8.67/2.95  Total                : 2.17
% 8.67/2.95  Index Insertion      : 0.00
% 8.67/2.95  Index Deletion       : 0.00
% 8.67/2.95  Index Matching       : 0.00
% 8.67/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------

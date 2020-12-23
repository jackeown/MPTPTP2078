%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:12 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 300 expanded)
%              Number of leaves         :   46 ( 119 expanded)
%              Depth                    :   21
%              Number of atoms          :  167 ( 438 expanded)
%              Number of equality atoms :   92 ( 229 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_92,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6051,plain,(
    ! [A_267,B_268,C_269] :
      ( k7_subset_1(A_267,B_268,C_269) = k4_xboole_0(B_268,C_269)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(A_267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6054,plain,(
    ! [C_269] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_269) = k4_xboole_0('#skF_3',C_269) ),
    inference(resolution,[status(thm)],[c_52,c_6051])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_120,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1476,plain,(
    ! [B_139,A_140] :
      ( v4_pre_topc(B_139,A_140)
      | k2_pre_topc(A_140,B_139) != B_139
      | ~ v2_pre_topc(A_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1482,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1476])).

tff(c_1486,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_1482])).

tff(c_1487,plain,(
    k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_1486])).

tff(c_1712,plain,(
    ! [A_147,B_148] :
      ( k4_subset_1(u1_struct_0(A_147),B_148,k2_tops_1(A_147,B_148)) = k2_pre_topc(A_147,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1716,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1712])).

tff(c_1720,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1716])).

tff(c_18,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_479,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_238,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(B_68,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_136])).

tff(c_32,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_266,plain,(
    ! [B_69,A_70] : k2_xboole_0(B_69,A_70) = k2_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_32])).

tff(c_282,plain,(
    ! [A_70] : k2_xboole_0(k1_xboole_0,A_70) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_18])).

tff(c_22,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_207,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_216,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = k2_xboole_0(k1_xboole_0,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_207])).

tff(c_313,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_216])).

tff(c_506,plain,(
    ! [B_87] : k4_xboole_0(k1_xboole_0,B_87) = k3_xboole_0(k1_xboole_0,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_313])).

tff(c_16,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(k4_xboole_0(A_10,C_12),B_11)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_527,plain,(
    ! [B_87,B_11] :
      ( r1_tarski(k3_xboole_0(k1_xboole_0,B_87),B_11)
      | ~ r1_tarski(k1_xboole_0,B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_16])).

tff(c_598,plain,(
    ! [B_91,B_92] : r1_tarski(k3_xboole_0(k1_xboole_0,B_91),B_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_527])).

tff(c_567,plain,(
    ! [B_88,A_89] :
      ( B_88 = A_89
      | ~ r1_tarski(B_88,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_579,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_567])).

tff(c_615,plain,(
    ! [B_91] : k3_xboole_0(k1_xboole_0,B_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_598,c_579])).

tff(c_486,plain,(
    ! [B_86] : k4_xboole_0(k1_xboole_0,B_86) = k3_xboole_0(k1_xboole_0,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_313])).

tff(c_651,plain,(
    ! [B_94] : k4_xboole_0(k1_xboole_0,B_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_486])).

tff(c_28,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_674,plain,(
    ! [B_94] : k5_xboole_0(B_94,k1_xboole_0) = k2_xboole_0(B_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_28])).

tff(c_704,plain,(
    ! [B_94] : k5_xboole_0(B_94,k1_xboole_0) = B_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_674])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_261,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_64])).

tff(c_778,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_subset_1(A_100,B_101,C_102) = k4_xboole_0(B_101,C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_920,plain,(
    ! [C_109] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_109) = k4_xboole_0('#skF_3',C_109) ),
    inference(resolution,[status(thm)],[c_52,c_778])).

tff(c_932,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_920])).

tff(c_121,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_151,plain,(
    ! [B_60,A_61] : k1_setfam_1(k2_tarski(B_60,A_61)) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_121])).

tff(c_38,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_157,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,A_61) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_38])).

tff(c_622,plain,(
    ! [B_93] : k3_xboole_0(k1_xboole_0,B_93) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_598,c_579])).

tff(c_646,plain,(
    ! [A_61] : k3_xboole_0(A_61,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_622])).

tff(c_402,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_426,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_402])).

tff(c_736,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_426])).

tff(c_783,plain,(
    ! [A_103] : k4_xboole_0(A_103,A_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_426])).

tff(c_26,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_791,plain,(
    ! [A_103] : k4_xboole_0(A_103,k1_xboole_0) = k3_xboole_0(A_103,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_26])).

tff(c_822,plain,(
    ! [A_104] : k3_xboole_0(A_104,A_104) = A_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_791])).

tff(c_14,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_836,plain,(
    ! [A_104] : k5_xboole_0(A_104,A_104) = k4_xboole_0(A_104,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_14])).

tff(c_854,plain,(
    ! [A_104] : k5_xboole_0(A_104,A_104) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_836])).

tff(c_24,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_405,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,k4_xboole_0(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_26])).

tff(c_427,plain,(
    ! [A_80,B_81] : k3_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_405])).

tff(c_1241,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k3_xboole_0(B_132,A_131)) = k4_xboole_0(A_131,B_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_479])).

tff(c_1261,plain,(
    ! [A_80,B_81] : k5_xboole_0(k4_xboole_0(A_80,B_81),k4_xboole_0(A_80,B_81)) = k4_xboole_0(k4_xboole_0(A_80,B_81),A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_1241])).

tff(c_1360,plain,(
    ! [A_135,B_136] : k4_xboole_0(k4_xboole_0(A_135,B_136),A_135) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_1261])).

tff(c_1395,plain,(
    k4_xboole_0(k2_tops_1('#skF_2','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_1360])).

tff(c_1640,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_28])).

tff(c_1649,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_1640])).

tff(c_46,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k2_tops_1(A_39,B_40),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1163,plain,(
    ! [A_125,B_126,C_127] :
      ( k4_subset_1(A_125,B_126,C_127) = k2_xboole_0(B_126,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4707,plain,(
    ! [A_209,B_210,B_211] :
      ( k4_subset_1(u1_struct_0(A_209),B_210,k2_tops_1(A_209,B_211)) = k2_xboole_0(B_210,k2_tops_1(A_209,B_211))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(resolution,[status(thm)],[c_46,c_1163])).

tff(c_4711,plain,(
    ! [B_211] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_211)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_211))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_4707])).

tff(c_5370,plain,(
    ! [B_221] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_221)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_221))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4711])).

tff(c_5377,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_5370])).

tff(c_5382,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_1649,c_5377])).

tff(c_5384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1487,c_5382])).

tff(c_5385,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6130,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6054,c_5385])).

tff(c_5386,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6344,plain,(
    ! [A_288,B_289] :
      ( k2_pre_topc(A_288,B_289) = B_289
      | ~ v4_pre_topc(B_289,A_288)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6350,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_6344])).

tff(c_6354,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5386,c_6350])).

tff(c_7744,plain,(
    ! [A_327,B_328] :
      ( k7_subset_1(u1_struct_0(A_327),k2_pre_topc(A_327,B_328),k1_tops_1(A_327,B_328)) = k2_tops_1(A_327,B_328)
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ l1_pre_topc(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7753,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6354,c_7744])).

tff(c_7757,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_6054,c_7753])).

tff(c_7759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6130,c_7757])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.20  
% 5.74/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.20  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.74/2.20  
% 5.74/2.20  %Foreground sorts:
% 5.74/2.20  
% 5.74/2.20  
% 5.74/2.20  %Background operators:
% 5.74/2.20  
% 5.74/2.20  
% 5.74/2.20  %Foreground operators:
% 5.74/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.74/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.74/2.20  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.74/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.74/2.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.74/2.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.74/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.74/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.74/2.20  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.74/2.20  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.74/2.20  tff('#skF_2', type, '#skF_2': $i).
% 5.74/2.20  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.74/2.20  tff('#skF_3', type, '#skF_3': $i).
% 5.74/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.74/2.20  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.74/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.74/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.74/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.74/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.74/2.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.74/2.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.74/2.20  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.74/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.74/2.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.74/2.20  
% 5.74/2.22  tff(f_124, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.74/2.22  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.74/2.22  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.74/2.22  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.74/2.22  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.74/2.22  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.74/2.22  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.74/2.22  tff(f_58, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.74/2.22  tff(f_60, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.74/2.22  tff(f_50, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.74/2.22  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.74/2.22  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 5.74/2.22  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.74/2.22  tff(f_72, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.74/2.22  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.74/2.22  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.74/2.22  tff(f_98, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.74/2.22  tff(f_66, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.74/2.22  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.74/2.22  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.74/2.22  tff(c_6051, plain, (![A_267, B_268, C_269]: (k7_subset_1(A_267, B_268, C_269)=k4_xboole_0(B_268, C_269) | ~m1_subset_1(B_268, k1_zfmisc_1(A_267)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.74/2.22  tff(c_6054, plain, (![C_269]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_269)=k4_xboole_0('#skF_3', C_269))), inference(resolution, [status(thm)], [c_52, c_6051])).
% 5.74/2.22  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.74/2.22  tff(c_120, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 5.74/2.22  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.74/2.22  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.74/2.22  tff(c_1476, plain, (![B_139, A_140]: (v4_pre_topc(B_139, A_140) | k2_pre_topc(A_140, B_139)!=B_139 | ~v2_pre_topc(A_140) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.74/2.22  tff(c_1482, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3' | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1476])).
% 5.74/2.22  tff(c_1486, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_1482])).
% 5.74/2.22  tff(c_1487, plain, (k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_120, c_1486])).
% 5.74/2.22  tff(c_1712, plain, (![A_147, B_148]: (k4_subset_1(u1_struct_0(A_147), B_148, k2_tops_1(A_147, B_148))=k2_pre_topc(A_147, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.74/2.22  tff(c_1716, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1712])).
% 5.74/2.22  tff(c_1720, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1716])).
% 5.74/2.22  tff(c_18, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.74/2.22  tff(c_20, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.74/2.22  tff(c_479, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.74/2.22  tff(c_30, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.74/2.22  tff(c_136, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.74/2.22  tff(c_238, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(B_68, A_67))), inference(superposition, [status(thm), theory('equality')], [c_30, c_136])).
% 5.74/2.22  tff(c_32, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.74/2.22  tff(c_266, plain, (![B_69, A_70]: (k2_xboole_0(B_69, A_70)=k2_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_238, c_32])).
% 5.74/2.22  tff(c_282, plain, (![A_70]: (k2_xboole_0(k1_xboole_0, A_70)=A_70)), inference(superposition, [status(thm), theory('equality')], [c_266, c_18])).
% 5.74/2.22  tff(c_22, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.74/2.22  tff(c_207, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.74/2.22  tff(c_216, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=k2_xboole_0(k1_xboole_0, A_15))), inference(superposition, [status(thm), theory('equality')], [c_22, c_207])).
% 5.74/2.22  tff(c_313, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_282, c_216])).
% 5.74/2.22  tff(c_506, plain, (![B_87]: (k4_xboole_0(k1_xboole_0, B_87)=k3_xboole_0(k1_xboole_0, B_87))), inference(superposition, [status(thm), theory('equality')], [c_479, c_313])).
% 5.74/2.22  tff(c_16, plain, (![A_10, C_12, B_11]: (r1_tarski(k4_xboole_0(A_10, C_12), B_11) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.74/2.22  tff(c_527, plain, (![B_87, B_11]: (r1_tarski(k3_xboole_0(k1_xboole_0, B_87), B_11) | ~r1_tarski(k1_xboole_0, B_11))), inference(superposition, [status(thm), theory('equality')], [c_506, c_16])).
% 5.74/2.22  tff(c_598, plain, (![B_91, B_92]: (r1_tarski(k3_xboole_0(k1_xboole_0, B_91), B_92))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_527])).
% 5.74/2.22  tff(c_567, plain, (![B_88, A_89]: (B_88=A_89 | ~r1_tarski(B_88, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.74/2.22  tff(c_579, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_567])).
% 5.74/2.22  tff(c_615, plain, (![B_91]: (k3_xboole_0(k1_xboole_0, B_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_598, c_579])).
% 5.74/2.22  tff(c_486, plain, (![B_86]: (k4_xboole_0(k1_xboole_0, B_86)=k3_xboole_0(k1_xboole_0, B_86))), inference(superposition, [status(thm), theory('equality')], [c_479, c_313])).
% 5.74/2.22  tff(c_651, plain, (![B_94]: (k4_xboole_0(k1_xboole_0, B_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_615, c_486])).
% 5.74/2.22  tff(c_28, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.74/2.22  tff(c_674, plain, (![B_94]: (k5_xboole_0(B_94, k1_xboole_0)=k2_xboole_0(B_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_651, c_28])).
% 5.74/2.22  tff(c_704, plain, (![B_94]: (k5_xboole_0(B_94, k1_xboole_0)=B_94)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_674])).
% 5.74/2.22  tff(c_64, plain, (v4_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.74/2.22  tff(c_261, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_120, c_64])).
% 5.74/2.22  tff(c_778, plain, (![A_100, B_101, C_102]: (k7_subset_1(A_100, B_101, C_102)=k4_xboole_0(B_101, C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.74/2.22  tff(c_920, plain, (![C_109]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_109)=k4_xboole_0('#skF_3', C_109))), inference(resolution, [status(thm)], [c_52, c_778])).
% 5.74/2.22  tff(c_932, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_920])).
% 5.74/2.22  tff(c_121, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.22  tff(c_151, plain, (![B_60, A_61]: (k1_setfam_1(k2_tarski(B_60, A_61))=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_30, c_121])).
% 5.74/2.22  tff(c_38, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.22  tff(c_157, plain, (![B_60, A_61]: (k3_xboole_0(B_60, A_61)=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_151, c_38])).
% 5.74/2.22  tff(c_622, plain, (![B_93]: (k3_xboole_0(k1_xboole_0, B_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_598, c_579])).
% 5.74/2.22  tff(c_646, plain, (![A_61]: (k3_xboole_0(A_61, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_622])).
% 5.74/2.22  tff(c_402, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.74/2.22  tff(c_426, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_402])).
% 5.74/2.22  tff(c_736, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_646, c_426])).
% 5.74/2.22  tff(c_783, plain, (![A_103]: (k4_xboole_0(A_103, A_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_646, c_426])).
% 5.74/2.22  tff(c_26, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.74/2.22  tff(c_791, plain, (![A_103]: (k4_xboole_0(A_103, k1_xboole_0)=k3_xboole_0(A_103, A_103))), inference(superposition, [status(thm), theory('equality')], [c_783, c_26])).
% 5.74/2.22  tff(c_822, plain, (![A_104]: (k3_xboole_0(A_104, A_104)=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_791])).
% 5.74/2.22  tff(c_14, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.74/2.22  tff(c_836, plain, (![A_104]: (k5_xboole_0(A_104, A_104)=k4_xboole_0(A_104, A_104))), inference(superposition, [status(thm), theory('equality')], [c_822, c_14])).
% 5.74/2.22  tff(c_854, plain, (![A_104]: (k5_xboole_0(A_104, A_104)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_736, c_836])).
% 5.74/2.22  tff(c_24, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.74/2.22  tff(c_405, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k3_xboole_0(A_80, k4_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_402, c_26])).
% 5.74/2.22  tff(c_427, plain, (![A_80, B_81]: (k3_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_405])).
% 5.74/2.22  tff(c_1241, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k3_xboole_0(B_132, A_131))=k4_xboole_0(A_131, B_132))), inference(superposition, [status(thm), theory('equality')], [c_157, c_479])).
% 5.74/2.22  tff(c_1261, plain, (![A_80, B_81]: (k5_xboole_0(k4_xboole_0(A_80, B_81), k4_xboole_0(A_80, B_81))=k4_xboole_0(k4_xboole_0(A_80, B_81), A_80))), inference(superposition, [status(thm), theory('equality')], [c_427, c_1241])).
% 5.74/2.22  tff(c_1360, plain, (![A_135, B_136]: (k4_xboole_0(k4_xboole_0(A_135, B_136), A_135)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_854, c_1261])).
% 5.74/2.22  tff(c_1395, plain, (k4_xboole_0(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_932, c_1360])).
% 5.74/2.22  tff(c_1640, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1395, c_28])).
% 5.74/2.22  tff(c_1649, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_704, c_1640])).
% 5.74/2.22  tff(c_46, plain, (![A_39, B_40]: (m1_subset_1(k2_tops_1(A_39, B_40), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.74/2.22  tff(c_1163, plain, (![A_125, B_126, C_127]: (k4_subset_1(A_125, B_126, C_127)=k2_xboole_0(B_126, C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(A_125)) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.74/2.22  tff(c_4707, plain, (![A_209, B_210, B_211]: (k4_subset_1(u1_struct_0(A_209), B_210, k2_tops_1(A_209, B_211))=k2_xboole_0(B_210, k2_tops_1(A_209, B_211)) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_209))) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(resolution, [status(thm)], [c_46, c_1163])).
% 5.74/2.22  tff(c_4711, plain, (![B_211]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_211))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_211)) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_4707])).
% 5.74/2.22  tff(c_5370, plain, (![B_221]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_221))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_221)) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4711])).
% 5.74/2.22  tff(c_5377, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_5370])).
% 5.74/2.22  tff(c_5382, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1720, c_1649, c_5377])).
% 5.74/2.22  tff(c_5384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1487, c_5382])).
% 5.74/2.22  tff(c_5385, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 5.74/2.22  tff(c_6130, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6054, c_5385])).
% 5.74/2.22  tff(c_5386, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 5.74/2.22  tff(c_6344, plain, (![A_288, B_289]: (k2_pre_topc(A_288, B_289)=B_289 | ~v4_pre_topc(B_289, A_288) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.74/2.22  tff(c_6350, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_6344])).
% 5.74/2.22  tff(c_6354, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5386, c_6350])).
% 5.74/2.22  tff(c_7744, plain, (![A_327, B_328]: (k7_subset_1(u1_struct_0(A_327), k2_pre_topc(A_327, B_328), k1_tops_1(A_327, B_328))=k2_tops_1(A_327, B_328) | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0(A_327))) | ~l1_pre_topc(A_327))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.74/2.22  tff(c_7753, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6354, c_7744])).
% 5.74/2.22  tff(c_7757, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_6054, c_7753])).
% 5.74/2.22  tff(c_7759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6130, c_7757])).
% 5.74/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.22  
% 5.74/2.22  Inference rules
% 5.74/2.22  ----------------------
% 5.74/2.22  #Ref     : 0
% 5.74/2.22  #Sup     : 1881
% 5.74/2.22  #Fact    : 0
% 5.74/2.22  #Define  : 0
% 5.74/2.22  #Split   : 3
% 5.74/2.22  #Chain   : 0
% 5.74/2.22  #Close   : 0
% 5.74/2.22  
% 5.74/2.22  Ordering : KBO
% 5.74/2.22  
% 5.74/2.22  Simplification rules
% 5.74/2.22  ----------------------
% 5.74/2.22  #Subsume      : 200
% 5.74/2.22  #Demod        : 1871
% 5.74/2.22  #Tautology    : 1324
% 5.74/2.22  #SimpNegUnit  : 4
% 5.74/2.22  #BackRed      : 6
% 5.74/2.22  
% 5.74/2.22  #Partial instantiations: 0
% 5.74/2.22  #Strategies tried      : 1
% 5.74/2.22  
% 5.74/2.22  Timing (in seconds)
% 5.74/2.22  ----------------------
% 6.08/2.23  Preprocessing        : 0.34
% 6.08/2.23  Parsing              : 0.18
% 6.08/2.23  CNF conversion       : 0.02
% 6.08/2.23  Main loop            : 1.11
% 6.08/2.23  Inferencing          : 0.34
% 6.08/2.23  Reduction            : 0.50
% 6.08/2.23  Demodulation         : 0.41
% 6.08/2.23  BG Simplification    : 0.03
% 6.08/2.23  Subsumption          : 0.17
% 6.08/2.23  Abstraction          : 0.07
% 6.08/2.23  MUC search           : 0.00
% 6.08/2.23  Cooper               : 0.00
% 6.08/2.23  Total                : 1.50
% 6.08/2.23  Index Insertion      : 0.00
% 6.08/2.23  Index Deletion       : 0.00
% 6.08/2.23  Index Matching       : 0.00
% 6.08/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

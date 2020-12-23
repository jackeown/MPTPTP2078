%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:20 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.42s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 170 expanded)
%              Number of leaves         :   42 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 293 expanded)
%              Number of equality atoms :   76 ( 120 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
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

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5574,plain,(
    ! [A_200,B_201,C_202] :
      ( k7_subset_1(A_200,B_201,C_202) = k4_xboole_0(B_201,C_202)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(A_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5577,plain,(
    ! [C_202] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_202) = k4_xboole_0('#skF_2',C_202) ),
    inference(resolution,[status(thm)],[c_40,c_5574])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_86,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1769,plain,(
    ! [B_117,A_118] :
      ( v4_pre_topc(B_117,A_118)
      | k2_pre_topc(A_118,B_117) != B_117
      | ~ v2_pre_topc(A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1775,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1769])).

tff(c_1779,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1775])).

tff(c_1780,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1779])).

tff(c_2013,plain,(
    ! [A_123,B_124] :
      ( k4_subset_1(u1_struct_0(A_123),B_124,k2_tops_1(A_123,B_124)) = k2_pre_topc(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2017,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2013])).

tff(c_2021,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2017])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_133,plain,(
    ! [A_8] : k3_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_120])).

tff(c_419,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_166,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k4_xboole_0(B_55,A_54)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_175,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k2_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_166])).

tff(c_426,plain,(
    ! [B_70] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_70)) = k4_xboole_0(k1_xboole_0,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_175])).

tff(c_456,plain,(
    ! [B_71] : k4_xboole_0(k1_xboole_0,B_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_133,c_426])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_471,plain,(
    ! [B_71] : k5_xboole_0(B_71,k1_xboole_0) = k2_xboole_0(B_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_18])).

tff(c_496,plain,(
    ! [B_71] : k5_xboole_0(B_71,k1_xboole_0) = B_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_471])).

tff(c_551,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(A_74,B_75,C_76) = k4_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_577,plain,(
    ! [C_78] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_78) = k4_xboole_0('#skF_2',C_78) ),
    inference(resolution,[status(thm)],[c_40,c_551])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_267,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_52])).

tff(c_583,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_267])).

tff(c_20,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_151,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_197,plain,(
    ! [B_57,A_58] : k1_setfam_1(k2_tarski(B_57,A_58)) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_151])).

tff(c_26,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_220,plain,(
    ! [B_59,A_60] : k3_xboole_0(B_59,A_60) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_26])).

tff(c_236,plain,(
    ! [B_59] : k3_xboole_0(B_59,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_133])).

tff(c_318,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_339,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_318])).

tff(c_342,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_339])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_448,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_419])).

tff(c_455,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_448])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_593,plain,(
    ! [A_79,B_80] : k3_xboole_0(k4_xboole_0(A_79,B_80),A_79) = k4_xboole_0(A_79,B_80) ),
    inference(resolution,[status(thm)],[c_12,c_120])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_599,plain,(
    ! [A_79,B_80] : k5_xboole_0(k4_xboole_0(A_79,B_80),k4_xboole_0(A_79,B_80)) = k4_xboole_0(k4_xboole_0(A_79,B_80),A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_4])).

tff(c_644,plain,(
    ! [A_79,B_80] : k4_xboole_0(k4_xboole_0(A_79,B_80),A_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_599])).

tff(c_916,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_644])).

tff(c_952,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_18])).

tff(c_962,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_952])).

tff(c_32,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_tops_1(A_29,B_30),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1738,plain,(
    ! [A_113,B_114,C_115] :
      ( k4_subset_1(A_113,B_114,C_115) = k2_xboole_0(B_114,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(A_113))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5036,plain,(
    ! [A_168,B_169,B_170] :
      ( k4_subset_1(u1_struct_0(A_168),B_169,k2_tops_1(A_168,B_170)) = k2_xboole_0(B_169,k2_tops_1(A_168,B_170))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_32,c_1738])).

tff(c_5040,plain,(
    ! [B_170] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_170)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_170))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_5036])).

tff(c_5048,plain,(
    ! [B_171] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_171)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_171))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5040])).

tff(c_5055,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_5048])).

tff(c_5060,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2021,c_962,c_5055])).

tff(c_5062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1780,c_5060])).

tff(c_5063,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5811,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5577,c_5063])).

tff(c_5064,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5716,plain,(
    ! [A_208,B_209] :
      ( k2_pre_topc(A_208,B_209) = B_209
      | ~ v4_pre_topc(B_209,A_208)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5719,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_5716])).

tff(c_5722,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5064,c_5719])).

tff(c_7208,plain,(
    ! [A_258,B_259] :
      ( k7_subset_1(u1_struct_0(A_258),k2_pre_topc(A_258,B_259),k1_tops_1(A_258,B_259)) = k2_tops_1(A_258,B_259)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7217,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5722,c_7208])).

tff(c_7221,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5577,c_7217])).

tff(c_7223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5811,c_7221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:31:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.26/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.11  
% 5.26/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.11  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.26/2.11  
% 5.26/2.11  %Foreground sorts:
% 5.26/2.11  
% 5.26/2.11  
% 5.26/2.11  %Background operators:
% 5.26/2.11  
% 5.26/2.11  
% 5.26/2.11  %Foreground operators:
% 5.26/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.26/2.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.26/2.11  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.26/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.26/2.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.26/2.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.26/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.26/2.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.26/2.11  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.26/2.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.26/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.26/2.11  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.26/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.26/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.26/2.11  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.26/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.26/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.26/2.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.26/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.26/2.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.26/2.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.26/2.11  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.26/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.26/2.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.26/2.11  
% 5.42/2.13  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.42/2.13  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.42/2.13  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.42/2.13  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.42/2.13  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.42/2.13  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.42/2.13  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.42/2.13  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.42/2.13  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.42/2.13  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.42/2.13  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.42/2.13  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.42/2.13  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.42/2.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.42/2.13  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.42/2.13  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.42/2.13  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.42/2.13  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.42/2.13  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.42/2.13  tff(c_5574, plain, (![A_200, B_201, C_202]: (k7_subset_1(A_200, B_201, C_202)=k4_xboole_0(B_201, C_202) | ~m1_subset_1(B_201, k1_zfmisc_1(A_200)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.42/2.13  tff(c_5577, plain, (![C_202]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_202)=k4_xboole_0('#skF_2', C_202))), inference(resolution, [status(thm)], [c_40, c_5574])).
% 5.42/2.13  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.42/2.13  tff(c_86, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 5.42/2.13  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.42/2.13  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.42/2.13  tff(c_1769, plain, (![B_117, A_118]: (v4_pre_topc(B_117, A_118) | k2_pre_topc(A_118, B_117)!=B_117 | ~v2_pre_topc(A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.42/2.13  tff(c_1775, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1769])).
% 5.42/2.13  tff(c_1779, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1775])).
% 5.42/2.13  tff(c_1780, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_86, c_1779])).
% 5.42/2.13  tff(c_2013, plain, (![A_123, B_124]: (k4_subset_1(u1_struct_0(A_123), B_124, k2_tops_1(A_123, B_124))=k2_pre_topc(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.42/2.13  tff(c_2017, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2013])).
% 5.42/2.13  tff(c_2021, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2017])).
% 5.42/2.13  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.42/2.13  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.42/2.13  tff(c_120, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.42/2.13  tff(c_133, plain, (![A_8]: (k3_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_120])).
% 5.42/2.13  tff(c_419, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.42/2.13  tff(c_14, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.42/2.13  tff(c_166, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k4_xboole_0(B_55, A_54))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.42/2.13  tff(c_175, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k2_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_166])).
% 5.42/2.13  tff(c_426, plain, (![B_70]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_70))=k4_xboole_0(k1_xboole_0, B_70))), inference(superposition, [status(thm), theory('equality')], [c_419, c_175])).
% 5.42/2.13  tff(c_456, plain, (![B_71]: (k4_xboole_0(k1_xboole_0, B_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_133, c_426])).
% 5.42/2.13  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.42/2.13  tff(c_471, plain, (![B_71]: (k5_xboole_0(B_71, k1_xboole_0)=k2_xboole_0(B_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_456, c_18])).
% 5.42/2.13  tff(c_496, plain, (![B_71]: (k5_xboole_0(B_71, k1_xboole_0)=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_471])).
% 5.42/2.13  tff(c_551, plain, (![A_74, B_75, C_76]: (k7_subset_1(A_74, B_75, C_76)=k4_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.42/2.13  tff(c_577, plain, (![C_78]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_78)=k4_xboole_0('#skF_2', C_78))), inference(resolution, [status(thm)], [c_40, c_551])).
% 5.42/2.13  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.42/2.13  tff(c_267, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_86, c_52])).
% 5.42/2.13  tff(c_583, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_577, c_267])).
% 5.42/2.13  tff(c_20, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.42/2.13  tff(c_151, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.42/2.13  tff(c_197, plain, (![B_57, A_58]: (k1_setfam_1(k2_tarski(B_57, A_58))=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_20, c_151])).
% 5.42/2.13  tff(c_26, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.42/2.13  tff(c_220, plain, (![B_59, A_60]: (k3_xboole_0(B_59, A_60)=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_197, c_26])).
% 5.42/2.13  tff(c_236, plain, (![B_59]: (k3_xboole_0(B_59, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_220, c_133])).
% 5.42/2.13  tff(c_318, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.42/2.13  tff(c_339, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_318])).
% 5.42/2.13  tff(c_342, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_339])).
% 5.42/2.13  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.42/2.13  tff(c_448, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_419])).
% 5.42/2.13  tff(c_455, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_342, c_448])).
% 5.42/2.13  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.42/2.13  tff(c_593, plain, (![A_79, B_80]: (k3_xboole_0(k4_xboole_0(A_79, B_80), A_79)=k4_xboole_0(A_79, B_80))), inference(resolution, [status(thm)], [c_12, c_120])).
% 5.42/2.13  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.42/2.13  tff(c_599, plain, (![A_79, B_80]: (k5_xboole_0(k4_xboole_0(A_79, B_80), k4_xboole_0(A_79, B_80))=k4_xboole_0(k4_xboole_0(A_79, B_80), A_79))), inference(superposition, [status(thm), theory('equality')], [c_593, c_4])).
% 5.42/2.13  tff(c_644, plain, (![A_79, B_80]: (k4_xboole_0(k4_xboole_0(A_79, B_80), A_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_455, c_599])).
% 5.42/2.13  tff(c_916, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_583, c_644])).
% 5.42/2.13  tff(c_952, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_916, c_18])).
% 5.42/2.13  tff(c_962, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_496, c_952])).
% 5.42/2.13  tff(c_32, plain, (![A_29, B_30]: (m1_subset_1(k2_tops_1(A_29, B_30), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.42/2.13  tff(c_1738, plain, (![A_113, B_114, C_115]: (k4_subset_1(A_113, B_114, C_115)=k2_xboole_0(B_114, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(A_113)) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.42/2.13  tff(c_5036, plain, (![A_168, B_169, B_170]: (k4_subset_1(u1_struct_0(A_168), B_169, k2_tops_1(A_168, B_170))=k2_xboole_0(B_169, k2_tops_1(A_168, B_170)) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(resolution, [status(thm)], [c_32, c_1738])).
% 5.42/2.13  tff(c_5040, plain, (![B_170]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_170))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_170)) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_5036])).
% 5.42/2.13  tff(c_5048, plain, (![B_171]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_171))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_171)) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5040])).
% 5.42/2.13  tff(c_5055, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_5048])).
% 5.42/2.13  tff(c_5060, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2021, c_962, c_5055])).
% 5.42/2.13  tff(c_5062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1780, c_5060])).
% 5.42/2.13  tff(c_5063, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.42/2.13  tff(c_5811, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5577, c_5063])).
% 5.42/2.13  tff(c_5064, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 5.42/2.13  tff(c_5716, plain, (![A_208, B_209]: (k2_pre_topc(A_208, B_209)=B_209 | ~v4_pre_topc(B_209, A_208) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.42/2.13  tff(c_5719, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_5716])).
% 5.42/2.13  tff(c_5722, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5064, c_5719])).
% 5.42/2.13  tff(c_7208, plain, (![A_258, B_259]: (k7_subset_1(u1_struct_0(A_258), k2_pre_topc(A_258, B_259), k1_tops_1(A_258, B_259))=k2_tops_1(A_258, B_259) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.42/2.13  tff(c_7217, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5722, c_7208])).
% 5.42/2.13  tff(c_7221, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_5577, c_7217])).
% 5.42/2.13  tff(c_7223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5811, c_7221])).
% 5.42/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.13  
% 5.42/2.13  Inference rules
% 5.42/2.13  ----------------------
% 5.42/2.13  #Ref     : 0
% 5.42/2.13  #Sup     : 1740
% 5.42/2.13  #Fact    : 0
% 5.42/2.13  #Define  : 0
% 5.42/2.13  #Split   : 2
% 5.42/2.13  #Chain   : 0
% 5.42/2.13  #Close   : 0
% 5.42/2.13  
% 5.42/2.13  Ordering : KBO
% 5.42/2.13  
% 5.42/2.13  Simplification rules
% 5.42/2.13  ----------------------
% 5.42/2.13  #Subsume      : 78
% 5.42/2.13  #Demod        : 2505
% 5.42/2.13  #Tautology    : 1491
% 5.42/2.13  #SimpNegUnit  : 4
% 5.42/2.13  #BackRed      : 4
% 5.42/2.13  
% 5.42/2.13  #Partial instantiations: 0
% 5.42/2.13  #Strategies tried      : 1
% 5.42/2.13  
% 5.42/2.13  Timing (in seconds)
% 5.42/2.13  ----------------------
% 5.42/2.13  Preprocessing        : 0.34
% 5.42/2.13  Parsing              : 0.19
% 5.42/2.13  CNF conversion       : 0.02
% 5.42/2.13  Main loop            : 0.98
% 5.42/2.13  Inferencing          : 0.30
% 5.42/2.13  Reduction            : 0.48
% 5.42/2.13  Demodulation         : 0.41
% 5.42/2.13  BG Simplification    : 0.03
% 5.42/2.13  Subsumption          : 0.11
% 5.42/2.13  Abstraction          : 0.05
% 5.42/2.13  MUC search           : 0.00
% 5.42/2.13  Cooper               : 0.00
% 5.42/2.13  Total                : 1.36
% 5.42/2.13  Index Insertion      : 0.00
% 5.42/2.13  Index Deletion       : 0.00
% 5.42/2.13  Index Matching       : 0.00
% 5.42/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

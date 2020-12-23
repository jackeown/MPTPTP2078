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
% DateTime   : Thu Dec  3 10:21:22 EST 2020

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 205 expanded)
%              Number of leaves         :   44 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  152 ( 327 expanded)
%              Number of equality atoms :   85 ( 154 expanded)
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

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5687,plain,(
    ! [A_224,B_225,C_226] :
      ( k7_subset_1(A_224,B_225,C_226) = k4_xboole_0(B_225,C_226)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(A_224)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5690,plain,(
    ! [C_226] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_226) = k4_xboole_0('#skF_2',C_226) ),
    inference(resolution,[status(thm)],[c_40,c_5687])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_90,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1388,plain,(
    ! [B_116,A_117] :
      ( v4_pre_topc(B_116,A_117)
      | k2_pre_topc(A_117,B_116) != B_116
      | ~ v2_pre_topc(A_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1394,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1388])).

tff(c_1398,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1394])).

tff(c_1399,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1398])).

tff(c_1666,plain,(
    ! [A_124,B_125] :
      ( k4_subset_1(u1_struct_0(A_124),B_125,k2_tops_1(A_124,B_125)) = k2_pre_topc(A_124,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1670,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1666])).

tff(c_1674,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1670])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_228,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_52])).

tff(c_573,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_618,plain,(
    ! [C_83] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_83) = k4_xboole_0('#skF_2',C_83) ),
    inference(resolution,[status(thm)],[c_40,c_573])).

tff(c_630,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_618])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_272,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(B_67,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_124])).

tff(c_22,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_295,plain,(
    ! [B_68,A_69] : k2_xboole_0(B_68,A_69) = k2_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_22])).

tff(c_323,plain,(
    ! [A_69] : k2_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_6])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_425,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k4_xboole_0(B_75,A_74)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_437,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,A_10) = k2_xboole_0(k1_xboole_0,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_425])).

tff(c_441,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_437])).

tff(c_354,plain,(
    ! [A_70] : k2_xboole_0(k1_xboole_0,A_70) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_6])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_154,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(resolution,[status(thm)],[c_16,c_154])).

tff(c_480,plain,(
    ! [A_77] : k3_xboole_0(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_167])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_495,plain,(
    ! [A_77] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_4])).

tff(c_579,plain,(
    ! [A_82] : k4_xboole_0(k1_xboole_0,A_82) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_495])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_584,plain,(
    ! [A_82] : k5_xboole_0(A_82,k1_xboole_0) = k2_xboole_0(A_82,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_18])).

tff(c_610,plain,(
    ! [A_82] : k5_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_584])).

tff(c_139,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_205,plain,(
    ! [A_62,B_63] : k1_setfam_1(k2_tarski(A_62,B_63)) = k3_xboole_0(B_63,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_139])).

tff(c_28,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_211,plain,(
    ! [B_63,A_62] : k3_xboole_0(B_63,A_62) = k3_xboole_0(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_28])).

tff(c_509,plain,(
    ! [A_62] : k3_xboole_0(A_62,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_480])).

tff(c_397,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_415,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_397])).

tff(c_768,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_415])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_177,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_168])).

tff(c_769,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_177])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1059,plain,(
    ! [A_107,B_108] : k3_xboole_0(k4_xboole_0(A_107,B_108),A_107) = k4_xboole_0(A_107,B_108) ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_1081,plain,(
    ! [A_107,B_108] : k5_xboole_0(k4_xboole_0(A_107,B_108),k4_xboole_0(A_107,B_108)) = k4_xboole_0(k4_xboole_0(A_107,B_108),A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_1059,c_4])).

tff(c_1145,plain,(
    ! [A_110,B_111] : k4_xboole_0(k4_xboole_0(A_110,B_111),A_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_1081])).

tff(c_1156,plain,(
    ! [A_110,B_111] : k2_xboole_0(A_110,k4_xboole_0(A_110,B_111)) = k5_xboole_0(A_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_18])).

tff(c_1216,plain,(
    ! [A_112,B_113] : k2_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_1156])).

tff(c_1259,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_1216])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_tops_1(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1050,plain,(
    ! [A_104,B_105,C_106] :
      ( k4_subset_1(A_104,B_105,C_106) = k2_xboole_0(B_105,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4663,plain,(
    ! [A_179,B_180,B_181] :
      ( k4_subset_1(u1_struct_0(A_179),B_180,k2_tops_1(A_179,B_181)) = k2_xboole_0(B_180,k2_tops_1(A_179,B_181))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(resolution,[status(thm)],[c_34,c_1050])).

tff(c_4667,plain,(
    ! [B_181] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_181)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_181))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_4663])).

tff(c_5097,plain,(
    ! [B_188] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_188)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_188))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4667])).

tff(c_5104,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_5097])).

tff(c_5109,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1674,c_1259,c_5104])).

tff(c_5111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1399,c_5109])).

tff(c_5112,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5722,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5690,c_5112])).

tff(c_5113,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6078,plain,(
    ! [A_243,B_244] :
      ( k2_pre_topc(A_243,B_244) = B_244
      | ~ v4_pre_topc(B_244,A_243)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6084,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_6078])).

tff(c_6088,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5113,c_6084])).

tff(c_7316,plain,(
    ! [A_280,B_281] :
      ( k7_subset_1(u1_struct_0(A_280),k2_pre_topc(A_280,B_281),k1_tops_1(A_280,B_281)) = k2_tops_1(A_280,B_281)
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7325,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6088,c_7316])).

tff(c_7329,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5690,c_7325])).

tff(c_7331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5722,c_7329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:44:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/2.06  
% 5.24/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/2.06  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.24/2.06  
% 5.24/2.06  %Foreground sorts:
% 5.24/2.06  
% 5.24/2.06  
% 5.24/2.06  %Background operators:
% 5.24/2.06  
% 5.24/2.06  
% 5.24/2.06  %Foreground operators:
% 5.24/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.24/2.06  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.24/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.24/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.24/2.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.24/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.24/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.24/2.06  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.24/2.06  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.24/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.24/2.06  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.24/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.24/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.24/2.06  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.24/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/2.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.24/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.24/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.24/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.24/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.24/2.06  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.24/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.24/2.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.24/2.06  
% 5.24/2.08  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.24/2.08  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.24/2.08  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.24/2.08  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.24/2.08  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.24/2.08  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.24/2.08  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.24/2.08  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.24/2.08  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.24/2.08  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.24/2.08  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.24/2.08  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.24/2.08  tff(f_61, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.24/2.08  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.24/2.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.24/2.08  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.24/2.08  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.24/2.08  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.24/2.08  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.24/2.08  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.24/2.08  tff(c_5687, plain, (![A_224, B_225, C_226]: (k7_subset_1(A_224, B_225, C_226)=k4_xboole_0(B_225, C_226) | ~m1_subset_1(B_225, k1_zfmisc_1(A_224)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.24/2.08  tff(c_5690, plain, (![C_226]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_226)=k4_xboole_0('#skF_2', C_226))), inference(resolution, [status(thm)], [c_40, c_5687])).
% 5.24/2.08  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.24/2.08  tff(c_90, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 5.24/2.08  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.24/2.08  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.24/2.08  tff(c_1388, plain, (![B_116, A_117]: (v4_pre_topc(B_116, A_117) | k2_pre_topc(A_117, B_116)!=B_116 | ~v2_pre_topc(A_117) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.24/2.08  tff(c_1394, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1388])).
% 5.24/2.08  tff(c_1398, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1394])).
% 5.24/2.08  tff(c_1399, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_90, c_1398])).
% 5.24/2.08  tff(c_1666, plain, (![A_124, B_125]: (k4_subset_1(u1_struct_0(A_124), B_125, k2_tops_1(A_124, B_125))=k2_pre_topc(A_124, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/2.08  tff(c_1670, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1666])).
% 5.24/2.08  tff(c_1674, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1670])).
% 5.24/2.08  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.24/2.08  tff(c_228, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_90, c_52])).
% 5.24/2.08  tff(c_573, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.24/2.08  tff(c_618, plain, (![C_83]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_83)=k4_xboole_0('#skF_2', C_83))), inference(resolution, [status(thm)], [c_40, c_573])).
% 5.24/2.08  tff(c_630, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_228, c_618])).
% 5.24/2.08  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.24/2.08  tff(c_20, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.24/2.08  tff(c_124, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.24/2.08  tff(c_272, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(B_67, A_66))), inference(superposition, [status(thm), theory('equality')], [c_20, c_124])).
% 5.24/2.08  tff(c_22, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.24/2.08  tff(c_295, plain, (![B_68, A_69]: (k2_xboole_0(B_68, A_69)=k2_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_272, c_22])).
% 5.24/2.08  tff(c_323, plain, (![A_69]: (k2_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_295, c_6])).
% 5.24/2.08  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.24/2.08  tff(c_425, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k4_xboole_0(B_75, A_74))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.24/2.08  tff(c_437, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, A_10)=k2_xboole_0(k1_xboole_0, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_425])).
% 5.24/2.08  tff(c_441, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_323, c_437])).
% 5.24/2.08  tff(c_354, plain, (![A_70]: (k2_xboole_0(k1_xboole_0, A_70)=A_70)), inference(superposition, [status(thm), theory('equality')], [c_295, c_6])).
% 5.24/2.08  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.24/2.08  tff(c_154, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.24/2.08  tff(c_167, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(resolution, [status(thm)], [c_16, c_154])).
% 5.24/2.08  tff(c_480, plain, (![A_77]: (k3_xboole_0(k1_xboole_0, A_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_354, c_167])).
% 5.24/2.08  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.24/2.08  tff(c_495, plain, (![A_77]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_77))), inference(superposition, [status(thm), theory('equality')], [c_480, c_4])).
% 5.24/2.08  tff(c_579, plain, (![A_82]: (k4_xboole_0(k1_xboole_0, A_82)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_441, c_495])).
% 5.24/2.08  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.24/2.08  tff(c_584, plain, (![A_82]: (k5_xboole_0(A_82, k1_xboole_0)=k2_xboole_0(A_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_579, c_18])).
% 5.24/2.08  tff(c_610, plain, (![A_82]: (k5_xboole_0(A_82, k1_xboole_0)=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_584])).
% 5.24/2.08  tff(c_139, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.24/2.08  tff(c_205, plain, (![A_62, B_63]: (k1_setfam_1(k2_tarski(A_62, B_63))=k3_xboole_0(B_63, A_62))), inference(superposition, [status(thm), theory('equality')], [c_20, c_139])).
% 5.24/2.08  tff(c_28, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.24/2.08  tff(c_211, plain, (![B_63, A_62]: (k3_xboole_0(B_63, A_62)=k3_xboole_0(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_205, c_28])).
% 5.24/2.08  tff(c_509, plain, (![A_62]: (k3_xboole_0(A_62, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_211, c_480])).
% 5.24/2.08  tff(c_397, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.24/2.08  tff(c_415, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_397])).
% 5.24/2.08  tff(c_768, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_509, c_415])).
% 5.24/2.08  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.24/2.08  tff(c_168, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.24/2.08  tff(c_177, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_168])).
% 5.24/2.08  tff(c_769, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_768, c_177])).
% 5.24/2.08  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.24/2.08  tff(c_1059, plain, (![A_107, B_108]: (k3_xboole_0(k4_xboole_0(A_107, B_108), A_107)=k4_xboole_0(A_107, B_108))), inference(resolution, [status(thm)], [c_10, c_154])).
% 5.24/2.08  tff(c_1081, plain, (![A_107, B_108]: (k5_xboole_0(k4_xboole_0(A_107, B_108), k4_xboole_0(A_107, B_108))=k4_xboole_0(k4_xboole_0(A_107, B_108), A_107))), inference(superposition, [status(thm), theory('equality')], [c_1059, c_4])).
% 5.24/2.08  tff(c_1145, plain, (![A_110, B_111]: (k4_xboole_0(k4_xboole_0(A_110, B_111), A_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_769, c_1081])).
% 5.24/2.08  tff(c_1156, plain, (![A_110, B_111]: (k2_xboole_0(A_110, k4_xboole_0(A_110, B_111))=k5_xboole_0(A_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1145, c_18])).
% 5.24/2.08  tff(c_1216, plain, (![A_112, B_113]: (k2_xboole_0(A_112, k4_xboole_0(A_112, B_113))=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_610, c_1156])).
% 5.24/2.08  tff(c_1259, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_630, c_1216])).
% 5.24/2.08  tff(c_34, plain, (![A_32, B_33]: (m1_subset_1(k2_tops_1(A_32, B_33), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.24/2.08  tff(c_1050, plain, (![A_104, B_105, C_106]: (k4_subset_1(A_104, B_105, C_106)=k2_xboole_0(B_105, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.24/2.08  tff(c_4663, plain, (![A_179, B_180, B_181]: (k4_subset_1(u1_struct_0(A_179), B_180, k2_tops_1(A_179, B_181))=k2_xboole_0(B_180, k2_tops_1(A_179, B_181)) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(resolution, [status(thm)], [c_34, c_1050])).
% 5.24/2.08  tff(c_4667, plain, (![B_181]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_181))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_181)) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_4663])).
% 5.24/2.08  tff(c_5097, plain, (![B_188]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_188))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_188)) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4667])).
% 5.24/2.08  tff(c_5104, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_5097])).
% 5.24/2.08  tff(c_5109, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1674, c_1259, c_5104])).
% 5.24/2.08  tff(c_5111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1399, c_5109])).
% 5.24/2.08  tff(c_5112, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.24/2.08  tff(c_5722, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5690, c_5112])).
% 5.24/2.08  tff(c_5113, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 5.24/2.08  tff(c_6078, plain, (![A_243, B_244]: (k2_pre_topc(A_243, B_244)=B_244 | ~v4_pre_topc(B_244, A_243) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.24/2.08  tff(c_6084, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_6078])).
% 5.24/2.08  tff(c_6088, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5113, c_6084])).
% 5.24/2.08  tff(c_7316, plain, (![A_280, B_281]: (k7_subset_1(u1_struct_0(A_280), k2_pre_topc(A_280, B_281), k1_tops_1(A_280, B_281))=k2_tops_1(A_280, B_281) | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.24/2.08  tff(c_7325, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6088, c_7316])).
% 5.24/2.08  tff(c_7329, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_5690, c_7325])).
% 5.24/2.08  tff(c_7331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5722, c_7329])).
% 5.24/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/2.08  
% 5.24/2.08  Inference rules
% 5.24/2.08  ----------------------
% 5.24/2.08  #Ref     : 0
% 5.24/2.08  #Sup     : 1774
% 5.24/2.08  #Fact    : 0
% 5.24/2.08  #Define  : 0
% 5.24/2.08  #Split   : 2
% 5.24/2.08  #Chain   : 0
% 5.24/2.08  #Close   : 0
% 5.24/2.09  
% 5.24/2.09  Ordering : KBO
% 5.24/2.09  
% 5.24/2.09  Simplification rules
% 5.24/2.09  ----------------------
% 5.24/2.09  #Subsume      : 23
% 5.24/2.09  #Demod        : 1818
% 5.24/2.09  #Tautology    : 1487
% 5.24/2.09  #SimpNegUnit  : 4
% 5.24/2.09  #BackRed      : 2
% 5.24/2.09  
% 5.24/2.09  #Partial instantiations: 0
% 5.24/2.09  #Strategies tried      : 1
% 5.24/2.09  
% 5.24/2.09  Timing (in seconds)
% 5.24/2.09  ----------------------
% 5.24/2.09  Preprocessing        : 0.34
% 5.24/2.09  Parsing              : 0.19
% 5.24/2.09  CNF conversion       : 0.02
% 5.24/2.09  Main loop            : 0.97
% 5.24/2.09  Inferencing          : 0.30
% 5.24/2.09  Reduction            : 0.45
% 5.24/2.09  Demodulation         : 0.37
% 5.24/2.09  BG Simplification    : 0.03
% 5.24/2.09  Subsumption          : 0.13
% 5.24/2.09  Abstraction          : 0.05
% 5.24/2.09  MUC search           : 0.00
% 5.24/2.09  Cooper               : 0.00
% 5.24/2.09  Total                : 1.35
% 5.24/2.09  Index Insertion      : 0.00
% 5.24/2.09  Index Deletion       : 0.00
% 5.24/2.09  Index Matching       : 0.00
% 5.24/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

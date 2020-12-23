%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:22 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 190 expanded)
%              Number of leaves         :   42 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 312 expanded)
%              Number of equality atoms :   79 ( 139 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_72,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7011,plain,(
    ! [A_277,B_278,C_279] :
      ( k7_subset_1(A_277,B_278,C_279) = k4_xboole_0(B_278,C_279)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(A_277)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7014,plain,(
    ! [C_279] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_279) = k4_xboole_0('#skF_2',C_279) ),
    inference(resolution,[status(thm)],[c_36,c_7011])).

tff(c_42,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_113,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1158,plain,(
    ! [B_101,A_102] :
      ( v4_pre_topc(B_101,A_102)
      | k2_pre_topc(A_102,B_101) != B_101
      | ~ v2_pre_topc(A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1164,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1158])).

tff(c_1168,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_1164])).

tff(c_1169,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_1168])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_244,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_48])).

tff(c_402,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_subset_1(A_66,B_67,C_68) = k4_xboole_0(B_67,C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_551,plain,(
    ! [C_75] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_75) = k4_xboole_0('#skF_2',C_75) ),
    inference(resolution,[status(thm)],[c_36,c_402])).

tff(c_563,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_551])).

tff(c_59,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [B_41] : k3_xboole_0(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_8])).

tff(c_16,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_136,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_758,plain,(
    ! [A_84,B_85] : k1_setfam_1(k2_tarski(A_84,B_85)) = k3_xboole_0(B_85,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_136])).

tff(c_24,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_781,plain,(
    ! [B_86,A_87] : k3_xboole_0(B_86,A_87) = k3_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_24])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [A_53,B_54] : k2_xboole_0(k3_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    ! [A_5] : k2_xboole_0(k3_xboole_0(A_5,k1_xboole_0),A_5) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_174])).

tff(c_815,plain,(
    ! [A_87] : k2_xboole_0(k3_xboole_0(k1_xboole_0,A_87),A_87) = A_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_192])).

tff(c_868,plain,(
    ! [A_87] : k2_xboole_0(k1_xboole_0,A_87) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_815])).

tff(c_764,plain,(
    ! [B_85,A_84] : k3_xboole_0(B_85,A_84) = k3_xboole_0(A_84,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_24])).

tff(c_121,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [B_51,A_52] : k3_tarski(k2_tarski(B_51,A_52)) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_121])).

tff(c_18,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_18])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)) = k4_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1395,plain,(
    ! [A_113,B_114] : k2_xboole_0(k3_xboole_0(A_113,k2_xboole_0(A_113,B_114)),k1_xboole_0) = A_113 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_174])).

tff(c_5103,plain,(
    ! [A_225,B_226,C_227] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_225,B_226),k4_xboole_0(A_225,k4_xboole_0(B_226,C_227))),k1_xboole_0) = k4_xboole_0(A_225,B_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1395])).

tff(c_5309,plain,(
    ! [A_225,A_7] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_225,A_7),k4_xboole_0(A_225,k1_xboole_0)),k1_xboole_0) = k4_xboole_0(A_225,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_5103])).

tff(c_6228,plain,(
    ! [A_249,A_250] : k3_xboole_0(A_249,k4_xboole_0(A_249,A_250)) = k4_xboole_0(A_249,A_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_764,c_157,c_6,c_5309])).

tff(c_363,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_375,plain,(
    ! [B_65] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_363])).

tff(c_386,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_10])).

tff(c_372,plain,(
    ! [B_41] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_363])).

tff(c_396,plain,(
    ! [B_41] : k4_xboole_0(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_372])).

tff(c_497,plain,(
    ! [A_72,B_73,C_74] : k2_xboole_0(k4_xboole_0(A_72,B_73),k3_xboole_0(A_72,C_74)) = k4_xboole_0(A_72,k4_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_542,plain,(
    ! [A_5,C_74] : k4_xboole_0(A_5,k4_xboole_0(k1_xboole_0,C_74)) = k2_xboole_0(A_5,k3_xboole_0(A_5,C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_497])).

tff(c_547,plain,(
    ! [A_5,C_74] : k2_xboole_0(A_5,k3_xboole_0(A_5,C_74)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_396,c_542])).

tff(c_6460,plain,(
    ! [A_251,A_252] : k2_xboole_0(A_251,k4_xboole_0(A_251,A_252)) = A_251 ),
    inference(superposition,[status(thm),theory(equality)],[c_6228,c_547])).

tff(c_6581,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_6460])).

tff(c_1313,plain,(
    ! [A_109,B_110] :
      ( k4_subset_1(u1_struct_0(A_109),B_110,k2_tops_1(A_109,B_110)) = k2_pre_topc(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1317,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1313])).

tff(c_1321,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1317])).

tff(c_30,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_tops_1(A_29,B_30),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1071,plain,(
    ! [A_95,B_96,C_97] :
      ( k4_subset_1(A_95,B_96,C_97) = k2_xboole_0(B_96,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4267,plain,(
    ! [A_205,B_206,B_207] :
      ( k4_subset_1(u1_struct_0(A_205),B_206,k2_tops_1(A_205,B_207)) = k2_xboole_0(B_206,k2_tops_1(A_205,B_207))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(resolution,[status(thm)],[c_30,c_1071])).

tff(c_4271,plain,(
    ! [B_207] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_207)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_207))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_4267])).

tff(c_4279,plain,(
    ! [B_208] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_208)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4271])).

tff(c_4286,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_4279])).

tff(c_4291,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_4286])).

tff(c_6645,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6581,c_4291])).

tff(c_6647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1169,c_6645])).

tff(c_6648,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_7017,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7014,c_6648])).

tff(c_6649,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_7396,plain,(
    ! [A_296,B_297] :
      ( k2_pre_topc(A_296,B_297) = B_297
      | ~ v4_pre_topc(B_297,A_296)
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7399,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_7396])).

tff(c_7402,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6649,c_7399])).

tff(c_8233,plain,(
    ! [A_332,B_333] :
      ( k7_subset_1(u1_struct_0(A_332),k2_pre_topc(A_332,B_333),k1_tops_1(A_332,B_333)) = k2_tops_1(A_332,B_333)
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0(A_332)))
      | ~ l1_pre_topc(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8242,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7402,c_8233])).

tff(c_8246,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_7014,c_8242])).

tff(c_8248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7017,c_8246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.02/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.36  
% 6.09/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.37  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.09/2.37  
% 6.09/2.37  %Foreground sorts:
% 6.09/2.37  
% 6.09/2.37  
% 6.09/2.37  %Background operators:
% 6.09/2.37  
% 6.09/2.37  
% 6.09/2.37  %Foreground operators:
% 6.09/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.09/2.37  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.09/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.09/2.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.09/2.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.09/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.09/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.09/2.37  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.09/2.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.09/2.37  tff('#skF_2', type, '#skF_2': $i).
% 6.09/2.37  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.09/2.37  tff('#skF_1', type, '#skF_1': $i).
% 6.09/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.09/2.37  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.09/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.09/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.09/2.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.09/2.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.09/2.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.09/2.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.09/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.09/2.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.09/2.37  
% 6.09/2.39  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 6.09/2.39  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.09/2.39  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.09/2.39  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.09/2.39  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.09/2.39  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.09/2.39  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.09/2.39  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.09/2.39  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.09/2.39  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.09/2.39  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.09/2.39  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.09/2.39  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.09/2.39  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 6.09/2.39  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.09/2.39  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.09/2.39  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 6.09/2.39  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.09/2.39  tff(c_7011, plain, (![A_277, B_278, C_279]: (k7_subset_1(A_277, B_278, C_279)=k4_xboole_0(B_278, C_279) | ~m1_subset_1(B_278, k1_zfmisc_1(A_277)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.09/2.39  tff(c_7014, plain, (![C_279]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_279)=k4_xboole_0('#skF_2', C_279))), inference(resolution, [status(thm)], [c_36, c_7011])).
% 6.09/2.39  tff(c_42, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.09/2.39  tff(c_113, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 6.09/2.39  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.09/2.39  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.09/2.39  tff(c_1158, plain, (![B_101, A_102]: (v4_pre_topc(B_101, A_102) | k2_pre_topc(A_102, B_101)!=B_101 | ~v2_pre_topc(A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.09/2.39  tff(c_1164, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1158])).
% 6.09/2.39  tff(c_1168, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_1164])).
% 6.09/2.39  tff(c_1169, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_113, c_1168])).
% 6.09/2.39  tff(c_48, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.09/2.39  tff(c_244, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_113, c_48])).
% 6.09/2.39  tff(c_402, plain, (![A_66, B_67, C_68]: (k7_subset_1(A_66, B_67, C_68)=k4_xboole_0(B_67, C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.09/2.39  tff(c_551, plain, (![C_75]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_75)=k4_xboole_0('#skF_2', C_75))), inference(resolution, [status(thm)], [c_36, c_402])).
% 6.09/2.39  tff(c_563, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_244, c_551])).
% 6.09/2.39  tff(c_59, plain, (![A_40, B_41]: (r1_tarski(k3_xboole_0(A_40, B_41), A_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.09/2.39  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.09/2.39  tff(c_64, plain, (![B_41]: (k3_xboole_0(k1_xboole_0, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_59, c_8])).
% 6.09/2.39  tff(c_16, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.09/2.39  tff(c_136, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.09/2.39  tff(c_758, plain, (![A_84, B_85]: (k1_setfam_1(k2_tarski(A_84, B_85))=k3_xboole_0(B_85, A_84))), inference(superposition, [status(thm), theory('equality')], [c_16, c_136])).
% 6.09/2.39  tff(c_24, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.09/2.39  tff(c_781, plain, (![B_86, A_87]: (k3_xboole_0(B_86, A_87)=k3_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_758, c_24])).
% 6.09/2.39  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.09/2.39  tff(c_174, plain, (![A_53, B_54]: (k2_xboole_0(k3_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=A_53)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.09/2.39  tff(c_192, plain, (![A_5]: (k2_xboole_0(k3_xboole_0(A_5, k1_xboole_0), A_5)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_6, c_174])).
% 6.09/2.39  tff(c_815, plain, (![A_87]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, A_87), A_87)=A_87)), inference(superposition, [status(thm), theory('equality')], [c_781, c_192])).
% 6.09/2.39  tff(c_868, plain, (![A_87]: (k2_xboole_0(k1_xboole_0, A_87)=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_815])).
% 6.09/2.39  tff(c_764, plain, (![B_85, A_84]: (k3_xboole_0(B_85, A_84)=k3_xboole_0(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_758, c_24])).
% 6.09/2.39  tff(c_121, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.09/2.39  tff(c_151, plain, (![B_51, A_52]: (k3_tarski(k2_tarski(B_51, A_52))=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_16, c_121])).
% 6.09/2.39  tff(c_18, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.09/2.39  tff(c_157, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_151, c_18])).
% 6.09/2.39  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.09/2.39  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13))=k4_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.09/2.39  tff(c_1395, plain, (![A_113, B_114]: (k2_xboole_0(k3_xboole_0(A_113, k2_xboole_0(A_113, B_114)), k1_xboole_0)=A_113)), inference(superposition, [status(thm), theory('equality')], [c_10, c_174])).
% 6.09/2.39  tff(c_5103, plain, (![A_225, B_226, C_227]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_225, B_226), k4_xboole_0(A_225, k4_xboole_0(B_226, C_227))), k1_xboole_0)=k4_xboole_0(A_225, B_226))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1395])).
% 6.09/2.39  tff(c_5309, plain, (![A_225, A_7]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_225, A_7), k4_xboole_0(A_225, k1_xboole_0)), k1_xboole_0)=k4_xboole_0(A_225, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_5103])).
% 6.09/2.39  tff(c_6228, plain, (![A_249, A_250]: (k3_xboole_0(A_249, k4_xboole_0(A_249, A_250))=k4_xboole_0(A_249, A_250))), inference(demodulation, [status(thm), theory('equality')], [c_868, c_764, c_157, c_6, c_5309])).
% 6.09/2.39  tff(c_363, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.09/2.39  tff(c_375, plain, (![B_65]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_65))), inference(superposition, [status(thm), theory('equality')], [c_64, c_363])).
% 6.09/2.39  tff(c_386, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_375, c_10])).
% 6.09/2.39  tff(c_372, plain, (![B_41]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_41))), inference(superposition, [status(thm), theory('equality')], [c_64, c_363])).
% 6.09/2.39  tff(c_396, plain, (![B_41]: (k4_xboole_0(k1_xboole_0, B_41)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_386, c_372])).
% 6.09/2.39  tff(c_497, plain, (![A_72, B_73, C_74]: (k2_xboole_0(k4_xboole_0(A_72, B_73), k3_xboole_0(A_72, C_74))=k4_xboole_0(A_72, k4_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.09/2.39  tff(c_542, plain, (![A_5, C_74]: (k4_xboole_0(A_5, k4_xboole_0(k1_xboole_0, C_74))=k2_xboole_0(A_5, k3_xboole_0(A_5, C_74)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_497])).
% 6.09/2.39  tff(c_547, plain, (![A_5, C_74]: (k2_xboole_0(A_5, k3_xboole_0(A_5, C_74))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_396, c_542])).
% 6.09/2.39  tff(c_6460, plain, (![A_251, A_252]: (k2_xboole_0(A_251, k4_xboole_0(A_251, A_252))=A_251)), inference(superposition, [status(thm), theory('equality')], [c_6228, c_547])).
% 6.09/2.39  tff(c_6581, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_563, c_6460])).
% 6.09/2.39  tff(c_1313, plain, (![A_109, B_110]: (k4_subset_1(u1_struct_0(A_109), B_110, k2_tops_1(A_109, B_110))=k2_pre_topc(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.09/2.39  tff(c_1317, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1313])).
% 6.09/2.39  tff(c_1321, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1317])).
% 6.09/2.39  tff(c_30, plain, (![A_29, B_30]: (m1_subset_1(k2_tops_1(A_29, B_30), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.09/2.39  tff(c_1071, plain, (![A_95, B_96, C_97]: (k4_subset_1(A_95, B_96, C_97)=k2_xboole_0(B_96, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.09/2.39  tff(c_4267, plain, (![A_205, B_206, B_207]: (k4_subset_1(u1_struct_0(A_205), B_206, k2_tops_1(A_205, B_207))=k2_xboole_0(B_206, k2_tops_1(A_205, B_207)) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(resolution, [status(thm)], [c_30, c_1071])).
% 6.09/2.39  tff(c_4271, plain, (![B_207]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_207))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_207)) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_4267])).
% 6.09/2.39  tff(c_4279, plain, (![B_208]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_208))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4271])).
% 6.09/2.39  tff(c_4286, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_4279])).
% 6.09/2.39  tff(c_4291, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1321, c_4286])).
% 6.09/2.39  tff(c_6645, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6581, c_4291])).
% 6.09/2.39  tff(c_6647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1169, c_6645])).
% 6.09/2.39  tff(c_6648, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 6.09/2.39  tff(c_7017, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7014, c_6648])).
% 6.09/2.39  tff(c_6649, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 6.09/2.39  tff(c_7396, plain, (![A_296, B_297]: (k2_pre_topc(A_296, B_297)=B_297 | ~v4_pre_topc(B_297, A_296) | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0(A_296))) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.09/2.39  tff(c_7399, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_7396])).
% 6.09/2.39  tff(c_7402, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6649, c_7399])).
% 6.09/2.39  tff(c_8233, plain, (![A_332, B_333]: (k7_subset_1(u1_struct_0(A_332), k2_pre_topc(A_332, B_333), k1_tops_1(A_332, B_333))=k2_tops_1(A_332, B_333) | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0(A_332))) | ~l1_pre_topc(A_332))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.09/2.39  tff(c_8242, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7402, c_8233])).
% 6.09/2.39  tff(c_8246, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_7014, c_8242])).
% 6.09/2.39  tff(c_8248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7017, c_8246])).
% 6.09/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.39  
% 6.09/2.39  Inference rules
% 6.09/2.39  ----------------------
% 6.09/2.39  #Ref     : 0
% 6.09/2.39  #Sup     : 2020
% 6.09/2.39  #Fact    : 0
% 6.09/2.39  #Define  : 0
% 6.09/2.39  #Split   : 2
% 6.09/2.39  #Chain   : 0
% 6.09/2.39  #Close   : 0
% 6.09/2.39  
% 6.09/2.39  Ordering : KBO
% 6.09/2.39  
% 6.09/2.39  Simplification rules
% 6.09/2.39  ----------------------
% 6.09/2.39  #Subsume      : 11
% 6.09/2.39  #Demod        : 1898
% 6.09/2.39  #Tautology    : 1561
% 6.09/2.39  #SimpNegUnit  : 4
% 6.09/2.39  #BackRed      : 13
% 6.09/2.39  
% 6.09/2.39  #Partial instantiations: 0
% 6.09/2.39  #Strategies tried      : 1
% 6.09/2.39  
% 6.09/2.39  Timing (in seconds)
% 6.09/2.39  ----------------------
% 6.09/2.39  Preprocessing        : 0.34
% 6.09/2.39  Parsing              : 0.19
% 6.09/2.39  CNF conversion       : 0.02
% 6.09/2.39  Main loop            : 1.22
% 6.09/2.39  Inferencing          : 0.36
% 6.09/2.39  Reduction            : 0.57
% 6.09/2.39  Demodulation         : 0.47
% 6.09/2.39  BG Simplification    : 0.04
% 6.09/2.39  Subsumption          : 0.17
% 6.09/2.39  Abstraction          : 0.05
% 6.09/2.39  MUC search           : 0.00
% 6.09/2.39  Cooper               : 0.00
% 6.09/2.39  Total                : 1.61
% 6.09/2.39  Index Insertion      : 0.00
% 6.09/2.39  Index Deletion       : 0.00
% 6.09/2.39  Index Matching       : 0.00
% 6.09/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

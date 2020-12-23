%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:34 EST 2020

% Result     : Theorem 8.11s
% Output     : CNFRefutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 357 expanded)
%              Number of leaves         :   47 ( 136 expanded)
%              Depth                    :   14
%              Number of atoms          :  240 ( 610 expanded)
%              Number of equality atoms :  114 ( 226 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
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

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10785,plain,(
    ! [A_406,B_407,C_408] :
      ( k7_subset_1(A_406,B_407,C_408) = k4_xboole_0(B_407,C_408)
      | ~ m1_subset_1(B_407,k1_zfmisc_1(A_406)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10795,plain,(
    ! [C_408] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_408) = k4_xboole_0('#skF_2',C_408) ),
    inference(resolution,[status(thm)],[c_52,c_10785])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_185,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_355,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2243,plain,(
    ! [A_168,B_169] :
      ( k4_subset_1(u1_struct_0(A_168),B_169,k2_tops_1(A_168,B_169)) = k2_pre_topc(A_168,B_169)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2248,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2243])).

tff(c_2258,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2248])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_120,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_131,plain,(
    ! [A_30] : r1_tarski(k1_xboole_0,A_30) ),
    inference(resolution,[status(thm)],[c_36,c_120])).

tff(c_169,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [A_67] :
      ( k1_xboole_0 = A_67
      | ~ r1_tarski(A_67,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_131,c_169])).

tff(c_201,plain,(
    ! [B_12] : k4_xboole_0(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_186])).

tff(c_261,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_273,plain,(
    ! [B_12] : k5_xboole_0(B_12,k1_xboole_0) = k2_xboole_0(B_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_261])).

tff(c_279,plain,(
    ! [B_12] : k5_xboole_0(B_12,k1_xboole_0) = B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_273])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1171,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(A_123,B_124) = k3_subset_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1180,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = k3_subset_1(A_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_1171])).

tff(c_1187,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1180])).

tff(c_811,plain,(
    ! [A_101,B_102] :
      ( k3_subset_1(A_101,k3_subset_1(A_101,B_102)) = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_822,plain,(
    ! [A_30] : k3_subset_1(A_30,k3_subset_1(A_30,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_811])).

tff(c_1189,plain,(
    ! [A_30] : k3_subset_1(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_822])).

tff(c_24,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_21] : m1_subset_1(k2_subset_1(A_21),k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_65,plain,(
    ! [A_21] : m1_subset_1(A_21,k1_zfmisc_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_1188,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_subset_1(A_21,A_21) ),
    inference(resolution,[status(thm)],[c_65,c_1171])).

tff(c_1223,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_1188])).

tff(c_226,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_255,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_226])).

tff(c_1224,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_255])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_425,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_448,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_425])).

tff(c_454,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k3_xboole_0(B_2,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_448])).

tff(c_1313,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_454])).

tff(c_1448,plain,(
    ! [A_130,B_131,C_132] :
      ( k7_subset_1(A_130,B_131,C_132) = k4_xboole_0(B_131,C_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1488,plain,(
    ! [C_137] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_137) = k4_xboole_0('#skF_2',C_137) ),
    inference(resolution,[status(thm)],[c_52,c_1448])).

tff(c_1500,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_1488])).

tff(c_109,plain,(
    ! [A_11,B_12] : k3_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k4_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_16,c_102])).

tff(c_1515,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1500,c_109])).

tff(c_1527,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1500,c_1515])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1959,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_8])).

tff(c_1971,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_1959])).

tff(c_22,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2016,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1971,c_22])).

tff(c_2029,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_2016])).

tff(c_821,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_811])).

tff(c_1185,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1171])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,k1_zfmisc_1(B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2134,plain,(
    ! [B_164,A_165] :
      ( k4_xboole_0(B_164,A_165) = k3_subset_1(B_164,A_165)
      | ~ r1_tarski(A_165,B_164) ) ),
    inference(resolution,[status(thm)],[c_40,c_1171])).

tff(c_2176,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_16,c_2134])).

tff(c_2200,plain,(
    ! [A_166,B_167] : k3_subset_1(A_166,k4_xboole_0(A_166,B_167)) = k3_xboole_0(A_166,B_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2176])).

tff(c_2221,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1185,c_2200])).

tff(c_2239,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_2221])).

tff(c_484,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(A_82,C_83)
      | ~ r1_tarski(B_84,C_83)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_598,plain,(
    ! [A_90,A_91,B_92] :
      ( r1_tarski(A_90,A_91)
      | ~ r1_tarski(A_90,k4_xboole_0(A_91,B_92)) ) ),
    inference(resolution,[status(thm)],[c_16,c_484])).

tff(c_696,plain,(
    ! [A_96,B_97,B_98] : r1_tarski(k4_xboole_0(k4_xboole_0(A_96,B_97),B_98),A_96) ),
    inference(resolution,[status(thm)],[c_16,c_598])).

tff(c_734,plain,(
    ! [A_14,B_15,B_98] : r1_tarski(k4_xboole_0(k3_xboole_0(A_14,B_15),B_98),A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_696])).

tff(c_2327,plain,(
    ! [B_171] : r1_tarski(k4_xboole_0('#skF_2',B_171),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2239,c_734])).

tff(c_2339,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1500,c_2327])).

tff(c_2040,plain,(
    ! [A_155,B_156,C_157] :
      ( k4_subset_1(A_155,B_156,C_157) = k2_xboole_0(B_156,C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(A_155))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8437,plain,(
    ! [B_300,B_301,A_302] :
      ( k4_subset_1(B_300,B_301,A_302) = k2_xboole_0(B_301,A_302)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(B_300))
      | ~ r1_tarski(A_302,B_300) ) ),
    inference(resolution,[status(thm)],[c_40,c_2040])).

tff(c_8840,plain,(
    ! [A_309] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_309) = k2_xboole_0('#skF_2',A_309)
      | ~ r1_tarski(A_309,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_8437])).

tff(c_8913,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2339,c_8840])).

tff(c_8990,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2258,c_2029,c_8913])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1653,plain,(
    ! [A_143,B_144] :
      ( v4_pre_topc(k2_pre_topc(A_143,B_144),A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1658,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1653])).

tff(c_1668,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1658])).

tff(c_9012,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8990,c_1668])).

tff(c_9014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_9012])).

tff(c_9015,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_9434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_9015])).

tff(c_9435,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_9613,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9435,c_58])).

tff(c_10829,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10795,c_9613])).

tff(c_11612,plain,(
    ! [A_445,B_446] :
      ( k4_subset_1(u1_struct_0(A_445),B_446,k2_tops_1(A_445,B_446)) = k2_pre_topc(A_445,B_446)
      | ~ m1_subset_1(B_446,k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ l1_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_11617,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_11612])).

tff(c_11627,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_11617])).

tff(c_9437,plain,(
    ! [A_340] :
      ( k1_xboole_0 = A_340
      | ~ r1_tarski(A_340,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_131,c_169])).

tff(c_9452,plain,(
    ! [B_12] : k4_xboole_0(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_9437])).

tff(c_9614,plain,(
    ! [A_348,B_349] : k5_xboole_0(A_348,k4_xboole_0(B_349,A_348)) = k2_xboole_0(A_348,B_349) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9632,plain,(
    ! [B_12] : k5_xboole_0(B_12,k1_xboole_0) = k2_xboole_0(B_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9452,c_9614])).

tff(c_9638,plain,(
    ! [B_12] : k5_xboole_0(B_12,k1_xboole_0) = B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9632])).

tff(c_10517,plain,(
    ! [A_399,B_400] :
      ( k4_xboole_0(A_399,B_400) = k3_subset_1(A_399,B_400)
      | ~ m1_subset_1(B_400,k1_zfmisc_1(A_399)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10526,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = k3_subset_1(A_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_10517])).

tff(c_10533,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10526])).

tff(c_10272,plain,(
    ! [A_389,B_390] :
      ( k3_subset_1(A_389,k3_subset_1(A_389,B_390)) = B_390
      | ~ m1_subset_1(B_390,k1_zfmisc_1(A_389)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10283,plain,(
    ! [A_30] : k3_subset_1(A_30,k3_subset_1(A_30,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_10272])).

tff(c_10535,plain,(
    ! [A_30] : k3_subset_1(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10533,c_10283])).

tff(c_10534,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_subset_1(A_21,A_21) ),
    inference(resolution,[status(thm)],[c_65,c_10517])).

tff(c_10596,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10535,c_10534])).

tff(c_9477,plain,(
    ! [A_342,B_343] : k4_xboole_0(A_342,k4_xboole_0(A_342,B_343)) = k3_xboole_0(A_342,B_343) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9506,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_9477])).

tff(c_10597,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10596,c_9506])).

tff(c_9677,plain,(
    ! [A_352,B_353] : k5_xboole_0(A_352,k3_xboole_0(A_352,B_353)) = k4_xboole_0(A_352,B_353) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9700,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_9677])).

tff(c_9706,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k3_xboole_0(B_2,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9506,c_9700])).

tff(c_10660,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10597,c_9706])).

tff(c_11095,plain,(
    ! [A_426,B_427] :
      ( r1_tarski(k2_tops_1(A_426,B_427),B_427)
      | ~ v4_pre_topc(B_427,A_426)
      | ~ m1_subset_1(B_427,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_pre_topc(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_11100,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_11095])).

tff(c_11110,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_9435,c_11100])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11122,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_11110,c_14])).

tff(c_11265,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11122,c_8])).

tff(c_11277,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10660,c_11265])).

tff(c_11297,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11277,c_22])).

tff(c_11310,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9638,c_11297])).

tff(c_130,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_120])).

tff(c_9736,plain,(
    ! [A_355,C_356,B_357] :
      ( r1_tarski(A_355,C_356)
      | ~ r1_tarski(B_357,C_356)
      | ~ r1_tarski(A_355,B_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9773,plain,(
    ! [A_360] :
      ( r1_tarski(A_360,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_360,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_130,c_9736])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_17596,plain,(
    ! [A_575,A_576] :
      ( r1_tarski(A_575,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_575,A_576)
      | ~ r1_tarski(A_576,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_9773,c_12])).

tff(c_17660,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_11110,c_17596])).

tff(c_17750,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17660])).

tff(c_11359,plain,(
    ! [A_434,B_435,C_436] :
      ( k4_subset_1(A_434,B_435,C_436) = k2_xboole_0(B_435,C_436)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(A_434))
      | ~ m1_subset_1(B_435,k1_zfmisc_1(A_434)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18610,plain,(
    ! [B_588,B_589,A_590] :
      ( k4_subset_1(B_588,B_589,A_590) = k2_xboole_0(B_589,A_590)
      | ~ m1_subset_1(B_589,k1_zfmisc_1(B_588))
      | ~ r1_tarski(A_590,B_588) ) ),
    inference(resolution,[status(thm)],[c_40,c_11359])).

tff(c_18640,plain,(
    ! [A_591] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_591) = k2_xboole_0('#skF_2',A_591)
      | ~ r1_tarski(A_591,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_18610])).

tff(c_18659,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_17750,c_18640])).

tff(c_18782,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11627,c_11310,c_18659])).

tff(c_46,plain,(
    ! [A_38,B_40] :
      ( k7_subset_1(u1_struct_0(A_38),k2_pre_topc(A_38,B_40),k1_tops_1(A_38,B_40)) = k2_tops_1(A_38,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18833,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18782,c_46])).

tff(c_18839,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_10795,c_18833])).

tff(c_18841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10829,c_18839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.11/3.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.11/3.13  
% 8.11/3.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.11/3.13  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.11/3.13  
% 8.11/3.13  %Foreground sorts:
% 8.11/3.13  
% 8.11/3.13  
% 8.11/3.13  %Background operators:
% 8.11/3.13  
% 8.11/3.13  
% 8.11/3.13  %Foreground operators:
% 8.11/3.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.11/3.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.11/3.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.11/3.13  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.11/3.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.11/3.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.11/3.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.11/3.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.11/3.13  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.11/3.13  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.11/3.13  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.11/3.13  tff('#skF_2', type, '#skF_2': $i).
% 8.11/3.13  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.11/3.13  tff('#skF_1', type, '#skF_1': $i).
% 8.11/3.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.11/3.13  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.11/3.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.11/3.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.11/3.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.11/3.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.11/3.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.11/3.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.11/3.13  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.11/3.13  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.11/3.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.11/3.13  
% 8.26/3.16  tff(f_130, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 8.26/3.16  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.26/3.16  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 8.26/3.16  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.26/3.16  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.26/3.16  tff(f_77, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.26/3.16  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.26/3.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.26/3.16  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.26/3.16  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.26/3.16  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.26/3.16  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.26/3.16  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.26/3.16  tff(f_61, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.26/3.16  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.26/3.16  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.26/3.16  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.26/3.16  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.26/3.16  tff(f_71, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.26/3.16  tff(f_95, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 8.26/3.16  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 8.26/3.16  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 8.26/3.16  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.26/3.16  tff(c_10785, plain, (![A_406, B_407, C_408]: (k7_subset_1(A_406, B_407, C_408)=k4_xboole_0(B_407, C_408) | ~m1_subset_1(B_407, k1_zfmisc_1(A_406)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.26/3.16  tff(c_10795, plain, (![C_408]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_408)=k4_xboole_0('#skF_2', C_408))), inference(resolution, [status(thm)], [c_52, c_10785])).
% 8.26/3.16  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.26/3.16  tff(c_185, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 8.26/3.16  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.26/3.16  tff(c_355, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 8.26/3.16  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.26/3.16  tff(c_2243, plain, (![A_168, B_169]: (k4_subset_1(u1_struct_0(A_168), B_169, k2_tops_1(A_168, B_169))=k2_pre_topc(A_168, B_169) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.26/3.16  tff(c_2248, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2243])).
% 8.26/3.16  tff(c_2258, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2248])).
% 8.26/3.16  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.26/3.16  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.26/3.16  tff(c_36, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.26/3.16  tff(c_120, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.26/3.16  tff(c_131, plain, (![A_30]: (r1_tarski(k1_xboole_0, A_30))), inference(resolution, [status(thm)], [c_36, c_120])).
% 8.26/3.16  tff(c_169, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.26/3.16  tff(c_186, plain, (![A_67]: (k1_xboole_0=A_67 | ~r1_tarski(A_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_131, c_169])).
% 8.26/3.16  tff(c_201, plain, (![B_12]: (k4_xboole_0(k1_xboole_0, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_186])).
% 8.26/3.16  tff(c_261, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.26/3.16  tff(c_273, plain, (![B_12]: (k5_xboole_0(B_12, k1_xboole_0)=k2_xboole_0(B_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_201, c_261])).
% 8.26/3.16  tff(c_279, plain, (![B_12]: (k5_xboole_0(B_12, k1_xboole_0)=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_273])).
% 8.26/3.16  tff(c_18, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.26/3.16  tff(c_1171, plain, (![A_123, B_124]: (k4_xboole_0(A_123, B_124)=k3_subset_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.26/3.16  tff(c_1180, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=k3_subset_1(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_1171])).
% 8.26/3.16  tff(c_1187, plain, (![A_30]: (k3_subset_1(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1180])).
% 8.26/3.16  tff(c_811, plain, (![A_101, B_102]: (k3_subset_1(A_101, k3_subset_1(A_101, B_102))=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.26/3.16  tff(c_822, plain, (![A_30]: (k3_subset_1(A_30, k3_subset_1(A_30, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_811])).
% 8.26/3.16  tff(c_1189, plain, (![A_30]: (k3_subset_1(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_822])).
% 8.26/3.16  tff(c_24, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.26/3.16  tff(c_28, plain, (![A_21]: (m1_subset_1(k2_subset_1(A_21), k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.26/3.16  tff(c_65, plain, (![A_21]: (m1_subset_1(A_21, k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 8.26/3.16  tff(c_1188, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_subset_1(A_21, A_21))), inference(resolution, [status(thm)], [c_65, c_1171])).
% 8.26/3.16  tff(c_1223, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_1188])).
% 8.26/3.16  tff(c_226, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.26/3.16  tff(c_255, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_226])).
% 8.26/3.16  tff(c_1224, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1223, c_255])).
% 8.26/3.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.26/3.16  tff(c_102, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.26/3.16  tff(c_110, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_102])).
% 8.26/3.16  tff(c_425, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.26/3.16  tff(c_448, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_110, c_425])).
% 8.26/3.16  tff(c_454, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k3_xboole_0(B_2, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_448])).
% 8.26/3.16  tff(c_1313, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1224, c_454])).
% 8.26/3.16  tff(c_1448, plain, (![A_130, B_131, C_132]: (k7_subset_1(A_130, B_131, C_132)=k4_xboole_0(B_131, C_132) | ~m1_subset_1(B_131, k1_zfmisc_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.26/3.16  tff(c_1488, plain, (![C_137]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_137)=k4_xboole_0('#skF_2', C_137))), inference(resolution, [status(thm)], [c_52, c_1448])).
% 8.26/3.16  tff(c_1500, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_185, c_1488])).
% 8.26/3.16  tff(c_109, plain, (![A_11, B_12]: (k3_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k4_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_102])).
% 8.26/3.16  tff(c_1515, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1500, c_109])).
% 8.26/3.16  tff(c_1527, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1500, c_1515])).
% 8.26/3.16  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.26/3.16  tff(c_1959, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1527, c_8])).
% 8.26/3.16  tff(c_1971, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_1959])).
% 8.26/3.16  tff(c_22, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.26/3.16  tff(c_2016, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1971, c_22])).
% 8.26/3.16  tff(c_2029, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_2016])).
% 8.26/3.16  tff(c_821, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_52, c_811])).
% 8.26/3.16  tff(c_1185, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_52, c_1171])).
% 8.26/3.16  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.26/3.16  tff(c_40, plain, (![A_31, B_32]: (m1_subset_1(A_31, k1_zfmisc_1(B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.26/3.16  tff(c_2134, plain, (![B_164, A_165]: (k4_xboole_0(B_164, A_165)=k3_subset_1(B_164, A_165) | ~r1_tarski(A_165, B_164))), inference(resolution, [status(thm)], [c_40, c_1171])).
% 8.26/3.16  tff(c_2176, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_subset_1(A_11, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_16, c_2134])).
% 8.26/3.16  tff(c_2200, plain, (![A_166, B_167]: (k3_subset_1(A_166, k4_xboole_0(A_166, B_167))=k3_xboole_0(A_166, B_167))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2176])).
% 8.26/3.16  tff(c_2221, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1185, c_2200])).
% 8.26/3.16  tff(c_2239, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_821, c_2221])).
% 8.26/3.16  tff(c_484, plain, (![A_82, C_83, B_84]: (r1_tarski(A_82, C_83) | ~r1_tarski(B_84, C_83) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.26/3.16  tff(c_598, plain, (![A_90, A_91, B_92]: (r1_tarski(A_90, A_91) | ~r1_tarski(A_90, k4_xboole_0(A_91, B_92)))), inference(resolution, [status(thm)], [c_16, c_484])).
% 8.26/3.16  tff(c_696, plain, (![A_96, B_97, B_98]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_96, B_97), B_98), A_96))), inference(resolution, [status(thm)], [c_16, c_598])).
% 8.26/3.16  tff(c_734, plain, (![A_14, B_15, B_98]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_14, B_15), B_98), A_14))), inference(superposition, [status(thm), theory('equality')], [c_20, c_696])).
% 8.26/3.16  tff(c_2327, plain, (![B_171]: (r1_tarski(k4_xboole_0('#skF_2', B_171), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2239, c_734])).
% 8.26/3.16  tff(c_2339, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1500, c_2327])).
% 8.26/3.16  tff(c_2040, plain, (![A_155, B_156, C_157]: (k4_subset_1(A_155, B_156, C_157)=k2_xboole_0(B_156, C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(A_155)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.26/3.16  tff(c_8437, plain, (![B_300, B_301, A_302]: (k4_subset_1(B_300, B_301, A_302)=k2_xboole_0(B_301, A_302) | ~m1_subset_1(B_301, k1_zfmisc_1(B_300)) | ~r1_tarski(A_302, B_300))), inference(resolution, [status(thm)], [c_40, c_2040])).
% 8.26/3.16  tff(c_8840, plain, (![A_309]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_309)=k2_xboole_0('#skF_2', A_309) | ~r1_tarski(A_309, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_8437])).
% 8.26/3.16  tff(c_8913, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2339, c_8840])).
% 8.26/3.16  tff(c_8990, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2258, c_2029, c_8913])).
% 8.26/3.16  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.26/3.16  tff(c_1653, plain, (![A_143, B_144]: (v4_pre_topc(k2_pre_topc(A_143, B_144), A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.26/3.16  tff(c_1658, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1653])).
% 8.26/3.16  tff(c_1668, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1658])).
% 8.26/3.16  tff(c_9012, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8990, c_1668])).
% 8.26/3.16  tff(c_9014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_355, c_9012])).
% 8.26/3.16  tff(c_9015, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 8.26/3.16  tff(c_9434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_9015])).
% 8.26/3.16  tff(c_9435, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 8.26/3.16  tff(c_9613, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9435, c_58])).
% 8.26/3.16  tff(c_10829, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10795, c_9613])).
% 8.26/3.16  tff(c_11612, plain, (![A_445, B_446]: (k4_subset_1(u1_struct_0(A_445), B_446, k2_tops_1(A_445, B_446))=k2_pre_topc(A_445, B_446) | ~m1_subset_1(B_446, k1_zfmisc_1(u1_struct_0(A_445))) | ~l1_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.26/3.16  tff(c_11617, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_11612])).
% 8.26/3.16  tff(c_11627, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_11617])).
% 8.26/3.16  tff(c_9437, plain, (![A_340]: (k1_xboole_0=A_340 | ~r1_tarski(A_340, k1_xboole_0))), inference(resolution, [status(thm)], [c_131, c_169])).
% 8.26/3.16  tff(c_9452, plain, (![B_12]: (k4_xboole_0(k1_xboole_0, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_9437])).
% 8.26/3.16  tff(c_9614, plain, (![A_348, B_349]: (k5_xboole_0(A_348, k4_xboole_0(B_349, A_348))=k2_xboole_0(A_348, B_349))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.26/3.16  tff(c_9632, plain, (![B_12]: (k5_xboole_0(B_12, k1_xboole_0)=k2_xboole_0(B_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9452, c_9614])).
% 8.26/3.16  tff(c_9638, plain, (![B_12]: (k5_xboole_0(B_12, k1_xboole_0)=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9632])).
% 8.26/3.16  tff(c_10517, plain, (![A_399, B_400]: (k4_xboole_0(A_399, B_400)=k3_subset_1(A_399, B_400) | ~m1_subset_1(B_400, k1_zfmisc_1(A_399)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.26/3.16  tff(c_10526, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=k3_subset_1(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_10517])).
% 8.26/3.16  tff(c_10533, plain, (![A_30]: (k3_subset_1(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10526])).
% 8.26/3.16  tff(c_10272, plain, (![A_389, B_390]: (k3_subset_1(A_389, k3_subset_1(A_389, B_390))=B_390 | ~m1_subset_1(B_390, k1_zfmisc_1(A_389)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.26/3.16  tff(c_10283, plain, (![A_30]: (k3_subset_1(A_30, k3_subset_1(A_30, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_10272])).
% 8.26/3.16  tff(c_10535, plain, (![A_30]: (k3_subset_1(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10533, c_10283])).
% 8.26/3.16  tff(c_10534, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_subset_1(A_21, A_21))), inference(resolution, [status(thm)], [c_65, c_10517])).
% 8.26/3.16  tff(c_10596, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10535, c_10534])).
% 8.26/3.16  tff(c_9477, plain, (![A_342, B_343]: (k4_xboole_0(A_342, k4_xboole_0(A_342, B_343))=k3_xboole_0(A_342, B_343))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.26/3.16  tff(c_9506, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_9477])).
% 8.26/3.16  tff(c_10597, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10596, c_9506])).
% 8.26/3.16  tff(c_9677, plain, (![A_352, B_353]: (k5_xboole_0(A_352, k3_xboole_0(A_352, B_353))=k4_xboole_0(A_352, B_353))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.26/3.16  tff(c_9700, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_110, c_9677])).
% 8.26/3.16  tff(c_9706, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k3_xboole_0(B_2, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_9506, c_9700])).
% 8.26/3.16  tff(c_10660, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10597, c_9706])).
% 8.26/3.16  tff(c_11095, plain, (![A_426, B_427]: (r1_tarski(k2_tops_1(A_426, B_427), B_427) | ~v4_pre_topc(B_427, A_426) | ~m1_subset_1(B_427, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_pre_topc(A_426))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.26/3.16  tff(c_11100, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_11095])).
% 8.26/3.16  tff(c_11110, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_9435, c_11100])).
% 8.26/3.16  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.26/3.16  tff(c_11122, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_11110, c_14])).
% 8.26/3.16  tff(c_11265, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11122, c_8])).
% 8.26/3.16  tff(c_11277, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10660, c_11265])).
% 8.26/3.16  tff(c_11297, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11277, c_22])).
% 8.26/3.16  tff(c_11310, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9638, c_11297])).
% 8.26/3.16  tff(c_130, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_120])).
% 8.26/3.16  tff(c_9736, plain, (![A_355, C_356, B_357]: (r1_tarski(A_355, C_356) | ~r1_tarski(B_357, C_356) | ~r1_tarski(A_355, B_357))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.26/3.16  tff(c_9773, plain, (![A_360]: (r1_tarski(A_360, u1_struct_0('#skF_1')) | ~r1_tarski(A_360, '#skF_2'))), inference(resolution, [status(thm)], [c_130, c_9736])).
% 8.26/3.16  tff(c_12, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.26/3.16  tff(c_17596, plain, (![A_575, A_576]: (r1_tarski(A_575, u1_struct_0('#skF_1')) | ~r1_tarski(A_575, A_576) | ~r1_tarski(A_576, '#skF_2'))), inference(resolution, [status(thm)], [c_9773, c_12])).
% 8.26/3.16  tff(c_17660, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_11110, c_17596])).
% 8.26/3.16  tff(c_17750, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_17660])).
% 8.26/3.16  tff(c_11359, plain, (![A_434, B_435, C_436]: (k4_subset_1(A_434, B_435, C_436)=k2_xboole_0(B_435, C_436) | ~m1_subset_1(C_436, k1_zfmisc_1(A_434)) | ~m1_subset_1(B_435, k1_zfmisc_1(A_434)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.26/3.16  tff(c_18610, plain, (![B_588, B_589, A_590]: (k4_subset_1(B_588, B_589, A_590)=k2_xboole_0(B_589, A_590) | ~m1_subset_1(B_589, k1_zfmisc_1(B_588)) | ~r1_tarski(A_590, B_588))), inference(resolution, [status(thm)], [c_40, c_11359])).
% 8.26/3.16  tff(c_18640, plain, (![A_591]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_591)=k2_xboole_0('#skF_2', A_591) | ~r1_tarski(A_591, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_18610])).
% 8.26/3.16  tff(c_18659, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_17750, c_18640])).
% 8.26/3.16  tff(c_18782, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11627, c_11310, c_18659])).
% 8.26/3.16  tff(c_46, plain, (![A_38, B_40]: (k7_subset_1(u1_struct_0(A_38), k2_pre_topc(A_38, B_40), k1_tops_1(A_38, B_40))=k2_tops_1(A_38, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.26/3.16  tff(c_18833, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18782, c_46])).
% 8.26/3.16  tff(c_18839, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_10795, c_18833])).
% 8.26/3.16  tff(c_18841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10829, c_18839])).
% 8.26/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.26/3.16  
% 8.26/3.16  Inference rules
% 8.26/3.16  ----------------------
% 8.26/3.16  #Ref     : 0
% 8.26/3.16  #Sup     : 4449
% 8.26/3.16  #Fact    : 0
% 8.26/3.16  #Define  : 0
% 8.26/3.16  #Split   : 6
% 8.26/3.16  #Chain   : 0
% 8.26/3.16  #Close   : 0
% 8.26/3.16  
% 8.26/3.16  Ordering : KBO
% 8.26/3.16  
% 8.26/3.16  Simplification rules
% 8.26/3.16  ----------------------
% 8.26/3.16  #Subsume      : 224
% 8.26/3.16  #Demod        : 3755
% 8.26/3.16  #Tautology    : 2741
% 8.26/3.16  #SimpNegUnit  : 2
% 8.26/3.16  #BackRed      : 23
% 8.26/3.16  
% 8.26/3.16  #Partial instantiations: 0
% 8.26/3.16  #Strategies tried      : 1
% 8.26/3.16  
% 8.26/3.16  Timing (in seconds)
% 8.26/3.16  ----------------------
% 8.26/3.16  Preprocessing        : 0.33
% 8.26/3.16  Parsing              : 0.18
% 8.26/3.16  CNF conversion       : 0.02
% 8.26/3.16  Main loop            : 2.01
% 8.26/3.16  Inferencing          : 0.52
% 8.26/3.16  Reduction            : 0.89
% 8.26/3.16  Demodulation         : 0.72
% 8.26/3.16  BG Simplification    : 0.06
% 8.26/3.16  Subsumption          : 0.39
% 8.26/3.16  Abstraction          : 0.10
% 8.26/3.16  MUC search           : 0.00
% 8.26/3.16  Cooper               : 0.00
% 8.26/3.16  Total                : 2.40
% 8.26/3.16  Index Insertion      : 0.00
% 8.26/3.16  Index Deletion       : 0.00
% 8.26/3.16  Index Matching       : 0.00
% 8.26/3.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

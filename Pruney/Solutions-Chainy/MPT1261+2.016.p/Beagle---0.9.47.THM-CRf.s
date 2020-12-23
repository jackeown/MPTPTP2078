%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:13 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 181 expanded)
%              Number of leaves         :   43 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  155 ( 303 expanded)
%              Number of equality atoms :   75 ( 117 expanded)
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

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6127,plain,(
    ! [A_205,B_206,C_207] :
      ( k7_subset_1(A_205,B_206,C_207) = k4_xboole_0(B_206,C_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(A_205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6130,plain,(
    ! [C_207] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_207) = k4_xboole_0('#skF_2',C_207) ),
    inference(resolution,[status(thm)],[c_42,c_6127])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_114,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2162,plain,(
    ! [A_126,B_127] :
      ( k4_subset_1(u1_struct_0(A_126),B_127,k2_tops_1(A_126,B_127)) = k2_pre_topc(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2166,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2162])).

tff(c_2170,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2166])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_270,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_54])).

tff(c_684,plain,(
    ! [A_80,B_81,C_82] :
      ( k7_subset_1(A_80,B_81,C_82) = k4_xboole_0(B_81,C_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_988,plain,(
    ! [C_97] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_97) = k4_xboole_0('#skF_2',C_97) ),
    inference(resolution,[status(thm)],[c_42,c_684])).

tff(c_1000,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_988])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_422,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_441,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_422])).

tff(c_471,plain,(
    ! [B_72] : k4_xboole_0(k1_xboole_0,B_72) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_441])).

tff(c_22,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_486,plain,(
    ! [B_72] : k5_xboole_0(B_72,k1_xboole_0) = k2_xboole_0(B_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_22])).

tff(c_511,plain,(
    ! [B_72] : k5_xboole_0(B_72,k1_xboole_0) = B_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_486])).

tff(c_24,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_115,plain,(
    ! [A_48,B_49] : k1_setfam_1(k2_tarski(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_200,plain,(
    ! [B_57,A_58] : k1_setfam_1(k2_tarski(B_57,A_58)) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_115])).

tff(c_30,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_223,plain,(
    ! [B_59,A_60] : k3_xboole_0(B_59,A_60) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_30])).

tff(c_130,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    ! [A_8] : k3_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_130])).

tff(c_239,plain,(
    ! [B_59] : k3_xboole_0(B_59,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_142])).

tff(c_18,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_321,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_342,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_321])).

tff(c_345,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_342])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_558,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_587,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_558])).

tff(c_594,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_587])).

tff(c_623,plain,(
    ! [A_78,B_79] : k3_xboole_0(k4_xboole_0(A_78,B_79),A_78) = k4_xboole_0(A_78,B_79) ),
    inference(resolution,[status(thm)],[c_16,c_130])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_629,plain,(
    ! [A_78,B_79] : k5_xboole_0(k4_xboole_0(A_78,B_79),k4_xboole_0(A_78,B_79)) = k4_xboole_0(k4_xboole_0(A_78,B_79),A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_8])).

tff(c_688,plain,(
    ! [A_83,B_84] : k4_xboole_0(k4_xboole_0(A_83,B_84),A_83) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_629])).

tff(c_702,plain,(
    ! [A_83,B_84] : k2_xboole_0(A_83,k4_xboole_0(A_83,B_84)) = k5_xboole_0(A_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_22])).

tff(c_735,plain,(
    ! [A_83,B_84] : k2_xboole_0(A_83,k4_xboole_0(A_83,B_84)) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_702])).

tff(c_1188,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_735])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k2_tops_1(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1544,plain,(
    ! [A_110,B_111,C_112] :
      ( k4_subset_1(A_110,B_111,C_112) = k2_xboole_0(B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5715,plain,(
    ! [A_177,B_178,B_179] :
      ( k4_subset_1(u1_struct_0(A_177),B_178,k2_tops_1(A_177,B_179)) = k2_xboole_0(B_178,k2_tops_1(A_177,B_179))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_32,c_1544])).

tff(c_5719,plain,(
    ! [B_179] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_179)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_179))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_5715])).

tff(c_5726,plain,(
    ! [B_180] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_180)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_180))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5719])).

tff(c_5733,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_5726])).

tff(c_5738,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2170,c_1188,c_5733])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1208,plain,(
    ! [A_102,B_103] :
      ( v4_pre_topc(k2_pre_topc(A_102,B_103),A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1212,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1208])).

tff(c_1216,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1212])).

tff(c_5740,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5738,c_1216])).

tff(c_5742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_5740])).

tff(c_5743,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6215,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6130,c_5743])).

tff(c_5745,plain,(
    ! [A_181,B_182] : k1_setfam_1(k2_tarski(A_181,B_182)) = k3_xboole_0(A_181,B_182) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5830,plain,(
    ! [A_190,B_191] : k1_setfam_1(k2_tarski(A_190,B_191)) = k3_xboole_0(B_191,A_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5745])).

tff(c_5836,plain,(
    ! [B_191,A_190] : k3_xboole_0(B_191,A_190) = k3_xboole_0(A_190,B_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_5830,c_30])).

tff(c_5744,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_7162,plain,(
    ! [A_247,B_248] :
      ( r1_tarski(k2_tops_1(A_247,B_248),B_248)
      | ~ v4_pre_topc(B_248,A_247)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7166,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_7162])).

tff(c_7170,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5744,c_7166])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7177,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_7170,c_12])).

tff(c_7227,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5836,c_7177])).

tff(c_7349,plain,(
    ! [A_250,B_251] :
      ( k7_subset_1(u1_struct_0(A_250),B_251,k2_tops_1(A_250,B_251)) = k1_tops_1(A_250,B_251)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7353,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_7349])).

tff(c_7357,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6130,c_7353])).

tff(c_20,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7370,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7357,c_20])).

tff(c_7380,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7227,c_7370])).

tff(c_7382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6215,c_7380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.25  
% 5.98/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.25  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.98/2.25  
% 5.98/2.25  %Foreground sorts:
% 5.98/2.25  
% 5.98/2.25  
% 5.98/2.25  %Background operators:
% 5.98/2.25  
% 5.98/2.25  
% 5.98/2.25  %Foreground operators:
% 5.98/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.98/2.25  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.98/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.98/2.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.98/2.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.98/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.98/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.98/2.25  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.98/2.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.98/2.25  tff('#skF_2', type, '#skF_2': $i).
% 5.98/2.25  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.98/2.25  tff('#skF_1', type, '#skF_1': $i).
% 5.98/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.98/2.25  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.98/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.98/2.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.98/2.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.98/2.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.98/2.25  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.98/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.98/2.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.98/2.25  
% 5.98/2.27  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.98/2.27  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.98/2.27  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.98/2.27  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.98/2.27  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.98/2.27  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.98/2.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.98/2.27  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.98/2.27  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.98/2.27  tff(f_63, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.98/2.27  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.98/2.27  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.98/2.27  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.98/2.27  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.98/2.27  tff(f_69, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.98/2.27  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.98/2.27  tff(f_77, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 5.98/2.27  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.98/2.27  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.98/2.27  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.98/2.27  tff(c_6127, plain, (![A_205, B_206, C_207]: (k7_subset_1(A_205, B_206, C_207)=k4_xboole_0(B_206, C_207) | ~m1_subset_1(B_206, k1_zfmisc_1(A_205)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.98/2.27  tff(c_6130, plain, (![C_207]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_207)=k4_xboole_0('#skF_2', C_207))), inference(resolution, [status(thm)], [c_42, c_6127])).
% 5.98/2.27  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.98/2.27  tff(c_114, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 5.98/2.27  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.98/2.27  tff(c_2162, plain, (![A_126, B_127]: (k4_subset_1(u1_struct_0(A_126), B_127, k2_tops_1(A_126, B_127))=k2_pre_topc(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.98/2.27  tff(c_2166, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2162])).
% 5.98/2.27  tff(c_2170, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2166])).
% 5.98/2.27  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.98/2.27  tff(c_270, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_114, c_54])).
% 5.98/2.27  tff(c_684, plain, (![A_80, B_81, C_82]: (k7_subset_1(A_80, B_81, C_82)=k4_xboole_0(B_81, C_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.98/2.27  tff(c_988, plain, (![C_97]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_97)=k4_xboole_0('#skF_2', C_97))), inference(resolution, [status(thm)], [c_42, c_684])).
% 5.98/2.27  tff(c_1000, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_270, c_988])).
% 5.98/2.27  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.98/2.27  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.98/2.27  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.98/2.27  tff(c_422, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.98/2.27  tff(c_441, plain, (![A_71]: (k1_xboole_0=A_71 | ~r1_tarski(A_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_422])).
% 5.98/2.27  tff(c_471, plain, (![B_72]: (k4_xboole_0(k1_xboole_0, B_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_441])).
% 5.98/2.27  tff(c_22, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.98/2.27  tff(c_486, plain, (![B_72]: (k5_xboole_0(B_72, k1_xboole_0)=k2_xboole_0(B_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_471, c_22])).
% 5.98/2.27  tff(c_511, plain, (![B_72]: (k5_xboole_0(B_72, k1_xboole_0)=B_72)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_486])).
% 5.98/2.27  tff(c_24, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.98/2.27  tff(c_115, plain, (![A_48, B_49]: (k1_setfam_1(k2_tarski(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.98/2.27  tff(c_200, plain, (![B_57, A_58]: (k1_setfam_1(k2_tarski(B_57, A_58))=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_24, c_115])).
% 5.98/2.27  tff(c_30, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.98/2.27  tff(c_223, plain, (![B_59, A_60]: (k3_xboole_0(B_59, A_60)=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_200, c_30])).
% 5.98/2.27  tff(c_130, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.98/2.27  tff(c_142, plain, (![A_8]: (k3_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_130])).
% 5.98/2.27  tff(c_239, plain, (![B_59]: (k3_xboole_0(B_59, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_223, c_142])).
% 5.98/2.27  tff(c_18, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.98/2.27  tff(c_321, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.27  tff(c_342, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_321])).
% 5.98/2.27  tff(c_345, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_239, c_342])).
% 5.98/2.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.98/2.27  tff(c_141, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_130])).
% 5.98/2.27  tff(c_558, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.98/2.27  tff(c_587, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_141, c_558])).
% 5.98/2.27  tff(c_594, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_587])).
% 5.98/2.27  tff(c_623, plain, (![A_78, B_79]: (k3_xboole_0(k4_xboole_0(A_78, B_79), A_78)=k4_xboole_0(A_78, B_79))), inference(resolution, [status(thm)], [c_16, c_130])).
% 5.98/2.27  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.98/2.27  tff(c_629, plain, (![A_78, B_79]: (k5_xboole_0(k4_xboole_0(A_78, B_79), k4_xboole_0(A_78, B_79))=k4_xboole_0(k4_xboole_0(A_78, B_79), A_78))), inference(superposition, [status(thm), theory('equality')], [c_623, c_8])).
% 5.98/2.27  tff(c_688, plain, (![A_83, B_84]: (k4_xboole_0(k4_xboole_0(A_83, B_84), A_83)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_594, c_629])).
% 5.98/2.27  tff(c_702, plain, (![A_83, B_84]: (k2_xboole_0(A_83, k4_xboole_0(A_83, B_84))=k5_xboole_0(A_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_688, c_22])).
% 5.98/2.27  tff(c_735, plain, (![A_83, B_84]: (k2_xboole_0(A_83, k4_xboole_0(A_83, B_84))=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_511, c_702])).
% 5.98/2.27  tff(c_1188, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1000, c_735])).
% 5.98/2.27  tff(c_32, plain, (![A_26, B_27]: (m1_subset_1(k2_tops_1(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.98/2.27  tff(c_1544, plain, (![A_110, B_111, C_112]: (k4_subset_1(A_110, B_111, C_112)=k2_xboole_0(B_111, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_110)) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.98/2.27  tff(c_5715, plain, (![A_177, B_178, B_179]: (k4_subset_1(u1_struct_0(A_177), B_178, k2_tops_1(A_177, B_179))=k2_xboole_0(B_178, k2_tops_1(A_177, B_179)) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(resolution, [status(thm)], [c_32, c_1544])).
% 5.98/2.27  tff(c_5719, plain, (![B_179]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_179))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_179)) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_5715])).
% 5.98/2.27  tff(c_5726, plain, (![B_180]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_180))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_180)) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5719])).
% 5.98/2.27  tff(c_5733, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_5726])).
% 5.98/2.27  tff(c_5738, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2170, c_1188, c_5733])).
% 5.98/2.27  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.98/2.27  tff(c_1208, plain, (![A_102, B_103]: (v4_pre_topc(k2_pre_topc(A_102, B_103), A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.98/2.27  tff(c_1212, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1208])).
% 5.98/2.27  tff(c_1216, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1212])).
% 5.98/2.27  tff(c_5740, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5738, c_1216])).
% 5.98/2.27  tff(c_5742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_5740])).
% 5.98/2.27  tff(c_5743, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 5.98/2.27  tff(c_6215, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6130, c_5743])).
% 5.98/2.27  tff(c_5745, plain, (![A_181, B_182]: (k1_setfam_1(k2_tarski(A_181, B_182))=k3_xboole_0(A_181, B_182))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.98/2.27  tff(c_5830, plain, (![A_190, B_191]: (k1_setfam_1(k2_tarski(A_190, B_191))=k3_xboole_0(B_191, A_190))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5745])).
% 5.98/2.27  tff(c_5836, plain, (![B_191, A_190]: (k3_xboole_0(B_191, A_190)=k3_xboole_0(A_190, B_191))), inference(superposition, [status(thm), theory('equality')], [c_5830, c_30])).
% 5.98/2.27  tff(c_5744, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 5.98/2.27  tff(c_7162, plain, (![A_247, B_248]: (r1_tarski(k2_tops_1(A_247, B_248), B_248) | ~v4_pre_topc(B_248, A_247) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.98/2.27  tff(c_7166, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_7162])).
% 5.98/2.27  tff(c_7170, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5744, c_7166])).
% 5.98/2.27  tff(c_12, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.98/2.27  tff(c_7177, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_7170, c_12])).
% 5.98/2.27  tff(c_7227, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5836, c_7177])).
% 5.98/2.27  tff(c_7349, plain, (![A_250, B_251]: (k7_subset_1(u1_struct_0(A_250), B_251, k2_tops_1(A_250, B_251))=k1_tops_1(A_250, B_251) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.98/2.27  tff(c_7353, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_7349])).
% 5.98/2.27  tff(c_7357, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6130, c_7353])).
% 5.98/2.27  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.27  tff(c_7370, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7357, c_20])).
% 5.98/2.27  tff(c_7380, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7227, c_7370])).
% 5.98/2.27  tff(c_7382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6215, c_7380])).
% 5.98/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.27  
% 5.98/2.27  Inference rules
% 5.98/2.27  ----------------------
% 5.98/2.27  #Ref     : 0
% 5.98/2.27  #Sup     : 1788
% 5.98/2.27  #Fact    : 0
% 5.98/2.27  #Define  : 0
% 5.98/2.27  #Split   : 3
% 5.98/2.27  #Chain   : 0
% 5.98/2.27  #Close   : 0
% 5.98/2.27  
% 5.98/2.27  Ordering : KBO
% 5.98/2.27  
% 5.98/2.27  Simplification rules
% 5.98/2.27  ----------------------
% 5.98/2.27  #Subsume      : 138
% 5.98/2.27  #Demod        : 2500
% 5.98/2.27  #Tautology    : 1432
% 5.98/2.27  #SimpNegUnit  : 3
% 5.98/2.27  #BackRed      : 5
% 5.98/2.27  
% 5.98/2.27  #Partial instantiations: 0
% 5.98/2.27  #Strategies tried      : 1
% 5.98/2.27  
% 5.98/2.27  Timing (in seconds)
% 5.98/2.27  ----------------------
% 5.98/2.27  Preprocessing        : 0.34
% 5.98/2.27  Parsing              : 0.18
% 5.98/2.27  CNF conversion       : 0.02
% 5.98/2.27  Main loop            : 1.15
% 5.98/2.27  Inferencing          : 0.35
% 5.98/2.27  Reduction            : 0.57
% 5.98/2.27  Demodulation         : 0.48
% 5.98/2.27  BG Simplification    : 0.03
% 5.98/2.27  Subsumption          : 0.14
% 5.98/2.27  Abstraction          : 0.06
% 5.98/2.27  MUC search           : 0.00
% 5.98/2.27  Cooper               : 0.00
% 5.98/2.27  Total                : 1.54
% 5.98/2.27  Index Insertion      : 0.00
% 5.98/2.28  Index Deletion       : 0.00
% 5.98/2.28  Index Matching       : 0.00
% 5.98/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:24 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 311 expanded)
%              Number of leaves         :   44 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  203 ( 507 expanded)
%              Number of equality atoms :   91 ( 202 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6024,plain,(
    ! [A_271,B_272,C_273] :
      ( k7_subset_1(A_271,B_272,C_273) = k4_xboole_0(B_272,C_273)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(A_271)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6030,plain,(
    ! [C_273] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_273) = k4_xboole_0('#skF_2',C_273) ),
    inference(resolution,[status(thm)],[c_42,c_6024])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_128,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_257,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2035,plain,(
    ! [A_150,B_151] :
      ( k4_subset_1(u1_struct_0(A_150),B_151,k2_tops_1(A_150,B_151)) = k2_pre_topc(A_150,B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2040,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2035])).

tff(c_2044,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2040])).

tff(c_814,plain,(
    ! [A_96,B_97,C_98] :
      ( k7_subset_1(A_96,B_97,C_98) = k4_xboole_0(B_97,C_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_988,plain,(
    ! [C_105] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_105) = k4_xboole_0('#skF_2',C_105) ),
    inference(resolution,[status(thm)],[c_42,c_814])).

tff(c_994,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_128])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_473,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_497,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k4_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_473])).

tff(c_501,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_497])).

tff(c_304,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_322,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_304])).

tff(c_325,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_322])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_494,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_473])).

tff(c_500,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_494])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_821,plain,(
    ! [A_99,B_100] : k3_xboole_0(k4_xboole_0(A_99,B_100),A_99) = k4_xboole_0(A_99,B_100) ),
    inference(resolution,[status(thm)],[c_12,c_139])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_827,plain,(
    ! [A_99,B_100] : k5_xboole_0(k4_xboole_0(A_99,B_100),k4_xboole_0(A_99,B_100)) = k4_xboole_0(k4_xboole_0(A_99,B_100),A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_4])).

tff(c_886,plain,(
    ! [A_101,B_102] : k4_xboole_0(k4_xboole_0(A_101,B_102),A_101) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_827])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_897,plain,(
    ! [A_101,B_102] : k2_xboole_0(A_101,k4_xboole_0(A_101,B_102)) = k5_xboole_0(A_101,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_18])).

tff(c_935,plain,(
    ! [A_101,B_102] : k2_xboole_0(A_101,k4_xboole_0(A_101,B_102)) = A_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_897])).

tff(c_1264,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_935])).

tff(c_152,plain,(
    ! [A_11,B_12] : k3_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k4_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_12,c_139])).

tff(c_20,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_157,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_187,plain,(
    ! [A_62,B_63] : k1_setfam_1(k2_tarski(A_62,B_63)) = k3_xboole_0(B_63,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_157])).

tff(c_28,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_193,plain,(
    ! [B_63,A_62] : k3_xboole_0(B_63,A_62) = k3_xboole_0(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_28])).

tff(c_129,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_133,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_129])).

tff(c_149,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_133,c_139])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_313,plain,(
    ! [A_67,B_68] : r1_tarski(k3_xboole_0(A_67,B_68),A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_12])).

tff(c_624,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_tarski(A_87,C_88)
      | ~ r1_tarski(B_89,C_88)
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1353,plain,(
    ! [A_119,A_120,B_121] :
      ( r1_tarski(A_119,A_120)
      | ~ r1_tarski(A_119,k4_xboole_0(A_120,B_121)) ) ),
    inference(resolution,[status(thm)],[c_12,c_624])).

tff(c_1411,plain,(
    ! [A_122,B_123,B_124] : r1_tarski(k3_xboole_0(k4_xboole_0(A_122,B_123),B_124),A_122) ),
    inference(resolution,[status(thm)],[c_313,c_1353])).

tff(c_1657,plain,(
    ! [A_132,B_133,B_134] : r1_tarski(k3_xboole_0(k3_xboole_0(A_132,B_133),B_134),A_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1411])).

tff(c_1913,plain,(
    ! [B_145,A_146,B_147] : r1_tarski(k3_xboole_0(k3_xboole_0(B_145,A_146),B_147),A_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_1657])).

tff(c_1975,plain,(
    ! [B_148] : r1_tarski(k3_xboole_0('#skF_2',B_148),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_1913])).

tff(c_2003,plain,(
    ! [B_149] : r1_tarski(k3_xboole_0(B_149,'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_1975])).

tff(c_2045,plain,(
    ! [B_152] : r1_tarski(k4_xboole_0('#skF_2',B_152),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2003])).

tff(c_2052,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_2045])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1326,plain,(
    ! [A_116,B_117,C_118] :
      ( k4_subset_1(A_116,B_117,C_118) = k2_xboole_0(B_117,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(A_116))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4558,plain,(
    ! [B_200,B_201,A_202] :
      ( k4_subset_1(B_200,B_201,A_202) = k2_xboole_0(B_201,A_202)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(B_200))
      | ~ r1_tarski(A_202,B_200) ) ),
    inference(resolution,[status(thm)],[c_32,c_1326])).

tff(c_4960,plain,(
    ! [A_209] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_209) = k2_xboole_0('#skF_2',A_209)
      | ~ r1_tarski(A_209,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_4558])).

tff(c_4971,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2052,c_4960])).

tff(c_5038,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_1264,c_4971])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1194,plain,(
    ! [A_112,B_113] :
      ( v4_pre_topc(k2_pre_topc(A_112,B_113),A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1199,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1194])).

tff(c_1203,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1199])).

tff(c_5063,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5038,c_1203])).

tff(c_5065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_5063])).

tff(c_5066,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_5066])).

tff(c_5340,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5424,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5340,c_48])).

tff(c_6198,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6030,c_5424])).

tff(c_5651,plain,(
    ! [A_252,B_253] : k5_xboole_0(A_252,k3_xboole_0(A_252,B_253)) = k4_xboole_0(A_252,B_253) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5675,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k4_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_5651])).

tff(c_5679,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5675])).

tff(c_5518,plain,(
    ! [A_242,B_243] : k4_xboole_0(A_242,k4_xboole_0(A_242,B_243)) = k3_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5536,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_5518])).

tff(c_5539,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5536])).

tff(c_5672,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5651])).

tff(c_5678,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5539,c_5672])).

tff(c_6676,plain,(
    ! [A_300,B_301] :
      ( r1_tarski(k2_tops_1(A_300,B_301),B_301)
      | ~ v4_pre_topc(B_301,A_300)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ l1_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6681,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_6676])).

tff(c_6685,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5340,c_6681])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6692,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6685,c_8])).

tff(c_7604,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6692,c_4])).

tff(c_7634,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_7604])).

tff(c_7664,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7634,c_18])).

tff(c_7680,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5679,c_7664])).

tff(c_7274,plain,(
    ! [A_328,B_329] :
      ( k4_subset_1(u1_struct_0(A_328),B_329,k2_tops_1(A_328,B_329)) = k2_pre_topc(A_328,B_329)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7279,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_7274])).

tff(c_7283,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7279])).

tff(c_5366,plain,(
    ! [A_233,B_234] : k1_setfam_1(k2_tarski(A_233,B_234)) = k3_xboole_0(A_233,B_234) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5400,plain,(
    ! [B_237,A_238] : k1_setfam_1(k2_tarski(B_237,A_238)) = k3_xboole_0(A_238,B_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5366])).

tff(c_5406,plain,(
    ! [B_237,A_238] : k3_xboole_0(B_237,A_238) = k3_xboole_0(A_238,B_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_5400,c_28])).

tff(c_5342,plain,(
    ! [A_227,B_228] :
      ( r1_tarski(A_227,B_228)
      | ~ m1_subset_1(A_227,k1_zfmisc_1(B_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5346,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_5342])).

tff(c_5352,plain,(
    ! [A_231,B_232] :
      ( k3_xboole_0(A_231,B_232) = A_231
      | ~ r1_tarski(A_231,B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5362,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5346,c_5352])).

tff(c_5527,plain,(
    ! [A_242,B_243] : r1_tarski(k3_xboole_0(A_242,B_243),A_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_5518,c_12])).

tff(c_5834,plain,(
    ! [A_262,C_263,B_264] :
      ( r1_tarski(A_262,C_263)
      | ~ r1_tarski(B_264,C_263)
      | ~ r1_tarski(A_262,B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6487,plain,(
    ! [A_291,A_292,B_293] :
      ( r1_tarski(A_291,A_292)
      | ~ r1_tarski(A_291,k4_xboole_0(A_292,B_293)) ) ),
    inference(resolution,[status(thm)],[c_12,c_5834])).

tff(c_6539,plain,(
    ! [A_294,B_295,B_296] : r1_tarski(k3_xboole_0(k4_xboole_0(A_294,B_295),B_296),A_294) ),
    inference(resolution,[status(thm)],[c_5527,c_6487])).

tff(c_6766,plain,(
    ! [A_305,B_306,B_307] : r1_tarski(k3_xboole_0(k3_xboole_0(A_305,B_306),B_307),A_305) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6539])).

tff(c_6994,plain,(
    ! [A_314,B_315,B_316] : r1_tarski(k3_xboole_0(k3_xboole_0(A_314,B_315),B_316),B_315) ),
    inference(superposition,[status(thm),theory(equality)],[c_5406,c_6766])).

tff(c_7068,plain,(
    ! [B_320] : r1_tarski(k3_xboole_0('#skF_2',B_320),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5362,c_6994])).

tff(c_7077,plain,(
    ! [B_237] : r1_tarski(k3_xboole_0(B_237,'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5406,c_7068])).

tff(c_7578,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6692,c_7077])).

tff(c_7061,plain,(
    ! [A_317,B_318,C_319] :
      ( k4_subset_1(A_317,B_318,C_319) = k2_xboole_0(B_318,C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(A_317))
      | ~ m1_subset_1(B_318,k1_zfmisc_1(A_317)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10750,plain,(
    ! [B_388,B_389,A_390] :
      ( k4_subset_1(B_388,B_389,A_390) = k2_xboole_0(B_389,A_390)
      | ~ m1_subset_1(B_389,k1_zfmisc_1(B_388))
      | ~ r1_tarski(A_390,B_388) ) ),
    inference(resolution,[status(thm)],[c_32,c_7061])).

tff(c_10966,plain,(
    ! [A_394] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_394) = k2_xboole_0('#skF_2',A_394)
      | ~ r1_tarski(A_394,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_10750])).

tff(c_10976,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7578,c_10966])).

tff(c_11051,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_7283,c_10976])).

tff(c_36,plain,(
    ! [A_34,B_36] :
      ( k7_subset_1(u1_struct_0(A_34),k2_pre_topc(A_34,B_36),k1_tops_1(A_34,B_36)) = k2_tops_1(A_34,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11086,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11051,c_36])).

tff(c_11092,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6030,c_11086])).

tff(c_11094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6198,c_11092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:37:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.77/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.43  
% 6.77/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.43  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.77/2.43  
% 6.77/2.43  %Foreground sorts:
% 6.77/2.43  
% 6.77/2.43  
% 6.77/2.43  %Background operators:
% 6.77/2.43  
% 6.77/2.43  
% 6.77/2.43  %Foreground operators:
% 6.77/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.77/2.43  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.77/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.77/2.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.77/2.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.77/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.77/2.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.77/2.43  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.77/2.43  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.77/2.43  tff('#skF_2', type, '#skF_2': $i).
% 6.77/2.43  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.77/2.43  tff('#skF_1', type, '#skF_1': $i).
% 6.77/2.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.77/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.77/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.77/2.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.77/2.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.77/2.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.77/2.43  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.77/2.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.77/2.43  
% 6.77/2.45  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 6.77/2.45  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.77/2.45  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 6.77/2.45  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.77/2.45  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.77/2.45  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.77/2.45  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.77/2.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.77/2.45  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.77/2.45  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.77/2.45  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.77/2.45  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.77/2.45  tff(f_65, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.77/2.45  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.77/2.45  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.77/2.45  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.77/2.45  tff(f_77, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 6.77/2.45  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 6.77/2.45  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 6.77/2.45  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.77/2.45  tff(c_6024, plain, (![A_271, B_272, C_273]: (k7_subset_1(A_271, B_272, C_273)=k4_xboole_0(B_272, C_273) | ~m1_subset_1(B_272, k1_zfmisc_1(A_271)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.45  tff(c_6030, plain, (![C_273]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_273)=k4_xboole_0('#skF_2', C_273))), inference(resolution, [status(thm)], [c_42, c_6024])).
% 6.77/2.45  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.77/2.45  tff(c_128, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 6.77/2.45  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.77/2.45  tff(c_257, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 6.77/2.45  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.77/2.45  tff(c_2035, plain, (![A_150, B_151]: (k4_subset_1(u1_struct_0(A_150), B_151, k2_tops_1(A_150, B_151))=k2_pre_topc(A_150, B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.77/2.45  tff(c_2040, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2035])).
% 6.77/2.45  tff(c_2044, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2040])).
% 6.77/2.45  tff(c_814, plain, (![A_96, B_97, C_98]: (k7_subset_1(A_96, B_97, C_98)=k4_xboole_0(B_97, C_98) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.45  tff(c_988, plain, (![C_105]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_105)=k4_xboole_0('#skF_2', C_105))), inference(resolution, [status(thm)], [c_42, c_814])).
% 6.77/2.45  tff(c_994, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_988, c_128])).
% 6.77/2.45  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.77/2.45  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.45  tff(c_473, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.77/2.45  tff(c_497, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k4_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_473])).
% 6.77/2.45  tff(c_501, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_497])).
% 6.77/2.45  tff(c_304, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.77/2.45  tff(c_322, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_304])).
% 6.77/2.45  tff(c_325, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_322])).
% 6.77/2.45  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.77/2.45  tff(c_494, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_473])).
% 6.77/2.45  tff(c_500, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_325, c_494])).
% 6.77/2.45  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.77/2.45  tff(c_139, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.77/2.45  tff(c_821, plain, (![A_99, B_100]: (k3_xboole_0(k4_xboole_0(A_99, B_100), A_99)=k4_xboole_0(A_99, B_100))), inference(resolution, [status(thm)], [c_12, c_139])).
% 6.77/2.45  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.77/2.45  tff(c_827, plain, (![A_99, B_100]: (k5_xboole_0(k4_xboole_0(A_99, B_100), k4_xboole_0(A_99, B_100))=k4_xboole_0(k4_xboole_0(A_99, B_100), A_99))), inference(superposition, [status(thm), theory('equality')], [c_821, c_4])).
% 6.77/2.45  tff(c_886, plain, (![A_101, B_102]: (k4_xboole_0(k4_xboole_0(A_101, B_102), A_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_500, c_827])).
% 6.77/2.45  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.77/2.45  tff(c_897, plain, (![A_101, B_102]: (k2_xboole_0(A_101, k4_xboole_0(A_101, B_102))=k5_xboole_0(A_101, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_886, c_18])).
% 6.77/2.45  tff(c_935, plain, (![A_101, B_102]: (k2_xboole_0(A_101, k4_xboole_0(A_101, B_102))=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_501, c_897])).
% 6.77/2.45  tff(c_1264, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_994, c_935])).
% 6.77/2.45  tff(c_152, plain, (![A_11, B_12]: (k3_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k4_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_12, c_139])).
% 6.77/2.45  tff(c_20, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.45  tff(c_157, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.77/2.45  tff(c_187, plain, (![A_62, B_63]: (k1_setfam_1(k2_tarski(A_62, B_63))=k3_xboole_0(B_63, A_62))), inference(superposition, [status(thm), theory('equality')], [c_20, c_157])).
% 6.77/2.45  tff(c_28, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.77/2.45  tff(c_193, plain, (![B_63, A_62]: (k3_xboole_0(B_63, A_62)=k3_xboole_0(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_187, c_28])).
% 6.77/2.45  tff(c_129, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.77/2.45  tff(c_133, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_129])).
% 6.77/2.45  tff(c_149, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_133, c_139])).
% 6.77/2.45  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.77/2.45  tff(c_313, plain, (![A_67, B_68]: (r1_tarski(k3_xboole_0(A_67, B_68), A_67))), inference(superposition, [status(thm), theory('equality')], [c_304, c_12])).
% 6.77/2.45  tff(c_624, plain, (![A_87, C_88, B_89]: (r1_tarski(A_87, C_88) | ~r1_tarski(B_89, C_88) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.77/2.45  tff(c_1353, plain, (![A_119, A_120, B_121]: (r1_tarski(A_119, A_120) | ~r1_tarski(A_119, k4_xboole_0(A_120, B_121)))), inference(resolution, [status(thm)], [c_12, c_624])).
% 6.77/2.45  tff(c_1411, plain, (![A_122, B_123, B_124]: (r1_tarski(k3_xboole_0(k4_xboole_0(A_122, B_123), B_124), A_122))), inference(resolution, [status(thm)], [c_313, c_1353])).
% 6.77/2.45  tff(c_1657, plain, (![A_132, B_133, B_134]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_132, B_133), B_134), A_132))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1411])).
% 6.77/2.45  tff(c_1913, plain, (![B_145, A_146, B_147]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_145, A_146), B_147), A_146))), inference(superposition, [status(thm), theory('equality')], [c_193, c_1657])).
% 6.77/2.45  tff(c_1975, plain, (![B_148]: (r1_tarski(k3_xboole_0('#skF_2', B_148), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_149, c_1913])).
% 6.77/2.45  tff(c_2003, plain, (![B_149]: (r1_tarski(k3_xboole_0(B_149, '#skF_2'), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_193, c_1975])).
% 6.77/2.45  tff(c_2045, plain, (![B_152]: (r1_tarski(k4_xboole_0('#skF_2', B_152), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_152, c_2003])).
% 6.77/2.45  tff(c_2052, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_994, c_2045])).
% 6.77/2.45  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.77/2.45  tff(c_1326, plain, (![A_116, B_117, C_118]: (k4_subset_1(A_116, B_117, C_118)=k2_xboole_0(B_117, C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(A_116)) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.45  tff(c_4558, plain, (![B_200, B_201, A_202]: (k4_subset_1(B_200, B_201, A_202)=k2_xboole_0(B_201, A_202) | ~m1_subset_1(B_201, k1_zfmisc_1(B_200)) | ~r1_tarski(A_202, B_200))), inference(resolution, [status(thm)], [c_32, c_1326])).
% 6.77/2.45  tff(c_4960, plain, (![A_209]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_209)=k2_xboole_0('#skF_2', A_209) | ~r1_tarski(A_209, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_4558])).
% 6.77/2.45  tff(c_4971, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2052, c_4960])).
% 6.77/2.45  tff(c_5038, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2044, c_1264, c_4971])).
% 6.77/2.45  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.77/2.45  tff(c_1194, plain, (![A_112, B_113]: (v4_pre_topc(k2_pre_topc(A_112, B_113), A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.77/2.45  tff(c_1199, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1194])).
% 6.77/2.45  tff(c_1203, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1199])).
% 6.77/2.45  tff(c_5063, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5038, c_1203])).
% 6.77/2.45  tff(c_5065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_5063])).
% 6.77/2.45  tff(c_5066, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 6.77/2.45  tff(c_5339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_5066])).
% 6.77/2.45  tff(c_5340, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 6.77/2.45  tff(c_5424, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5340, c_48])).
% 6.77/2.45  tff(c_6198, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6030, c_5424])).
% 6.77/2.45  tff(c_5651, plain, (![A_252, B_253]: (k5_xboole_0(A_252, k3_xboole_0(A_252, B_253))=k4_xboole_0(A_252, B_253))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.77/2.45  tff(c_5675, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k4_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_5651])).
% 6.77/2.45  tff(c_5679, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5675])).
% 6.77/2.45  tff(c_5518, plain, (![A_242, B_243]: (k4_xboole_0(A_242, k4_xboole_0(A_242, B_243))=k3_xboole_0(A_242, B_243))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.77/2.45  tff(c_5536, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_5518])).
% 6.77/2.45  tff(c_5539, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_5536])).
% 6.77/2.45  tff(c_5672, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5651])).
% 6.77/2.45  tff(c_5678, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5539, c_5672])).
% 6.77/2.45  tff(c_6676, plain, (![A_300, B_301]: (r1_tarski(k2_tops_1(A_300, B_301), B_301) | ~v4_pre_topc(B_301, A_300) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_300))) | ~l1_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.77/2.45  tff(c_6681, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_6676])).
% 6.77/2.45  tff(c_6685, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5340, c_6681])).
% 6.77/2.45  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.77/2.45  tff(c_6692, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6685, c_8])).
% 6.77/2.45  tff(c_7604, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6692, c_4])).
% 6.77/2.45  tff(c_7634, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5678, c_7604])).
% 6.77/2.45  tff(c_7664, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7634, c_18])).
% 6.77/2.45  tff(c_7680, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5679, c_7664])).
% 6.77/2.45  tff(c_7274, plain, (![A_328, B_329]: (k4_subset_1(u1_struct_0(A_328), B_329, k2_tops_1(A_328, B_329))=k2_pre_topc(A_328, B_329) | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.77/2.45  tff(c_7279, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_7274])).
% 6.77/2.45  tff(c_7283, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7279])).
% 6.77/2.45  tff(c_5366, plain, (![A_233, B_234]: (k1_setfam_1(k2_tarski(A_233, B_234))=k3_xboole_0(A_233, B_234))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.77/2.45  tff(c_5400, plain, (![B_237, A_238]: (k1_setfam_1(k2_tarski(B_237, A_238))=k3_xboole_0(A_238, B_237))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5366])).
% 6.77/2.45  tff(c_5406, plain, (![B_237, A_238]: (k3_xboole_0(B_237, A_238)=k3_xboole_0(A_238, B_237))), inference(superposition, [status(thm), theory('equality')], [c_5400, c_28])).
% 6.77/2.45  tff(c_5342, plain, (![A_227, B_228]: (r1_tarski(A_227, B_228) | ~m1_subset_1(A_227, k1_zfmisc_1(B_228)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.77/2.45  tff(c_5346, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_5342])).
% 6.77/2.45  tff(c_5352, plain, (![A_231, B_232]: (k3_xboole_0(A_231, B_232)=A_231 | ~r1_tarski(A_231, B_232))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.77/2.45  tff(c_5362, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_5346, c_5352])).
% 6.77/2.45  tff(c_5527, plain, (![A_242, B_243]: (r1_tarski(k3_xboole_0(A_242, B_243), A_242))), inference(superposition, [status(thm), theory('equality')], [c_5518, c_12])).
% 6.77/2.45  tff(c_5834, plain, (![A_262, C_263, B_264]: (r1_tarski(A_262, C_263) | ~r1_tarski(B_264, C_263) | ~r1_tarski(A_262, B_264))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.77/2.45  tff(c_6487, plain, (![A_291, A_292, B_293]: (r1_tarski(A_291, A_292) | ~r1_tarski(A_291, k4_xboole_0(A_292, B_293)))), inference(resolution, [status(thm)], [c_12, c_5834])).
% 6.77/2.45  tff(c_6539, plain, (![A_294, B_295, B_296]: (r1_tarski(k3_xboole_0(k4_xboole_0(A_294, B_295), B_296), A_294))), inference(resolution, [status(thm)], [c_5527, c_6487])).
% 6.77/2.45  tff(c_6766, plain, (![A_305, B_306, B_307]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_305, B_306), B_307), A_305))), inference(superposition, [status(thm), theory('equality')], [c_16, c_6539])).
% 6.77/2.45  tff(c_6994, plain, (![A_314, B_315, B_316]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_314, B_315), B_316), B_315))), inference(superposition, [status(thm), theory('equality')], [c_5406, c_6766])).
% 6.77/2.45  tff(c_7068, plain, (![B_320]: (r1_tarski(k3_xboole_0('#skF_2', B_320), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_5362, c_6994])).
% 6.77/2.45  tff(c_7077, plain, (![B_237]: (r1_tarski(k3_xboole_0(B_237, '#skF_2'), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_5406, c_7068])).
% 6.77/2.45  tff(c_7578, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6692, c_7077])).
% 6.77/2.45  tff(c_7061, plain, (![A_317, B_318, C_319]: (k4_subset_1(A_317, B_318, C_319)=k2_xboole_0(B_318, C_319) | ~m1_subset_1(C_319, k1_zfmisc_1(A_317)) | ~m1_subset_1(B_318, k1_zfmisc_1(A_317)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.45  tff(c_10750, plain, (![B_388, B_389, A_390]: (k4_subset_1(B_388, B_389, A_390)=k2_xboole_0(B_389, A_390) | ~m1_subset_1(B_389, k1_zfmisc_1(B_388)) | ~r1_tarski(A_390, B_388))), inference(resolution, [status(thm)], [c_32, c_7061])).
% 6.77/2.45  tff(c_10966, plain, (![A_394]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_394)=k2_xboole_0('#skF_2', A_394) | ~r1_tarski(A_394, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_10750])).
% 6.77/2.45  tff(c_10976, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_7578, c_10966])).
% 6.77/2.45  tff(c_11051, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_7283, c_10976])).
% 6.77/2.45  tff(c_36, plain, (![A_34, B_36]: (k7_subset_1(u1_struct_0(A_34), k2_pre_topc(A_34, B_36), k1_tops_1(A_34, B_36))=k2_tops_1(A_34, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.77/2.45  tff(c_11086, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11051, c_36])).
% 6.77/2.45  tff(c_11092, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6030, c_11086])).
% 6.77/2.45  tff(c_11094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6198, c_11092])).
% 6.77/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.45  
% 6.77/2.45  Inference rules
% 6.77/2.45  ----------------------
% 6.77/2.45  #Ref     : 0
% 6.77/2.45  #Sup     : 2653
% 6.77/2.45  #Fact    : 0
% 6.77/2.45  #Define  : 0
% 6.77/2.45  #Split   : 2
% 6.77/2.45  #Chain   : 0
% 6.77/2.45  #Close   : 0
% 6.77/2.45  
% 6.77/2.45  Ordering : KBO
% 6.77/2.45  
% 6.77/2.45  Simplification rules
% 6.77/2.45  ----------------------
% 6.77/2.45  #Subsume      : 101
% 6.77/2.45  #Demod        : 2349
% 6.77/2.45  #Tautology    : 1921
% 6.77/2.45  #SimpNegUnit  : 2
% 6.77/2.45  #BackRed      : 7
% 6.77/2.45  
% 6.77/2.45  #Partial instantiations: 0
% 6.77/2.45  #Strategies tried      : 1
% 6.77/2.45  
% 6.77/2.45  Timing (in seconds)
% 6.77/2.45  ----------------------
% 6.77/2.46  Preprocessing        : 0.34
% 6.77/2.46  Parsing              : 0.18
% 6.77/2.46  CNF conversion       : 0.02
% 6.77/2.46  Main loop            : 1.33
% 6.77/2.46  Inferencing          : 0.39
% 6.77/2.46  Reduction            : 0.60
% 6.77/2.46  Demodulation         : 0.50
% 6.77/2.46  BG Simplification    : 0.04
% 6.77/2.46  Subsumption          : 0.21
% 6.77/2.46  Abstraction          : 0.06
% 6.77/2.46  MUC search           : 0.00
% 6.77/2.46  Cooper               : 0.00
% 6.77/2.46  Total                : 1.72
% 6.77/2.46  Index Insertion      : 0.00
% 6.77/2.46  Index Deletion       : 0.00
% 6.77/2.46  Index Matching       : 0.00
% 6.77/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

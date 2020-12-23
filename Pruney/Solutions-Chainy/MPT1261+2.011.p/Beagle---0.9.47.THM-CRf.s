%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:13 EST 2020

% Result     : Theorem 9.90s
% Output     : CNFRefutation 10.15s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 340 expanded)
%              Number of leaves         :   47 ( 133 expanded)
%              Depth                    :   14
%              Number of atoms          :  236 ( 623 expanded)
%              Number of equality atoms :   88 ( 183 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_78,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10910,plain,(
    ! [A_447,B_448,C_449] :
      ( k7_subset_1(A_447,B_448,C_449) = k4_xboole_0(B_448,C_449)
      | ~ m1_subset_1(B_448,k1_zfmisc_1(A_447)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10924,plain,(
    ! [C_449] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_449) = k4_xboole_0('#skF_2',C_449) ),
    inference(resolution,[status(thm)],[c_50,c_10910])).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_120,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_1379,plain,(
    ! [A_145,B_146,C_147] :
      ( k7_subset_1(A_145,B_146,C_147) = k4_xboole_0(B_146,C_147)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1422,plain,(
    ! [C_152] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_152) = k4_xboole_0('#skF_2',C_152) ),
    inference(resolution,[status(thm)],[c_50,c_1379])).

tff(c_62,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_236,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_62])).

tff(c_1428,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_236])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_573,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_582,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = k3_subset_1(A_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_573])).

tff(c_586,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_582])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_277,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_295,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_277])).

tff(c_298,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_295])).

tff(c_18,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_151,plain,(
    ! [A_65,B_66] : k1_setfam_1(k2_tarski(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_166,plain,(
    ! [A_67,B_68] : k1_setfam_1(k2_tarski(A_67,B_68)) = k3_xboole_0(B_68,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_151])).

tff(c_34,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_189,plain,(
    ! [B_69,A_70] : k3_xboole_0(B_69,A_70) = k3_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_34])).

tff(c_205,plain,(
    ! [A_70] : k3_xboole_0(k1_xboole_0,A_70) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_12])).

tff(c_286,plain,(
    ! [A_70] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_277])).

tff(c_308,plain,(
    ! [A_70] : k4_xboole_0(k1_xboole_0,A_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_286])).

tff(c_1389,plain,(
    ! [A_30,C_147] : k7_subset_1(A_30,k1_xboole_0,C_147) = k4_xboole_0(k1_xboole_0,C_147) ),
    inference(resolution,[status(thm)],[c_32,c_1379])).

tff(c_1395,plain,(
    ! [A_30,C_147] : k7_subset_1(A_30,k1_xboole_0,C_147) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_1389])).

tff(c_38,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3065,plain,(
    ! [A_198,B_199,C_200] :
      ( k4_subset_1(A_198,k3_subset_1(A_198,B_199),C_200) = k3_subset_1(A_198,k7_subset_1(A_198,B_199,C_200))
      | ~ m1_subset_1(C_200,k1_zfmisc_1(A_198))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9120,plain,(
    ! [B_341,B_342,A_343] :
      ( k4_subset_1(B_341,k3_subset_1(B_341,B_342),A_343) = k3_subset_1(B_341,k7_subset_1(B_341,B_342,A_343))
      | ~ m1_subset_1(B_342,k1_zfmisc_1(B_341))
      | ~ r1_tarski(A_343,B_341) ) ),
    inference(resolution,[status(thm)],[c_38,c_3065])).

tff(c_9130,plain,(
    ! [A_30,A_343] :
      ( k4_subset_1(A_30,k3_subset_1(A_30,k1_xboole_0),A_343) = k3_subset_1(A_30,k7_subset_1(A_30,k1_xboole_0,A_343))
      | ~ r1_tarski(A_343,A_30) ) ),
    inference(resolution,[status(thm)],[c_32,c_9120])).

tff(c_9139,plain,(
    ! [A_344,A_345] :
      ( k4_subset_1(A_344,A_344,A_345) = A_344
      | ~ r1_tarski(A_345,A_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_1395,c_586,c_9130])).

tff(c_9302,plain,(
    ! [A_9,B_10] : k4_subset_1(A_9,A_9,k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(resolution,[status(thm)],[c_14,c_9139])).

tff(c_827,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(k3_subset_1(A_111,B_112),k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_836,plain,(
    ! [A_30] :
      ( m1_subset_1(A_30,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_827])).

tff(c_840,plain,(
    ! [A_30] : m1_subset_1(A_30,k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_836])).

tff(c_1616,plain,(
    ! [A_160,B_161,C_162] :
      ( k4_subset_1(A_160,B_161,C_162) = k2_xboole_0(B_161,C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(A_160))
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5458,plain,(
    ! [B_260,B_261,A_262] :
      ( k4_subset_1(B_260,B_261,A_262) = k2_xboole_0(B_261,A_262)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(B_260))
      | ~ r1_tarski(A_262,B_260) ) ),
    inference(resolution,[status(thm)],[c_38,c_1616])).

tff(c_5682,plain,(
    ! [A_266,A_267] :
      ( k4_subset_1(A_266,A_266,A_267) = k2_xboole_0(A_266,A_267)
      | ~ r1_tarski(A_267,A_266) ) ),
    inference(resolution,[status(thm)],[c_840,c_5458])).

tff(c_5818,plain,(
    ! [A_9,B_10] : k4_subset_1(A_9,A_9,k4_xboole_0(A_9,B_10)) = k2_xboole_0(A_9,k4_xboole_0(A_9,B_10)) ),
    inference(resolution,[status(thm)],[c_14,c_5682])).

tff(c_9872,plain,(
    ! [A_368,B_369] : k2_xboole_0(A_368,k4_xboole_0(A_368,B_369)) = A_368 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9302,c_5818])).

tff(c_9904,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_9872])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2154,plain,(
    ! [A_177,B_178] :
      ( k4_subset_1(u1_struct_0(A_177),B_178,k2_tops_1(A_177,B_178)) = k2_pre_topc(A_177,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2165,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2154])).

tff(c_2174,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2165])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1458,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_14])).

tff(c_137,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_148,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_423,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_tarski(A_83,C_84)
      | ~ r1_tarski(B_85,C_84)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_453,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_88,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_148,c_423])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2550,plain,(
    ! [A_190,A_191] :
      ( r1_tarski(A_190,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_190,A_191)
      | ~ r1_tarski(A_191,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_453,c_10])).

tff(c_2578,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1458,c_2550])).

tff(c_2642,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2578])).

tff(c_5820,plain,(
    ! [A_268] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_268) = k2_xboole_0('#skF_2',A_268)
      | ~ r1_tarski(A_268,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_50,c_5458])).

tff(c_5867,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2642,c_5820])).

tff(c_5970,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2174,c_5867])).

tff(c_9947,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9904,c_5970])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1560,plain,(
    ! [A_155,B_156] :
      ( v4_pre_topc(k2_pre_topc(A_155,B_156),A_155)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1571,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1560])).

tff(c_1580,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1571])).

tff(c_9984,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9947,c_1580])).

tff(c_9986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_9984])).

tff(c_9987,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_10963,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10924,c_9987])).

tff(c_9988,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_11474,plain,(
    ! [A_479,B_480] :
      ( r1_tarski(k2_tops_1(A_479,B_480),B_480)
      | ~ v4_pre_topc(B_480,A_479)
      | ~ m1_subset_1(B_480,k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ l1_pre_topc(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_11485,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_11474])).

tff(c_11494,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_9988,c_11485])).

tff(c_10678,plain,(
    ! [A_434,B_435] :
      ( k4_xboole_0(A_434,B_435) = k3_subset_1(A_434,B_435)
      | ~ m1_subset_1(B_435,k1_zfmisc_1(A_434)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10690,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = k3_subset_1(A_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_10678])).

tff(c_10695,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10690])).

tff(c_10006,plain,(
    ! [A_377,B_378] :
      ( r1_tarski(A_377,B_378)
      | ~ m1_subset_1(A_377,k1_zfmisc_1(B_378)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10018,plain,(
    ! [A_30] : r1_tarski(k1_xboole_0,A_30) ),
    inference(resolution,[status(thm)],[c_32,c_10006])).

tff(c_10035,plain,(
    ! [B_382,A_383] :
      ( B_382 = A_383
      | ~ r1_tarski(B_382,A_383)
      | ~ r1_tarski(A_383,B_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10051,plain,(
    ! [A_384] :
      ( k1_xboole_0 = A_384
      | ~ r1_tarski(A_384,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10018,c_10035])).

tff(c_10066,plain,(
    ! [B_10] : k4_xboole_0(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_10051])).

tff(c_10920,plain,(
    ! [A_30,C_449] : k7_subset_1(A_30,k1_xboole_0,C_449) = k4_xboole_0(k1_xboole_0,C_449) ),
    inference(resolution,[status(thm)],[c_32,c_10910])).

tff(c_10926,plain,(
    ! [A_30,C_449] : k7_subset_1(A_30,k1_xboole_0,C_449) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10066,c_10920])).

tff(c_12438,plain,(
    ! [A_505,B_506,C_507] :
      ( k4_subset_1(A_505,k3_subset_1(A_505,B_506),C_507) = k3_subset_1(A_505,k7_subset_1(A_505,B_506,C_507))
      | ~ m1_subset_1(C_507,k1_zfmisc_1(A_505))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(A_505)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18631,plain,(
    ! [B_656,B_657,A_658] :
      ( k4_subset_1(B_656,k3_subset_1(B_656,B_657),A_658) = k3_subset_1(B_656,k7_subset_1(B_656,B_657,A_658))
      | ~ m1_subset_1(B_657,k1_zfmisc_1(B_656))
      | ~ r1_tarski(A_658,B_656) ) ),
    inference(resolution,[status(thm)],[c_38,c_12438])).

tff(c_18641,plain,(
    ! [A_30,A_658] :
      ( k4_subset_1(A_30,k3_subset_1(A_30,k1_xboole_0),A_658) = k3_subset_1(A_30,k7_subset_1(A_30,k1_xboole_0,A_658))
      | ~ r1_tarski(A_658,A_30) ) ),
    inference(resolution,[status(thm)],[c_32,c_18631])).

tff(c_18650,plain,(
    ! [A_659,A_660] :
      ( k4_subset_1(A_659,A_659,A_660) = A_659
      | ~ r1_tarski(A_660,A_659) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10695,c_10926,c_10695,c_18641])).

tff(c_18797,plain,(
    k4_subset_1('#skF_2','#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_11494,c_18650])).

tff(c_11705,plain,(
    ! [A_488,B_489] :
      ( k4_subset_1(u1_struct_0(A_488),B_489,k2_tops_1(A_488,B_489)) = k2_pre_topc(A_488,B_489)
      | ~ m1_subset_1(B_489,k1_zfmisc_1(u1_struct_0(A_488)))
      | ~ l1_pre_topc(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_11716,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_11705])).

tff(c_11725,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_11716])).

tff(c_10017,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_10006])).

tff(c_10287,plain,(
    ! [A_398,C_399,B_400] :
      ( r1_tarski(A_398,C_399)
      | ~ r1_tarski(B_400,C_399)
      | ~ r1_tarski(A_398,B_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10317,plain,(
    ! [A_403] :
      ( r1_tarski(A_403,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_403,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10017,c_10287])).

tff(c_10322,plain,(
    ! [A_5,A_403] :
      ( r1_tarski(A_5,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_5,A_403)
      | ~ r1_tarski(A_403,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10317,c_10])).

tff(c_11500,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_11494,c_10322])).

tff(c_11508,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11500])).

tff(c_11420,plain,(
    ! [A_475,B_476,C_477] :
      ( k4_subset_1(A_475,B_476,C_477) = k2_xboole_0(B_476,C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(A_475))
      | ~ m1_subset_1(B_476,k1_zfmisc_1(A_475)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_15800,plain,(
    ! [B_586,B_587,A_588] :
      ( k4_subset_1(B_586,B_587,A_588) = k2_xboole_0(B_587,A_588)
      | ~ m1_subset_1(B_587,k1_zfmisc_1(B_586))
      | ~ r1_tarski(A_588,B_586) ) ),
    inference(resolution,[status(thm)],[c_38,c_11420])).

tff(c_16157,plain,(
    ! [A_593] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_593) = k2_xboole_0('#skF_2',A_593)
      | ~ r1_tarski(A_593,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_50,c_15800])).

tff(c_16233,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_11508,c_16157])).

tff(c_16322,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11725,c_16233])).

tff(c_10697,plain,(
    ! [A_436] : k3_subset_1(A_436,k1_xboole_0) = A_436 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10690])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10710,plain,(
    ! [A_436] :
      ( m1_subset_1(A_436,k1_zfmisc_1(A_436))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_436)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10697,c_24])).

tff(c_10720,plain,(
    ! [A_436] : m1_subset_1(A_436,k1_zfmisc_1(A_436)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10710])).

tff(c_16008,plain,(
    ! [A_591,A_592] :
      ( k4_subset_1(A_591,A_591,A_592) = k2_xboole_0(A_591,A_592)
      | ~ r1_tarski(A_592,A_591) ) ),
    inference(resolution,[status(thm)],[c_10720,c_15800])).

tff(c_16131,plain,(
    k4_subset_1('#skF_2','#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_11494,c_16008])).

tff(c_16647,plain,(
    k4_subset_1('#skF_2','#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16322,c_16131])).

tff(c_19033,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18797,c_16647])).

tff(c_44,plain,(
    ! [A_40,B_42] :
      ( k7_subset_1(u1_struct_0(A_40),k2_pre_topc(A_40,B_42),k1_tops_1(A_40,B_42)) = k2_tops_1(A_40,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_19048,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19033,c_44])).

tff(c_19054,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_10924,c_19048])).

tff(c_19056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10963,c_19054])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.90/3.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.90/3.74  
% 9.90/3.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.90/3.74  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.90/3.74  
% 9.90/3.74  %Foreground sorts:
% 9.90/3.74  
% 9.90/3.74  
% 9.90/3.74  %Background operators:
% 9.90/3.74  
% 9.90/3.74  
% 9.90/3.74  %Foreground operators:
% 9.90/3.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.90/3.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.90/3.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.90/3.74  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.90/3.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.90/3.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.90/3.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.90/3.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.90/3.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.90/3.74  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.90/3.74  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.90/3.74  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.90/3.74  tff('#skF_2', type, '#skF_2': $i).
% 9.90/3.74  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.90/3.74  tff('#skF_1', type, '#skF_1': $i).
% 9.90/3.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.90/3.74  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.90/3.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.90/3.74  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.90/3.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.90/3.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.90/3.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.90/3.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.90/3.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.90/3.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.90/3.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.90/3.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.90/3.74  
% 10.15/3.77  tff(f_131, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 10.15/3.77  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.15/3.77  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.15/3.77  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.15/3.77  tff(f_76, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.15/3.77  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.15/3.77  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.15/3.77  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.15/3.77  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.15/3.77  tff(f_78, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.15/3.77  tff(f_82, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.15/3.77  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 10.15/3.77  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.15/3.77  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.15/3.77  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.15/3.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.15/3.77  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.15/3.77  tff(f_96, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 10.15/3.77  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 10.15/3.77  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 10.15/3.77  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.15/3.77  tff(c_10910, plain, (![A_447, B_448, C_449]: (k7_subset_1(A_447, B_448, C_449)=k4_xboole_0(B_448, C_449) | ~m1_subset_1(B_448, k1_zfmisc_1(A_447)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.15/3.77  tff(c_10924, plain, (![C_449]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_449)=k4_xboole_0('#skF_2', C_449))), inference(resolution, [status(thm)], [c_50, c_10910])).
% 10.15/3.77  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.15/3.77  tff(c_120, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 10.15/3.77  tff(c_1379, plain, (![A_145, B_146, C_147]: (k7_subset_1(A_145, B_146, C_147)=k4_xboole_0(B_146, C_147) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.15/3.77  tff(c_1422, plain, (![C_152]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_152)=k4_xboole_0('#skF_2', C_152))), inference(resolution, [status(thm)], [c_50, c_1379])).
% 10.15/3.77  tff(c_62, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.15/3.77  tff(c_236, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_120, c_62])).
% 10.15/3.77  tff(c_1428, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1422, c_236])).
% 10.15/3.77  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.15/3.77  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.15/3.77  tff(c_32, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.15/3.77  tff(c_573, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.15/3.77  tff(c_582, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=k3_subset_1(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_573])).
% 10.15/3.77  tff(c_586, plain, (![A_30]: (k3_subset_1(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_582])).
% 10.15/3.77  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.15/3.77  tff(c_277, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.15/3.77  tff(c_295, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_277])).
% 10.15/3.77  tff(c_298, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_295])).
% 10.15/3.77  tff(c_18, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.15/3.77  tff(c_151, plain, (![A_65, B_66]: (k1_setfam_1(k2_tarski(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.15/3.77  tff(c_166, plain, (![A_67, B_68]: (k1_setfam_1(k2_tarski(A_67, B_68))=k3_xboole_0(B_68, A_67))), inference(superposition, [status(thm), theory('equality')], [c_18, c_151])).
% 10.15/3.77  tff(c_34, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.15/3.77  tff(c_189, plain, (![B_69, A_70]: (k3_xboole_0(B_69, A_70)=k3_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_166, c_34])).
% 10.15/3.77  tff(c_205, plain, (![A_70]: (k3_xboole_0(k1_xboole_0, A_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_189, c_12])).
% 10.15/3.77  tff(c_286, plain, (![A_70]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_70))), inference(superposition, [status(thm), theory('equality')], [c_205, c_277])).
% 10.15/3.77  tff(c_308, plain, (![A_70]: (k4_xboole_0(k1_xboole_0, A_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_298, c_286])).
% 10.15/3.77  tff(c_1389, plain, (![A_30, C_147]: (k7_subset_1(A_30, k1_xboole_0, C_147)=k4_xboole_0(k1_xboole_0, C_147))), inference(resolution, [status(thm)], [c_32, c_1379])).
% 10.15/3.77  tff(c_1395, plain, (![A_30, C_147]: (k7_subset_1(A_30, k1_xboole_0, C_147)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_308, c_1389])).
% 10.15/3.77  tff(c_38, plain, (![A_33, B_34]: (m1_subset_1(A_33, k1_zfmisc_1(B_34)) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.15/3.77  tff(c_3065, plain, (![A_198, B_199, C_200]: (k4_subset_1(A_198, k3_subset_1(A_198, B_199), C_200)=k3_subset_1(A_198, k7_subset_1(A_198, B_199, C_200)) | ~m1_subset_1(C_200, k1_zfmisc_1(A_198)) | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.15/3.77  tff(c_9120, plain, (![B_341, B_342, A_343]: (k4_subset_1(B_341, k3_subset_1(B_341, B_342), A_343)=k3_subset_1(B_341, k7_subset_1(B_341, B_342, A_343)) | ~m1_subset_1(B_342, k1_zfmisc_1(B_341)) | ~r1_tarski(A_343, B_341))), inference(resolution, [status(thm)], [c_38, c_3065])).
% 10.15/3.77  tff(c_9130, plain, (![A_30, A_343]: (k4_subset_1(A_30, k3_subset_1(A_30, k1_xboole_0), A_343)=k3_subset_1(A_30, k7_subset_1(A_30, k1_xboole_0, A_343)) | ~r1_tarski(A_343, A_30))), inference(resolution, [status(thm)], [c_32, c_9120])).
% 10.15/3.77  tff(c_9139, plain, (![A_344, A_345]: (k4_subset_1(A_344, A_344, A_345)=A_344 | ~r1_tarski(A_345, A_344))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_1395, c_586, c_9130])).
% 10.15/3.77  tff(c_9302, plain, (![A_9, B_10]: (k4_subset_1(A_9, A_9, k4_xboole_0(A_9, B_10))=A_9)), inference(resolution, [status(thm)], [c_14, c_9139])).
% 10.15/3.77  tff(c_827, plain, (![A_111, B_112]: (m1_subset_1(k3_subset_1(A_111, B_112), k1_zfmisc_1(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.15/3.77  tff(c_836, plain, (![A_30]: (m1_subset_1(A_30, k1_zfmisc_1(A_30)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_586, c_827])).
% 10.15/3.77  tff(c_840, plain, (![A_30]: (m1_subset_1(A_30, k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_836])).
% 10.15/3.77  tff(c_1616, plain, (![A_160, B_161, C_162]: (k4_subset_1(A_160, B_161, C_162)=k2_xboole_0(B_161, C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.15/3.77  tff(c_5458, plain, (![B_260, B_261, A_262]: (k4_subset_1(B_260, B_261, A_262)=k2_xboole_0(B_261, A_262) | ~m1_subset_1(B_261, k1_zfmisc_1(B_260)) | ~r1_tarski(A_262, B_260))), inference(resolution, [status(thm)], [c_38, c_1616])).
% 10.15/3.77  tff(c_5682, plain, (![A_266, A_267]: (k4_subset_1(A_266, A_266, A_267)=k2_xboole_0(A_266, A_267) | ~r1_tarski(A_267, A_266))), inference(resolution, [status(thm)], [c_840, c_5458])).
% 10.15/3.77  tff(c_5818, plain, (![A_9, B_10]: (k4_subset_1(A_9, A_9, k4_xboole_0(A_9, B_10))=k2_xboole_0(A_9, k4_xboole_0(A_9, B_10)))), inference(resolution, [status(thm)], [c_14, c_5682])).
% 10.15/3.77  tff(c_9872, plain, (![A_368, B_369]: (k2_xboole_0(A_368, k4_xboole_0(A_368, B_369))=A_368)), inference(demodulation, [status(thm), theory('equality')], [c_9302, c_5818])).
% 10.15/3.77  tff(c_9904, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1428, c_9872])).
% 10.15/3.77  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.15/3.77  tff(c_2154, plain, (![A_177, B_178]: (k4_subset_1(u1_struct_0(A_177), B_178, k2_tops_1(A_177, B_178))=k2_pre_topc(A_177, B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.15/3.77  tff(c_2165, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2154])).
% 10.15/3.77  tff(c_2174, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2165])).
% 10.15/3.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.15/3.77  tff(c_1458, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1428, c_14])).
% 10.15/3.77  tff(c_137, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.15/3.77  tff(c_148, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_137])).
% 10.15/3.77  tff(c_423, plain, (![A_83, C_84, B_85]: (r1_tarski(A_83, C_84) | ~r1_tarski(B_85, C_84) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.15/3.77  tff(c_453, plain, (![A_88]: (r1_tarski(A_88, u1_struct_0('#skF_1')) | ~r1_tarski(A_88, '#skF_2'))), inference(resolution, [status(thm)], [c_148, c_423])).
% 10.15/3.77  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.15/3.77  tff(c_2550, plain, (![A_190, A_191]: (r1_tarski(A_190, u1_struct_0('#skF_1')) | ~r1_tarski(A_190, A_191) | ~r1_tarski(A_191, '#skF_2'))), inference(resolution, [status(thm)], [c_453, c_10])).
% 10.15/3.77  tff(c_2578, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1458, c_2550])).
% 10.15/3.77  tff(c_2642, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2578])).
% 10.15/3.77  tff(c_5820, plain, (![A_268]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_268)=k2_xboole_0('#skF_2', A_268) | ~r1_tarski(A_268, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_50, c_5458])).
% 10.15/3.77  tff(c_5867, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2642, c_5820])).
% 10.15/3.77  tff(c_5970, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2174, c_5867])).
% 10.15/3.77  tff(c_9947, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9904, c_5970])).
% 10.15/3.77  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.15/3.77  tff(c_1560, plain, (![A_155, B_156]: (v4_pre_topc(k2_pre_topc(A_155, B_156), A_155) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.15/3.77  tff(c_1571, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1560])).
% 10.15/3.77  tff(c_1580, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1571])).
% 10.15/3.77  tff(c_9984, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9947, c_1580])).
% 10.15/3.77  tff(c_9986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_9984])).
% 10.15/3.77  tff(c_9987, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 10.15/3.77  tff(c_10963, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10924, c_9987])).
% 10.15/3.77  tff(c_9988, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 10.15/3.77  tff(c_11474, plain, (![A_479, B_480]: (r1_tarski(k2_tops_1(A_479, B_480), B_480) | ~v4_pre_topc(B_480, A_479) | ~m1_subset_1(B_480, k1_zfmisc_1(u1_struct_0(A_479))) | ~l1_pre_topc(A_479))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.15/3.77  tff(c_11485, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_11474])).
% 10.15/3.77  tff(c_11494, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_9988, c_11485])).
% 10.15/3.77  tff(c_10678, plain, (![A_434, B_435]: (k4_xboole_0(A_434, B_435)=k3_subset_1(A_434, B_435) | ~m1_subset_1(B_435, k1_zfmisc_1(A_434)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.15/3.77  tff(c_10690, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=k3_subset_1(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_10678])).
% 10.15/3.77  tff(c_10695, plain, (![A_30]: (k3_subset_1(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10690])).
% 10.15/3.77  tff(c_10006, plain, (![A_377, B_378]: (r1_tarski(A_377, B_378) | ~m1_subset_1(A_377, k1_zfmisc_1(B_378)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.15/3.77  tff(c_10018, plain, (![A_30]: (r1_tarski(k1_xboole_0, A_30))), inference(resolution, [status(thm)], [c_32, c_10006])).
% 10.15/3.77  tff(c_10035, plain, (![B_382, A_383]: (B_382=A_383 | ~r1_tarski(B_382, A_383) | ~r1_tarski(A_383, B_382))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.15/3.77  tff(c_10051, plain, (![A_384]: (k1_xboole_0=A_384 | ~r1_tarski(A_384, k1_xboole_0))), inference(resolution, [status(thm)], [c_10018, c_10035])).
% 10.15/3.77  tff(c_10066, plain, (![B_10]: (k4_xboole_0(k1_xboole_0, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_10051])).
% 10.15/3.77  tff(c_10920, plain, (![A_30, C_449]: (k7_subset_1(A_30, k1_xboole_0, C_449)=k4_xboole_0(k1_xboole_0, C_449))), inference(resolution, [status(thm)], [c_32, c_10910])).
% 10.15/3.77  tff(c_10926, plain, (![A_30, C_449]: (k7_subset_1(A_30, k1_xboole_0, C_449)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10066, c_10920])).
% 10.15/3.77  tff(c_12438, plain, (![A_505, B_506, C_507]: (k4_subset_1(A_505, k3_subset_1(A_505, B_506), C_507)=k3_subset_1(A_505, k7_subset_1(A_505, B_506, C_507)) | ~m1_subset_1(C_507, k1_zfmisc_1(A_505)) | ~m1_subset_1(B_506, k1_zfmisc_1(A_505)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.15/3.77  tff(c_18631, plain, (![B_656, B_657, A_658]: (k4_subset_1(B_656, k3_subset_1(B_656, B_657), A_658)=k3_subset_1(B_656, k7_subset_1(B_656, B_657, A_658)) | ~m1_subset_1(B_657, k1_zfmisc_1(B_656)) | ~r1_tarski(A_658, B_656))), inference(resolution, [status(thm)], [c_38, c_12438])).
% 10.15/3.77  tff(c_18641, plain, (![A_30, A_658]: (k4_subset_1(A_30, k3_subset_1(A_30, k1_xboole_0), A_658)=k3_subset_1(A_30, k7_subset_1(A_30, k1_xboole_0, A_658)) | ~r1_tarski(A_658, A_30))), inference(resolution, [status(thm)], [c_32, c_18631])).
% 10.15/3.77  tff(c_18650, plain, (![A_659, A_660]: (k4_subset_1(A_659, A_659, A_660)=A_659 | ~r1_tarski(A_660, A_659))), inference(demodulation, [status(thm), theory('equality')], [c_10695, c_10926, c_10695, c_18641])).
% 10.15/3.77  tff(c_18797, plain, (k4_subset_1('#skF_2', '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_11494, c_18650])).
% 10.15/3.77  tff(c_11705, plain, (![A_488, B_489]: (k4_subset_1(u1_struct_0(A_488), B_489, k2_tops_1(A_488, B_489))=k2_pre_topc(A_488, B_489) | ~m1_subset_1(B_489, k1_zfmisc_1(u1_struct_0(A_488))) | ~l1_pre_topc(A_488))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.15/3.77  tff(c_11716, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_11705])).
% 10.15/3.77  tff(c_11725, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_11716])).
% 10.15/3.77  tff(c_10017, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_10006])).
% 10.15/3.77  tff(c_10287, plain, (![A_398, C_399, B_400]: (r1_tarski(A_398, C_399) | ~r1_tarski(B_400, C_399) | ~r1_tarski(A_398, B_400))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.15/3.77  tff(c_10317, plain, (![A_403]: (r1_tarski(A_403, u1_struct_0('#skF_1')) | ~r1_tarski(A_403, '#skF_2'))), inference(resolution, [status(thm)], [c_10017, c_10287])).
% 10.15/3.77  tff(c_10322, plain, (![A_5, A_403]: (r1_tarski(A_5, u1_struct_0('#skF_1')) | ~r1_tarski(A_5, A_403) | ~r1_tarski(A_403, '#skF_2'))), inference(resolution, [status(thm)], [c_10317, c_10])).
% 10.15/3.77  tff(c_11500, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_11494, c_10322])).
% 10.15/3.77  tff(c_11508, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11500])).
% 10.15/3.77  tff(c_11420, plain, (![A_475, B_476, C_477]: (k4_subset_1(A_475, B_476, C_477)=k2_xboole_0(B_476, C_477) | ~m1_subset_1(C_477, k1_zfmisc_1(A_475)) | ~m1_subset_1(B_476, k1_zfmisc_1(A_475)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.15/3.77  tff(c_15800, plain, (![B_586, B_587, A_588]: (k4_subset_1(B_586, B_587, A_588)=k2_xboole_0(B_587, A_588) | ~m1_subset_1(B_587, k1_zfmisc_1(B_586)) | ~r1_tarski(A_588, B_586))), inference(resolution, [status(thm)], [c_38, c_11420])).
% 10.15/3.77  tff(c_16157, plain, (![A_593]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_593)=k2_xboole_0('#skF_2', A_593) | ~r1_tarski(A_593, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_50, c_15800])).
% 10.15/3.77  tff(c_16233, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_11508, c_16157])).
% 10.15/3.77  tff(c_16322, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11725, c_16233])).
% 10.15/3.77  tff(c_10697, plain, (![A_436]: (k3_subset_1(A_436, k1_xboole_0)=A_436)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10690])).
% 10.15/3.77  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.15/3.77  tff(c_10710, plain, (![A_436]: (m1_subset_1(A_436, k1_zfmisc_1(A_436)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_436)))), inference(superposition, [status(thm), theory('equality')], [c_10697, c_24])).
% 10.15/3.77  tff(c_10720, plain, (![A_436]: (m1_subset_1(A_436, k1_zfmisc_1(A_436)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10710])).
% 10.15/3.77  tff(c_16008, plain, (![A_591, A_592]: (k4_subset_1(A_591, A_591, A_592)=k2_xboole_0(A_591, A_592) | ~r1_tarski(A_592, A_591))), inference(resolution, [status(thm)], [c_10720, c_15800])).
% 10.15/3.77  tff(c_16131, plain, (k4_subset_1('#skF_2', '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_11494, c_16008])).
% 10.15/3.77  tff(c_16647, plain, (k4_subset_1('#skF_2', '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16322, c_16131])).
% 10.15/3.77  tff(c_19033, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18797, c_16647])).
% 10.15/3.77  tff(c_44, plain, (![A_40, B_42]: (k7_subset_1(u1_struct_0(A_40), k2_pre_topc(A_40, B_42), k1_tops_1(A_40, B_42))=k2_tops_1(A_40, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.15/3.77  tff(c_19048, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_19033, c_44])).
% 10.15/3.77  tff(c_19054, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_10924, c_19048])).
% 10.15/3.77  tff(c_19056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10963, c_19054])).
% 10.15/3.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.15/3.77  
% 10.15/3.77  Inference rules
% 10.15/3.77  ----------------------
% 10.15/3.77  #Ref     : 0
% 10.15/3.77  #Sup     : 4413
% 10.15/3.77  #Fact    : 0
% 10.15/3.77  #Define  : 0
% 10.15/3.77  #Split   : 5
% 10.15/3.77  #Chain   : 0
% 10.15/3.77  #Close   : 0
% 10.15/3.77  
% 10.15/3.77  Ordering : KBO
% 10.15/3.77  
% 10.15/3.77  Simplification rules
% 10.15/3.77  ----------------------
% 10.15/3.77  #Subsume      : 307
% 10.15/3.77  #Demod        : 2259
% 10.15/3.77  #Tautology    : 1346
% 10.15/3.77  #SimpNegUnit  : 3
% 10.15/3.77  #BackRed      : 44
% 10.15/3.77  
% 10.15/3.77  #Partial instantiations: 0
% 10.15/3.77  #Strategies tried      : 1
% 10.15/3.77  
% 10.15/3.77  Timing (in seconds)
% 10.15/3.77  ----------------------
% 10.15/3.77  Preprocessing        : 0.36
% 10.15/3.77  Parsing              : 0.19
% 10.15/3.77  CNF conversion       : 0.02
% 10.15/3.77  Main loop            : 2.61
% 10.15/3.77  Inferencing          : 0.66
% 10.15/3.77  Reduction            : 1.09
% 10.15/3.77  Demodulation         : 0.85
% 10.15/3.77  BG Simplification    : 0.09
% 10.15/3.77  Subsumption          : 0.57
% 10.15/3.77  Abstraction          : 0.16
% 10.15/3.77  MUC search           : 0.00
% 10.15/3.77  Cooper               : 0.00
% 10.15/3.77  Total                : 3.02
% 10.15/3.77  Index Insertion      : 0.00
% 10.15/3.77  Index Deletion       : 0.00
% 10.15/3.77  Index Matching       : 0.00
% 10.15/3.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------

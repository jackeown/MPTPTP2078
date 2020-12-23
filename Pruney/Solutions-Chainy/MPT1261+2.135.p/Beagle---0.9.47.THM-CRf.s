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
% DateTime   : Thu Dec  3 10:21:30 EST 2020

% Result     : Theorem 5.79s
% Output     : CNFRefutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 339 expanded)
%              Number of leaves         :   42 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  193 ( 695 expanded)
%              Number of equality atoms :   89 ( 201 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
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

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4789,plain,(
    ! [A_233,B_234,C_235] :
      ( k7_subset_1(A_233,B_234,C_235) = k4_xboole_0(B_234,C_235)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(A_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4795,plain,(
    ! [C_235] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_235) = k4_xboole_0('#skF_2',C_235) ),
    inference(resolution,[status(thm)],[c_46,c_4789])).

tff(c_52,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_238,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1614,plain,(
    ! [B_124,A_125] :
      ( v4_pre_topc(B_124,A_125)
      | k2_pre_topc(A_125,B_124) != B_124
      | ~ v2_pre_topc(A_125)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1624,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1614])).

tff(c_1629,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_1624])).

tff(c_1630,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_1629])).

tff(c_697,plain,(
    ! [A_85,B_86,C_87] :
      ( k7_subset_1(A_85,B_86,C_87) = k4_xboole_0(B_86,C_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_805,plain,(
    ! [C_91] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_91) = k4_xboole_0('#skF_2',C_91) ),
    inference(resolution,[status(thm)],[c_46,c_697])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_114,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_811,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_114])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_120,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_146,plain,(
    ! [A_56] : k3_xboole_0(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_120])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_155,plain,(
    ! [A_56] : k3_xboole_0(A_56,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_2])).

tff(c_283,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_295,plain,(
    ! [A_56] : k5_xboole_0(A_56,k1_xboole_0) = k4_xboole_0(A_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_283])).

tff(c_310,plain,(
    ! [A_56] : k5_xboole_0(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_295])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_594,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k3_subset_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_664,plain,(
    ! [B_82,A_83] :
      ( k4_xboole_0(B_82,A_83) = k3_subset_1(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_32,c_594])).

tff(c_679,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = k3_subset_1(A_9,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_664])).

tff(c_687,plain,(
    ! [A_9] : k3_subset_1(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_679])).

tff(c_387,plain,(
    ! [A_69,B_70] :
      ( k3_subset_1(A_69,k3_subset_1(A_69,B_70)) = B_70
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1100,plain,(
    ! [B_99,A_100] :
      ( k3_subset_1(B_99,k3_subset_1(B_99,A_100)) = A_100
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(resolution,[status(thm)],[c_32,c_387])).

tff(c_1118,plain,(
    ! [A_9] :
      ( k3_subset_1(A_9,A_9) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_1100])).

tff(c_1133,plain,(
    ! [A_9] : k3_subset_1(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1118])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_685,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k3_subset_1(B_4,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_664])).

tff(c_135,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_120])).

tff(c_301,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_283])).

tff(c_705,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k3_subset_1(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_301])).

tff(c_1155,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_705])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_503,plain,(
    ! [A_74,B_75] : k3_xboole_0(k4_xboole_0(A_74,B_75),A_74) = k4_xboole_0(A_74,B_75) ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_512,plain,(
    ! [A_74,B_75] : k5_xboole_0(k4_xboole_0(A_74,B_75),k4_xboole_0(A_74,B_75)) = k4_xboole_0(k4_xboole_0(A_74,B_75),A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_10])).

tff(c_2294,plain,(
    ! [A_152,B_153] : k4_xboole_0(k4_xboole_0(A_152,B_153),A_152) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_512])).

tff(c_20,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2329,plain,(
    ! [A_152,B_153] : k2_xboole_0(A_152,k4_xboole_0(A_152,B_153)) = k5_xboole_0(A_152,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2294,c_20])).

tff(c_2457,plain,(
    ! [A_155,B_156] : k2_xboole_0(A_155,k4_xboole_0(A_155,B_156)) = A_155 ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_2329])).

tff(c_2487,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_2457])).

tff(c_1781,plain,(
    ! [A_129,B_130] :
      ( k4_subset_1(u1_struct_0(A_129),B_130,k2_tops_1(A_129,B_130)) = k2_pre_topc(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1788,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1781])).

tff(c_1793,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1788])).

tff(c_907,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1(k2_tops_1(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( k3_subset_1(A_17,k3_subset_1(A_17,B_18)) = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4043,plain,(
    ! [A_191,B_192] :
      ( k3_subset_1(u1_struct_0(A_191),k3_subset_1(u1_struct_0(A_191),k2_tops_1(A_191,B_192))) = k2_tops_1(A_191,B_192)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191) ) ),
    inference(resolution,[status(thm)],[c_907,c_24])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k3_subset_1(A_15,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3694,plain,(
    ! [A_187,B_188] :
      ( k4_xboole_0(u1_struct_0(A_187),k2_tops_1(A_187,B_188)) = k3_subset_1(u1_struct_0(A_187),k2_tops_1(A_187,B_188))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187) ) ),
    inference(resolution,[status(thm)],[c_907,c_22])).

tff(c_3701,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_3694])).

tff(c_3706,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3701])).

tff(c_1378,plain,(
    ! [A_117,B_118] : k4_xboole_0(A_117,k4_xboole_0(A_117,B_118)) = k3_subset_1(A_117,k4_xboole_0(A_117,B_118)) ),
    inference(resolution,[status(thm)],[c_16,c_664])).

tff(c_1403,plain,(
    ! [A_117,B_118] : r1_tarski(k3_subset_1(A_117,k4_xboole_0(A_117,B_118)),A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_1378,c_16])).

tff(c_3755,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3706,c_1403])).

tff(c_4049,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4043,c_3755])).

tff(c_4064,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_4049])).

tff(c_1342,plain,(
    ! [A_110,B_111,C_112] :
      ( k4_subset_1(A_110,B_111,C_112) = k2_xboole_0(B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2281,plain,(
    ! [B_149,B_150,A_151] :
      ( k4_subset_1(B_149,B_150,A_151) = k2_xboole_0(B_150,A_151)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(B_149))
      | ~ r1_tarski(A_151,B_149) ) ),
    inference(resolution,[status(thm)],[c_32,c_1342])).

tff(c_2290,plain,(
    ! [A_151] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_151) = k2_xboole_0('#skF_2',A_151)
      | ~ r1_tarski(A_151,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_46,c_2281])).

tff(c_4074,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4064,c_2290])).

tff(c_4095,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2487,c_1793,c_4074])).

tff(c_4097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1630,c_4095])).

tff(c_4098,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4098,c_114])).

tff(c_4208,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4333,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4208,c_52])).

tff(c_4897,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4795,c_4333])).

tff(c_5514,plain,(
    ! [A_261,B_262] :
      ( r1_tarski(k2_tops_1(A_261,B_262),B_262)
      | ~ v4_pre_topc(B_262,A_261)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5521,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_5514])).

tff(c_5526,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4208,c_5521])).

tff(c_4686,plain,(
    ! [A_226,B_227] :
      ( k4_xboole_0(A_226,B_227) = k3_subset_1(A_226,B_227)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(A_226)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4693,plain,(
    ! [B_26,A_25] :
      ( k4_xboole_0(B_26,A_25) = k3_subset_1(B_26,A_25)
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_4686])).

tff(c_5535,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_5526,c_4693])).

tff(c_5720,plain,(
    ! [A_271,B_272] :
      ( k7_subset_1(u1_struct_0(A_271),B_272,k2_tops_1(A_271,B_272)) = k1_tops_1(A_271,B_272)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5727,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_5720])).

tff(c_5732,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5535,c_4795,c_5727])).

tff(c_4479,plain,(
    ! [A_217,B_218] :
      ( k3_subset_1(A_217,k3_subset_1(A_217,B_218)) = B_218
      | ~ m1_subset_1(B_218,k1_zfmisc_1(A_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4484,plain,(
    ! [B_26,A_25] :
      ( k3_subset_1(B_26,k3_subset_1(B_26,A_25)) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_4479])).

tff(c_5757,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5732,c_4484])).

tff(c_5761,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5526,c_5757])).

tff(c_5753,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5732,c_5535])).

tff(c_4756,plain,(
    ! [B_230,A_231] :
      ( k4_xboole_0(B_230,A_231) = k3_subset_1(B_230,A_231)
      | ~ r1_tarski(A_231,B_230) ) ),
    inference(resolution,[status(thm)],[c_32,c_4686])).

tff(c_5904,plain,(
    ! [A_278,B_279] : k4_xboole_0(A_278,k4_xboole_0(A_278,B_279)) = k3_subset_1(A_278,k4_xboole_0(A_278,B_279)) ),
    inference(resolution,[status(thm)],[c_16,c_4756])).

tff(c_5941,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5753,c_5904])).

tff(c_5976,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5761,c_5753,c_5941])).

tff(c_5978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4897,c_5976])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.79/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.79/2.16  
% 5.79/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.79/2.16  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.79/2.16  
% 5.79/2.16  %Foreground sorts:
% 5.79/2.16  
% 5.79/2.16  
% 5.79/2.16  %Background operators:
% 5.79/2.16  
% 5.79/2.16  
% 5.79/2.16  %Foreground operators:
% 5.79/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.79/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.79/2.16  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.79/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.79/2.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.79/2.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.79/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.79/2.16  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.79/2.16  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.79/2.16  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.79/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.79/2.16  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.79/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.79/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.79/2.16  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.79/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.79/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.79/2.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.79/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.79/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.79/2.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.79/2.16  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.79/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.79/2.16  
% 5.79/2.18  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.79/2.18  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.79/2.18  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.79/2.18  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.79/2.18  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.79/2.18  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.79/2.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.79/2.18  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.79/2.18  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.79/2.18  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.79/2.18  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.79/2.18  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.79/2.18  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.79/2.18  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.79/2.18  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.79/2.18  tff(f_90, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.79/2.18  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.79/2.18  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.79/2.18  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.79/2.18  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.79/2.18  tff(c_4789, plain, (![A_233, B_234, C_235]: (k7_subset_1(A_233, B_234, C_235)=k4_xboole_0(B_234, C_235) | ~m1_subset_1(B_234, k1_zfmisc_1(A_233)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.79/2.18  tff(c_4795, plain, (![C_235]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_235)=k4_xboole_0('#skF_2', C_235))), inference(resolution, [status(thm)], [c_46, c_4789])).
% 5.79/2.18  tff(c_52, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.79/2.18  tff(c_238, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 5.79/2.18  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.79/2.18  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.79/2.18  tff(c_1614, plain, (![B_124, A_125]: (v4_pre_topc(B_124, A_125) | k2_pre_topc(A_125, B_124)!=B_124 | ~v2_pre_topc(A_125) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.79/2.18  tff(c_1624, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1614])).
% 5.79/2.18  tff(c_1629, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_1624])).
% 5.79/2.18  tff(c_1630, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_238, c_1629])).
% 5.79/2.18  tff(c_697, plain, (![A_85, B_86, C_87]: (k7_subset_1(A_85, B_86, C_87)=k4_xboole_0(B_86, C_87) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.79/2.18  tff(c_805, plain, (![C_91]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_91)=k4_xboole_0('#skF_2', C_91))), inference(resolution, [status(thm)], [c_46, c_697])).
% 5.79/2.18  tff(c_58, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.79/2.18  tff(c_114, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 5.79/2.18  tff(c_811, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_805, c_114])).
% 5.79/2.18  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.79/2.18  tff(c_14, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.79/2.18  tff(c_120, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.79/2.18  tff(c_146, plain, (![A_56]: (k3_xboole_0(k1_xboole_0, A_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_120])).
% 5.79/2.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.79/2.18  tff(c_155, plain, (![A_56]: (k3_xboole_0(A_56, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_146, c_2])).
% 5.79/2.18  tff(c_283, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.79/2.18  tff(c_295, plain, (![A_56]: (k5_xboole_0(A_56, k1_xboole_0)=k4_xboole_0(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_155, c_283])).
% 5.79/2.18  tff(c_310, plain, (![A_56]: (k5_xboole_0(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_295])).
% 5.79/2.18  tff(c_32, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.79/2.18  tff(c_594, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k3_subset_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.79/2.18  tff(c_664, plain, (![B_82, A_83]: (k4_xboole_0(B_82, A_83)=k3_subset_1(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(resolution, [status(thm)], [c_32, c_594])).
% 5.79/2.18  tff(c_679, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=k3_subset_1(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_664])).
% 5.79/2.18  tff(c_687, plain, (![A_9]: (k3_subset_1(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_679])).
% 5.79/2.18  tff(c_387, plain, (![A_69, B_70]: (k3_subset_1(A_69, k3_subset_1(A_69, B_70))=B_70 | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.79/2.18  tff(c_1100, plain, (![B_99, A_100]: (k3_subset_1(B_99, k3_subset_1(B_99, A_100))=A_100 | ~r1_tarski(A_100, B_99))), inference(resolution, [status(thm)], [c_32, c_387])).
% 5.79/2.18  tff(c_1118, plain, (![A_9]: (k3_subset_1(A_9, A_9)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_687, c_1100])).
% 5.79/2.18  tff(c_1133, plain, (![A_9]: (k3_subset_1(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1118])).
% 5.79/2.18  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.79/2.18  tff(c_685, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k3_subset_1(B_4, B_4))), inference(resolution, [status(thm)], [c_8, c_664])).
% 5.79/2.18  tff(c_135, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_120])).
% 5.79/2.18  tff(c_301, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_135, c_283])).
% 5.79/2.18  tff(c_705, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k3_subset_1(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_685, c_301])).
% 5.79/2.18  tff(c_1155, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_705])).
% 5.79/2.18  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.79/2.18  tff(c_503, plain, (![A_74, B_75]: (k3_xboole_0(k4_xboole_0(A_74, B_75), A_74)=k4_xboole_0(A_74, B_75))), inference(resolution, [status(thm)], [c_16, c_120])).
% 5.79/2.18  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.79/2.18  tff(c_512, plain, (![A_74, B_75]: (k5_xboole_0(k4_xboole_0(A_74, B_75), k4_xboole_0(A_74, B_75))=k4_xboole_0(k4_xboole_0(A_74, B_75), A_74))), inference(superposition, [status(thm), theory('equality')], [c_503, c_10])).
% 5.79/2.18  tff(c_2294, plain, (![A_152, B_153]: (k4_xboole_0(k4_xboole_0(A_152, B_153), A_152)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1155, c_512])).
% 5.79/2.18  tff(c_20, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.79/2.18  tff(c_2329, plain, (![A_152, B_153]: (k2_xboole_0(A_152, k4_xboole_0(A_152, B_153))=k5_xboole_0(A_152, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2294, c_20])).
% 5.79/2.18  tff(c_2457, plain, (![A_155, B_156]: (k2_xboole_0(A_155, k4_xboole_0(A_155, B_156))=A_155)), inference(demodulation, [status(thm), theory('equality')], [c_310, c_2329])).
% 5.79/2.18  tff(c_2487, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_811, c_2457])).
% 5.79/2.18  tff(c_1781, plain, (![A_129, B_130]: (k4_subset_1(u1_struct_0(A_129), B_130, k2_tops_1(A_129, B_130))=k2_pre_topc(A_129, B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.79/2.18  tff(c_1788, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1781])).
% 5.79/2.18  tff(c_1793, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1788])).
% 5.79/2.18  tff(c_907, plain, (![A_93, B_94]: (m1_subset_1(k2_tops_1(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.79/2.18  tff(c_24, plain, (![A_17, B_18]: (k3_subset_1(A_17, k3_subset_1(A_17, B_18))=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.79/2.18  tff(c_4043, plain, (![A_191, B_192]: (k3_subset_1(u1_struct_0(A_191), k3_subset_1(u1_struct_0(A_191), k2_tops_1(A_191, B_192)))=k2_tops_1(A_191, B_192) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191))), inference(resolution, [status(thm)], [c_907, c_24])).
% 5.79/2.18  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=k3_subset_1(A_15, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.79/2.18  tff(c_3694, plain, (![A_187, B_188]: (k4_xboole_0(u1_struct_0(A_187), k2_tops_1(A_187, B_188))=k3_subset_1(u1_struct_0(A_187), k2_tops_1(A_187, B_188)) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187))), inference(resolution, [status(thm)], [c_907, c_22])).
% 5.79/2.18  tff(c_3701, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_3694])).
% 5.79/2.18  tff(c_3706, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3701])).
% 5.79/2.18  tff(c_1378, plain, (![A_117, B_118]: (k4_xboole_0(A_117, k4_xboole_0(A_117, B_118))=k3_subset_1(A_117, k4_xboole_0(A_117, B_118)))), inference(resolution, [status(thm)], [c_16, c_664])).
% 5.79/2.18  tff(c_1403, plain, (![A_117, B_118]: (r1_tarski(k3_subset_1(A_117, k4_xboole_0(A_117, B_118)), A_117))), inference(superposition, [status(thm), theory('equality')], [c_1378, c_16])).
% 5.79/2.18  tff(c_3755, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3706, c_1403])).
% 5.79/2.18  tff(c_4049, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4043, c_3755])).
% 5.79/2.18  tff(c_4064, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_4049])).
% 5.79/2.18  tff(c_1342, plain, (![A_110, B_111, C_112]: (k4_subset_1(A_110, B_111, C_112)=k2_xboole_0(B_111, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_110)) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.79/2.18  tff(c_2281, plain, (![B_149, B_150, A_151]: (k4_subset_1(B_149, B_150, A_151)=k2_xboole_0(B_150, A_151) | ~m1_subset_1(B_150, k1_zfmisc_1(B_149)) | ~r1_tarski(A_151, B_149))), inference(resolution, [status(thm)], [c_32, c_1342])).
% 5.79/2.18  tff(c_2290, plain, (![A_151]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_151)=k2_xboole_0('#skF_2', A_151) | ~r1_tarski(A_151, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_46, c_2281])).
% 5.79/2.18  tff(c_4074, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4064, c_2290])).
% 5.79/2.18  tff(c_4095, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2487, c_1793, c_4074])).
% 5.79/2.18  tff(c_4097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1630, c_4095])).
% 5.79/2.18  tff(c_4098, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 5.79/2.18  tff(c_4207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4098, c_114])).
% 5.79/2.18  tff(c_4208, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 5.79/2.18  tff(c_4333, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4208, c_52])).
% 5.79/2.18  tff(c_4897, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4795, c_4333])).
% 5.79/2.18  tff(c_5514, plain, (![A_261, B_262]: (r1_tarski(k2_tops_1(A_261, B_262), B_262) | ~v4_pre_topc(B_262, A_261) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.79/2.18  tff(c_5521, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_5514])).
% 5.79/2.18  tff(c_5526, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4208, c_5521])).
% 5.79/2.18  tff(c_4686, plain, (![A_226, B_227]: (k4_xboole_0(A_226, B_227)=k3_subset_1(A_226, B_227) | ~m1_subset_1(B_227, k1_zfmisc_1(A_226)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.79/2.18  tff(c_4693, plain, (![B_26, A_25]: (k4_xboole_0(B_26, A_25)=k3_subset_1(B_26, A_25) | ~r1_tarski(A_25, B_26))), inference(resolution, [status(thm)], [c_32, c_4686])).
% 5.79/2.18  tff(c_5535, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_5526, c_4693])).
% 5.79/2.18  tff(c_5720, plain, (![A_271, B_272]: (k7_subset_1(u1_struct_0(A_271), B_272, k2_tops_1(A_271, B_272))=k1_tops_1(A_271, B_272) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.79/2.18  tff(c_5727, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_5720])).
% 5.79/2.18  tff(c_5732, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5535, c_4795, c_5727])).
% 5.79/2.18  tff(c_4479, plain, (![A_217, B_218]: (k3_subset_1(A_217, k3_subset_1(A_217, B_218))=B_218 | ~m1_subset_1(B_218, k1_zfmisc_1(A_217)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.79/2.18  tff(c_4484, plain, (![B_26, A_25]: (k3_subset_1(B_26, k3_subset_1(B_26, A_25))=A_25 | ~r1_tarski(A_25, B_26))), inference(resolution, [status(thm)], [c_32, c_4479])).
% 5.79/2.18  tff(c_5757, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5732, c_4484])).
% 5.79/2.18  tff(c_5761, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5526, c_5757])).
% 5.79/2.18  tff(c_5753, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5732, c_5535])).
% 5.79/2.18  tff(c_4756, plain, (![B_230, A_231]: (k4_xboole_0(B_230, A_231)=k3_subset_1(B_230, A_231) | ~r1_tarski(A_231, B_230))), inference(resolution, [status(thm)], [c_32, c_4686])).
% 5.79/2.18  tff(c_5904, plain, (![A_278, B_279]: (k4_xboole_0(A_278, k4_xboole_0(A_278, B_279))=k3_subset_1(A_278, k4_xboole_0(A_278, B_279)))), inference(resolution, [status(thm)], [c_16, c_4756])).
% 5.79/2.18  tff(c_5941, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5753, c_5904])).
% 5.79/2.18  tff(c_5976, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5761, c_5753, c_5941])).
% 5.79/2.18  tff(c_5978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4897, c_5976])).
% 5.79/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.79/2.18  
% 5.79/2.18  Inference rules
% 5.79/2.18  ----------------------
% 5.79/2.18  #Ref     : 0
% 5.79/2.18  #Sup     : 1458
% 5.79/2.18  #Fact    : 0
% 5.79/2.18  #Define  : 0
% 5.79/2.18  #Split   : 11
% 5.79/2.18  #Chain   : 0
% 5.79/2.18  #Close   : 0
% 5.79/2.18  
% 5.79/2.18  Ordering : KBO
% 5.79/2.18  
% 5.79/2.18  Simplification rules
% 5.79/2.18  ----------------------
% 5.79/2.18  #Subsume      : 34
% 5.79/2.18  #Demod        : 1570
% 5.79/2.18  #Tautology    : 1025
% 5.79/2.18  #SimpNegUnit  : 6
% 5.79/2.18  #BackRed      : 32
% 5.79/2.18  
% 5.79/2.18  #Partial instantiations: 0
% 5.79/2.18  #Strategies tried      : 1
% 5.79/2.18  
% 5.79/2.18  Timing (in seconds)
% 5.79/2.18  ----------------------
% 5.79/2.19  Preprocessing        : 0.34
% 5.79/2.19  Parsing              : 0.18
% 5.79/2.19  CNF conversion       : 0.02
% 5.79/2.19  Main loop            : 1.07
% 5.79/2.19  Inferencing          : 0.35
% 5.79/2.19  Reduction            : 0.44
% 5.79/2.19  Demodulation         : 0.34
% 5.79/2.19  BG Simplification    : 0.04
% 5.79/2.19  Subsumption          : 0.17
% 5.79/2.19  Abstraction          : 0.05
% 5.79/2.19  MUC search           : 0.00
% 5.79/2.19  Cooper               : 0.00
% 5.79/2.19  Total                : 1.46
% 5.79/2.19  Index Insertion      : 0.00
% 5.79/2.19  Index Deletion       : 0.00
% 5.79/2.19  Index Matching       : 0.00
% 5.79/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

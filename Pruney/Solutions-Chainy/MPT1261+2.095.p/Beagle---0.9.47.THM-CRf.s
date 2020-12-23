%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:25 EST 2020

% Result     : Theorem 9.61s
% Output     : CNFRefutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 466 expanded)
%              Number of leaves         :   44 ( 173 expanded)
%              Depth                    :   20
%              Number of atoms          :  197 ( 695 expanded)
%              Number of equality atoms :  100 ( 338 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_86,axiom,(
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

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8775,plain,(
    ! [A_327,B_328,C_329] :
      ( k7_subset_1(A_327,B_328,C_329) = k4_xboole_0(B_328,C_329)
      | ~ m1_subset_1(B_328,k1_zfmisc_1(A_327)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8781,plain,(
    ! [C_329] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_329) = k4_xboole_0('#skF_2',C_329) ),
    inference(resolution,[status(thm)],[c_46,c_8775])).

tff(c_52,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_240,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2455,plain,(
    ! [B_157,A_158] :
      ( v4_pre_topc(B_157,A_158)
      | k2_pre_topc(A_158,B_157) != B_157
      | ~ v2_pre_topc(A_158)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2465,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2455])).

tff(c_2470,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_2465])).

tff(c_2471,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_2470])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1345,plain,(
    ! [A_109,B_110,C_111] :
      ( k7_subset_1(A_109,B_110,C_111) = k4_xboole_0(B_110,C_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1355,plain,(
    ! [C_112] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_112) = k4_xboole_0('#skF_2',C_112) ),
    inference(resolution,[status(thm)],[c_46,c_1345])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_187,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_1361,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1355,c_187])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_200,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_523,plain,(
    ! [A_81,B_82] : k3_xboole_0(k4_xboole_0(A_81,B_82),A_81) = k4_xboole_0(A_81,B_82) ),
    inference(resolution,[status(thm)],[c_12,c_200])).

tff(c_574,plain,(
    ! [A_3,B_82] : k3_xboole_0(A_3,k4_xboole_0(A_3,B_82)) = k4_xboole_0(A_3,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_523])).

tff(c_916,plain,(
    ! [A_95,B_96,C_97] :
      ( r1_tarski(A_95,k2_xboole_0(B_96,C_97))
      | ~ r1_tarski(k4_xboole_0(A_95,B_96),C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_946,plain,(
    ! [A_98,B_99] : r1_tarski(A_98,k2_xboole_0(B_99,A_98)) ),
    inference(resolution,[status(thm)],[c_12,c_916])).

tff(c_975,plain,(
    ! [A_100] : r1_tarski(k1_xboole_0,A_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_946])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_983,plain,(
    ! [A_101] : k3_xboole_0(k1_xboole_0,A_101) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_975,c_10])).

tff(c_1022,plain,(
    ! [A_101] : k3_xboole_0(A_101,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_4])).

tff(c_102,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [A_54] : k2_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_288,plain,(
    ! [A_70,B_71] : k2_xboole_0(A_70,k4_xboole_0(B_71,A_70)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_295,plain,(
    ! [B_71] : k4_xboole_0(B_71,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_118])).

tff(c_311,plain,(
    ! [B_72] : k4_xboole_0(B_72,k1_xboole_0) = B_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_295])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_320,plain,(
    ! [B_72] : k4_xboole_0(B_72,B_72) = k3_xboole_0(B_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_18])).

tff(c_331,plain,(
    ! [B_73] : r1_tarski(B_73,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_12])).

tff(c_335,plain,(
    ! [B_73] : k3_xboole_0(B_73,B_73) = B_73 ),
    inference(resolution,[status(thm)],[c_331,c_10])).

tff(c_470,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_479,plain,(
    ! [B_73] : k5_xboole_0(B_73,B_73) = k4_xboole_0(B_73,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_470])).

tff(c_491,plain,(
    ! [B_73] : k5_xboole_0(B_73,B_73) = k3_xboole_0(B_73,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_479])).

tff(c_1059,plain,(
    ! [B_73] : k5_xboole_0(B_73,B_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_491])).

tff(c_566,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(k3_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_523])).

tff(c_2805,plain,(
    ! [A_164,B_165] : k3_xboole_0(A_164,k3_xboole_0(A_164,B_165)) = k3_xboole_0(A_164,B_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4,c_566])).

tff(c_488,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_470])).

tff(c_2821,plain,(
    ! [A_164,B_165] : k5_xboole_0(k3_xboole_0(A_164,B_165),k3_xboole_0(A_164,B_165)) = k4_xboole_0(k3_xboole_0(A_164,B_165),A_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_2805,c_488])).

tff(c_2902,plain,(
    ! [A_166,B_167] : k4_xboole_0(k3_xboole_0(A_166,B_167),A_166) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_2821])).

tff(c_3283,plain,(
    ! [A_174,B_175] : k4_xboole_0(k4_xboole_0(A_174,B_175),A_174) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_2902])).

tff(c_3342,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_3283])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3990,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3342,c_14])).

tff(c_4008,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3990])).

tff(c_2748,plain,(
    ! [A_162,B_163] :
      ( k4_subset_1(u1_struct_0(A_162),B_163,k2_tops_1(A_162,B_163)) = k2_pre_topc(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2755,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2748])).

tff(c_2760,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2755])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_191,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_199,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_191])).

tff(c_207,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_199,c_200])).

tff(c_482,plain,(
    k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) = k5_xboole_0('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_470])).

tff(c_502,plain,(
    k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) = k3_xboole_0('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_482])).

tff(c_506,plain,(
    k2_xboole_0(u1_struct_0('#skF_1'),k3_xboole_0('#skF_2',k1_xboole_0)) = k2_xboole_0(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_14])).

tff(c_515,plain,(
    k2_xboole_0(u1_struct_0('#skF_1'),k3_xboole_0('#skF_2',k1_xboole_0)) = k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_506])).

tff(c_1057,plain,(
    k2_xboole_0(u1_struct_0('#skF_1'),k1_xboole_0) = k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_515])).

tff(c_1062,plain,(
    k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1057])).

tff(c_1213,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k3_subset_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1221,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1213])).

tff(c_1294,plain,(
    k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_14])).

tff(c_2540,plain,(
    k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_1294])).

tff(c_971,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_946])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(A_14,k2_xboole_0(B_15,C_16))
      | ~ r1_tarski(k4_xboole_0(A_14,B_15),C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2913,plain,(
    ! [A_166,B_167,C_16] :
      ( r1_tarski(k3_xboole_0(A_166,B_167),k2_xboole_0(A_166,C_16))
      | ~ r1_tarski(k1_xboole_0,C_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2902,c_16])).

tff(c_4294,plain,(
    ! [A_186,B_187,C_188] : r1_tarski(k3_xboole_0(A_186,B_187),k2_xboole_0(A_186,C_188)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_2913])).

tff(c_4412,plain,(
    ! [B_189] : r1_tarski(k3_xboole_0('#skF_2',B_189),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2540,c_4294])).

tff(c_4467,plain,(
    ! [B_190] : r1_tarski(k4_xboole_0('#skF_2',B_190),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_4412])).

tff(c_4484,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_4467])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,k1_zfmisc_1(B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1956,plain,(
    ! [A_132,B_133,C_134] :
      ( k4_subset_1(A_132,B_133,C_134) = k2_xboole_0(B_133,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(A_132))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7538,plain,(
    ! [B_261,B_262,A_263] :
      ( k4_subset_1(B_261,B_262,A_263) = k2_xboole_0(B_262,A_263)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(B_261))
      | ~ r1_tarski(A_263,B_261) ) ),
    inference(resolution,[status(thm)],[c_32,c_1956])).

tff(c_7585,plain,(
    ! [A_265] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_265) = k2_xboole_0('#skF_2',A_265)
      | ~ r1_tarski(A_265,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_46,c_7538])).

tff(c_7633,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4484,c_7585])).

tff(c_7687,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4008,c_2760,c_7633])).

tff(c_7689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2471,c_7687])).

tff(c_7690,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7690,c_187])).

tff(c_7967,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_8004,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7967,c_52])).

tff(c_8815,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8781,c_8004])).

tff(c_10219,plain,(
    ! [A_370,B_371] :
      ( r1_tarski(k2_tops_1(A_370,B_371),B_371)
      | ~ v4_pre_topc(B_371,A_370)
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ l1_pre_topc(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10226,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_10219])).

tff(c_10231,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7967,c_10226])).

tff(c_11557,plain,(
    ! [A_412,B_413] :
      ( k7_subset_1(u1_struct_0(A_412),B_413,k2_tops_1(A_412,B_413)) = k1_tops_1(A_412,B_413)
      | ~ m1_subset_1(B_413,k1_zfmisc_1(u1_struct_0(A_412)))
      | ~ l1_pre_topc(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_11564,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_11557])).

tff(c_11569,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8781,c_11564])).

tff(c_8558,plain,(
    ! [A_321,B_322] :
      ( k4_xboole_0(A_321,B_322) = k3_subset_1(A_321,B_322)
      | ~ m1_subset_1(B_322,k1_zfmisc_1(A_321)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_11909,plain,(
    ! [B_417,A_418] :
      ( k4_xboole_0(B_417,A_418) = k3_subset_1(B_417,A_418)
      | ~ r1_tarski(A_418,B_417) ) ),
    inference(resolution,[status(thm)],[c_32,c_8558])).

tff(c_11969,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10231,c_11909])).

tff(c_12023,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11569,c_11969])).

tff(c_8366,plain,(
    ! [A_312,B_313] :
      ( k3_subset_1(A_312,k3_subset_1(A_312,B_313)) = B_313
      | ~ m1_subset_1(B_313,k1_zfmisc_1(A_312)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8371,plain,(
    ! [B_32,A_31] :
      ( k3_subset_1(B_32,k3_subset_1(B_32,A_31)) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_32,c_8366])).

tff(c_14872,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12023,c_8371])).

tff(c_14876,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10231,c_14872])).

tff(c_11605,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11569,c_12])).

tff(c_11614,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_11605,c_10])).

tff(c_12002,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_subset_1(A_10,k4_xboole_0(A_10,B_11)) ),
    inference(resolution,[status(thm)],[c_12,c_11909])).

tff(c_15240,plain,(
    ! [A_489,B_490] : k3_subset_1(A_489,k4_xboole_0(A_489,B_490)) = k3_xboole_0(A_489,B_490) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12002])).

tff(c_15246,plain,(
    ! [A_489,B_490] :
      ( k3_subset_1(A_489,k3_xboole_0(A_489,B_490)) = k4_xboole_0(A_489,B_490)
      | ~ r1_tarski(k4_xboole_0(A_489,B_490),A_489) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15240,c_8371])).

tff(c_16458,plain,(
    ! [A_506,B_507] : k3_subset_1(A_506,k3_xboole_0(A_506,B_507)) = k4_xboole_0(A_506,B_507) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_15246])).

tff(c_20029,plain,(
    ! [A_547,B_548] : k3_subset_1(A_547,k3_xboole_0(B_548,A_547)) = k4_xboole_0(A_547,B_548) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_16458])).

tff(c_20075,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11614,c_20029])).

tff(c_20148,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14876,c_20075])).

tff(c_20150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8815,c_20148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:34:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.61/3.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.52  
% 9.61/3.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.52  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.61/3.52  
% 9.61/3.52  %Foreground sorts:
% 9.61/3.52  
% 9.61/3.52  
% 9.61/3.52  %Background operators:
% 9.61/3.52  
% 9.61/3.52  
% 9.61/3.52  %Foreground operators:
% 9.61/3.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.61/3.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.61/3.52  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.61/3.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.61/3.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.61/3.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.61/3.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.61/3.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.61/3.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.61/3.52  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.61/3.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.61/3.52  tff('#skF_2', type, '#skF_2': $i).
% 9.61/3.52  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.61/3.52  tff('#skF_1', type, '#skF_1': $i).
% 9.61/3.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.61/3.52  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.61/3.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.61/3.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.61/3.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.61/3.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.61/3.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.61/3.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.61/3.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.61/3.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.61/3.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.61/3.52  
% 9.61/3.55  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 9.61/3.55  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.61/3.55  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 9.61/3.55  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 9.61/3.55  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.61/3.55  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.61/3.55  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.61/3.55  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.61/3.55  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.61/3.55  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.61/3.55  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.61/3.55  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.61/3.55  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 9.61/3.55  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.61/3.55  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 9.61/3.55  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.61/3.55  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 9.61/3.55  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 9.61/3.55  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.61/3.55  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.61/3.55  tff(c_8775, plain, (![A_327, B_328, C_329]: (k7_subset_1(A_327, B_328, C_329)=k4_xboole_0(B_328, C_329) | ~m1_subset_1(B_328, k1_zfmisc_1(A_327)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.61/3.55  tff(c_8781, plain, (![C_329]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_329)=k4_xboole_0('#skF_2', C_329))), inference(resolution, [status(thm)], [c_46, c_8775])).
% 9.61/3.55  tff(c_52, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.61/3.55  tff(c_240, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 9.61/3.55  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.61/3.55  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.61/3.55  tff(c_2455, plain, (![B_157, A_158]: (v4_pre_topc(B_157, A_158) | k2_pre_topc(A_158, B_157)!=B_157 | ~v2_pre_topc(A_158) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.61/3.55  tff(c_2465, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_2455])).
% 9.61/3.55  tff(c_2470, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_2465])).
% 9.61/3.55  tff(c_2471, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_240, c_2470])).
% 9.61/3.55  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.61/3.55  tff(c_1345, plain, (![A_109, B_110, C_111]: (k7_subset_1(A_109, B_110, C_111)=k4_xboole_0(B_110, C_111) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.61/3.55  tff(c_1355, plain, (![C_112]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_112)=k4_xboole_0('#skF_2', C_112))), inference(resolution, [status(thm)], [c_46, c_1345])).
% 9.61/3.55  tff(c_58, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.61/3.55  tff(c_187, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 9.61/3.55  tff(c_1361, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1355, c_187])).
% 9.61/3.55  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.61/3.55  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.61/3.55  tff(c_200, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.61/3.55  tff(c_523, plain, (![A_81, B_82]: (k3_xboole_0(k4_xboole_0(A_81, B_82), A_81)=k4_xboole_0(A_81, B_82))), inference(resolution, [status(thm)], [c_12, c_200])).
% 9.61/3.55  tff(c_574, plain, (![A_3, B_82]: (k3_xboole_0(A_3, k4_xboole_0(A_3, B_82))=k4_xboole_0(A_3, B_82))), inference(superposition, [status(thm), theory('equality')], [c_4, c_523])).
% 9.61/3.55  tff(c_916, plain, (![A_95, B_96, C_97]: (r1_tarski(A_95, k2_xboole_0(B_96, C_97)) | ~r1_tarski(k4_xboole_0(A_95, B_96), C_97))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.55  tff(c_946, plain, (![A_98, B_99]: (r1_tarski(A_98, k2_xboole_0(B_99, A_98)))), inference(resolution, [status(thm)], [c_12, c_916])).
% 9.61/3.55  tff(c_975, plain, (![A_100]: (r1_tarski(k1_xboole_0, A_100))), inference(superposition, [status(thm), theory('equality')], [c_8, c_946])).
% 9.61/3.55  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.61/3.55  tff(c_983, plain, (![A_101]: (k3_xboole_0(k1_xboole_0, A_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_975, c_10])).
% 9.61/3.55  tff(c_1022, plain, (![A_101]: (k3_xboole_0(A_101, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_983, c_4])).
% 9.61/3.55  tff(c_102, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.61/3.55  tff(c_118, plain, (![A_54]: (k2_xboole_0(k1_xboole_0, A_54)=A_54)), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 9.61/3.55  tff(c_288, plain, (![A_70, B_71]: (k2_xboole_0(A_70, k4_xboole_0(B_71, A_70))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.61/3.55  tff(c_295, plain, (![B_71]: (k4_xboole_0(B_71, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_71))), inference(superposition, [status(thm), theory('equality')], [c_288, c_118])).
% 9.61/3.55  tff(c_311, plain, (![B_72]: (k4_xboole_0(B_72, k1_xboole_0)=B_72)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_295])).
% 9.61/3.55  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.61/3.55  tff(c_320, plain, (![B_72]: (k4_xboole_0(B_72, B_72)=k3_xboole_0(B_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_311, c_18])).
% 9.61/3.55  tff(c_331, plain, (![B_73]: (r1_tarski(B_73, B_73))), inference(superposition, [status(thm), theory('equality')], [c_311, c_12])).
% 9.61/3.55  tff(c_335, plain, (![B_73]: (k3_xboole_0(B_73, B_73)=B_73)), inference(resolution, [status(thm)], [c_331, c_10])).
% 9.61/3.55  tff(c_470, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.55  tff(c_479, plain, (![B_73]: (k5_xboole_0(B_73, B_73)=k4_xboole_0(B_73, B_73))), inference(superposition, [status(thm), theory('equality')], [c_335, c_470])).
% 9.61/3.55  tff(c_491, plain, (![B_73]: (k5_xboole_0(B_73, B_73)=k3_xboole_0(B_73, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_479])).
% 9.61/3.55  tff(c_1059, plain, (![B_73]: (k5_xboole_0(B_73, B_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_491])).
% 9.61/3.55  tff(c_566, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(k3_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_523])).
% 9.61/3.55  tff(c_2805, plain, (![A_164, B_165]: (k3_xboole_0(A_164, k3_xboole_0(A_164, B_165))=k3_xboole_0(A_164, B_165))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4, c_566])).
% 9.61/3.55  tff(c_488, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_470])).
% 9.61/3.55  tff(c_2821, plain, (![A_164, B_165]: (k5_xboole_0(k3_xboole_0(A_164, B_165), k3_xboole_0(A_164, B_165))=k4_xboole_0(k3_xboole_0(A_164, B_165), A_164))), inference(superposition, [status(thm), theory('equality')], [c_2805, c_488])).
% 9.61/3.55  tff(c_2902, plain, (![A_166, B_167]: (k4_xboole_0(k3_xboole_0(A_166, B_167), A_166)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_2821])).
% 9.61/3.55  tff(c_3283, plain, (![A_174, B_175]: (k4_xboole_0(k4_xboole_0(A_174, B_175), A_174)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_574, c_2902])).
% 9.61/3.55  tff(c_3342, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1361, c_3283])).
% 9.61/3.55  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.61/3.55  tff(c_3990, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3342, c_14])).
% 9.61/3.55  tff(c_4008, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3990])).
% 9.61/3.55  tff(c_2748, plain, (![A_162, B_163]: (k4_subset_1(u1_struct_0(A_162), B_163, k2_tops_1(A_162, B_163))=k2_pre_topc(A_162, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.61/3.55  tff(c_2755, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_2748])).
% 9.61/3.55  tff(c_2760, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2755])).
% 9.61/3.55  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.61/3.55  tff(c_191, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.61/3.55  tff(c_199, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_191])).
% 9.61/3.55  tff(c_207, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_199, c_200])).
% 9.61/3.55  tff(c_482, plain, (k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))=k5_xboole_0('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_207, c_470])).
% 9.61/3.55  tff(c_502, plain, (k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))=k3_xboole_0('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_491, c_482])).
% 9.61/3.55  tff(c_506, plain, (k2_xboole_0(u1_struct_0('#skF_1'), k3_xboole_0('#skF_2', k1_xboole_0))=k2_xboole_0(u1_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_502, c_14])).
% 9.61/3.55  tff(c_515, plain, (k2_xboole_0(u1_struct_0('#skF_1'), k3_xboole_0('#skF_2', k1_xboole_0))=k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_506])).
% 9.61/3.55  tff(c_1057, plain, (k2_xboole_0(u1_struct_0('#skF_1'), k1_xboole_0)=k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_515])).
% 9.61/3.55  tff(c_1062, plain, (k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1057])).
% 9.61/3.55  tff(c_1213, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k3_subset_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.61/3.55  tff(c_1221, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1213])).
% 9.61/3.55  tff(c_1294, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1221, c_14])).
% 9.61/3.55  tff(c_2540, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1062, c_1294])).
% 9.61/3.55  tff(c_971, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_946])).
% 9.61/3.55  tff(c_16, plain, (![A_14, B_15, C_16]: (r1_tarski(A_14, k2_xboole_0(B_15, C_16)) | ~r1_tarski(k4_xboole_0(A_14, B_15), C_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.55  tff(c_2913, plain, (![A_166, B_167, C_16]: (r1_tarski(k3_xboole_0(A_166, B_167), k2_xboole_0(A_166, C_16)) | ~r1_tarski(k1_xboole_0, C_16))), inference(superposition, [status(thm), theory('equality')], [c_2902, c_16])).
% 9.61/3.55  tff(c_4294, plain, (![A_186, B_187, C_188]: (r1_tarski(k3_xboole_0(A_186, B_187), k2_xboole_0(A_186, C_188)))), inference(demodulation, [status(thm), theory('equality')], [c_971, c_2913])).
% 9.61/3.55  tff(c_4412, plain, (![B_189]: (r1_tarski(k3_xboole_0('#skF_2', B_189), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2540, c_4294])).
% 9.61/3.55  tff(c_4467, plain, (![B_190]: (r1_tarski(k4_xboole_0('#skF_2', B_190), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_574, c_4412])).
% 9.61/3.55  tff(c_4484, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1361, c_4467])).
% 9.61/3.55  tff(c_32, plain, (![A_31, B_32]: (m1_subset_1(A_31, k1_zfmisc_1(B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.61/3.55  tff(c_1956, plain, (![A_132, B_133, C_134]: (k4_subset_1(A_132, B_133, C_134)=k2_xboole_0(B_133, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(A_132)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.61/3.55  tff(c_7538, plain, (![B_261, B_262, A_263]: (k4_subset_1(B_261, B_262, A_263)=k2_xboole_0(B_262, A_263) | ~m1_subset_1(B_262, k1_zfmisc_1(B_261)) | ~r1_tarski(A_263, B_261))), inference(resolution, [status(thm)], [c_32, c_1956])).
% 9.61/3.55  tff(c_7585, plain, (![A_265]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_265)=k2_xboole_0('#skF_2', A_265) | ~r1_tarski(A_265, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_46, c_7538])).
% 9.61/3.55  tff(c_7633, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4484, c_7585])).
% 9.61/3.55  tff(c_7687, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4008, c_2760, c_7633])).
% 9.61/3.55  tff(c_7689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2471, c_7687])).
% 9.61/3.55  tff(c_7690, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 9.61/3.55  tff(c_7966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7690, c_187])).
% 9.61/3.55  tff(c_7967, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 9.61/3.55  tff(c_8004, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7967, c_52])).
% 9.61/3.55  tff(c_8815, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8781, c_8004])).
% 9.61/3.55  tff(c_10219, plain, (![A_370, B_371]: (r1_tarski(k2_tops_1(A_370, B_371), B_371) | ~v4_pre_topc(B_371, A_370) | ~m1_subset_1(B_371, k1_zfmisc_1(u1_struct_0(A_370))) | ~l1_pre_topc(A_370))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.61/3.55  tff(c_10226, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_10219])).
% 9.61/3.55  tff(c_10231, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7967, c_10226])).
% 9.61/3.55  tff(c_11557, plain, (![A_412, B_413]: (k7_subset_1(u1_struct_0(A_412), B_413, k2_tops_1(A_412, B_413))=k1_tops_1(A_412, B_413) | ~m1_subset_1(B_413, k1_zfmisc_1(u1_struct_0(A_412))) | ~l1_pre_topc(A_412))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.61/3.55  tff(c_11564, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_11557])).
% 9.61/3.55  tff(c_11569, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8781, c_11564])).
% 9.61/3.55  tff(c_8558, plain, (![A_321, B_322]: (k4_xboole_0(A_321, B_322)=k3_subset_1(A_321, B_322) | ~m1_subset_1(B_322, k1_zfmisc_1(A_321)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.61/3.55  tff(c_11909, plain, (![B_417, A_418]: (k4_xboole_0(B_417, A_418)=k3_subset_1(B_417, A_418) | ~r1_tarski(A_418, B_417))), inference(resolution, [status(thm)], [c_32, c_8558])).
% 9.61/3.55  tff(c_11969, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10231, c_11909])).
% 9.61/3.55  tff(c_12023, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11569, c_11969])).
% 9.61/3.55  tff(c_8366, plain, (![A_312, B_313]: (k3_subset_1(A_312, k3_subset_1(A_312, B_313))=B_313 | ~m1_subset_1(B_313, k1_zfmisc_1(A_312)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.61/3.55  tff(c_8371, plain, (![B_32, A_31]: (k3_subset_1(B_32, k3_subset_1(B_32, A_31))=A_31 | ~r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_32, c_8366])).
% 9.61/3.55  tff(c_14872, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12023, c_8371])).
% 9.61/3.55  tff(c_14876, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10231, c_14872])).
% 9.61/3.55  tff(c_11605, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11569, c_12])).
% 9.61/3.55  tff(c_11614, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_11605, c_10])).
% 9.61/3.55  tff(c_12002, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_subset_1(A_10, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_12, c_11909])).
% 9.61/3.55  tff(c_15240, plain, (![A_489, B_490]: (k3_subset_1(A_489, k4_xboole_0(A_489, B_490))=k3_xboole_0(A_489, B_490))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12002])).
% 9.61/3.55  tff(c_15246, plain, (![A_489, B_490]: (k3_subset_1(A_489, k3_xboole_0(A_489, B_490))=k4_xboole_0(A_489, B_490) | ~r1_tarski(k4_xboole_0(A_489, B_490), A_489))), inference(superposition, [status(thm), theory('equality')], [c_15240, c_8371])).
% 9.61/3.55  tff(c_16458, plain, (![A_506, B_507]: (k3_subset_1(A_506, k3_xboole_0(A_506, B_507))=k4_xboole_0(A_506, B_507))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_15246])).
% 9.61/3.55  tff(c_20029, plain, (![A_547, B_548]: (k3_subset_1(A_547, k3_xboole_0(B_548, A_547))=k4_xboole_0(A_547, B_548))), inference(superposition, [status(thm), theory('equality')], [c_4, c_16458])).
% 9.61/3.55  tff(c_20075, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11614, c_20029])).
% 9.61/3.55  tff(c_20148, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14876, c_20075])).
% 9.61/3.55  tff(c_20150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8815, c_20148])).
% 9.61/3.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.55  
% 9.61/3.55  Inference rules
% 9.61/3.55  ----------------------
% 9.61/3.55  #Ref     : 0
% 9.61/3.55  #Sup     : 4890
% 9.61/3.55  #Fact    : 0
% 9.61/3.55  #Define  : 0
% 9.61/3.55  #Split   : 2
% 9.61/3.55  #Chain   : 0
% 9.61/3.55  #Close   : 0
% 9.61/3.55  
% 9.61/3.55  Ordering : KBO
% 9.61/3.55  
% 9.61/3.55  Simplification rules
% 9.61/3.55  ----------------------
% 9.61/3.55  #Subsume      : 24
% 9.61/3.55  #Demod        : 4514
% 9.61/3.55  #Tautology    : 3540
% 9.61/3.55  #SimpNegUnit  : 5
% 9.61/3.55  #BackRed      : 14
% 9.61/3.55  
% 9.61/3.55  #Partial instantiations: 0
% 9.61/3.55  #Strategies tried      : 1
% 9.61/3.55  
% 9.61/3.55  Timing (in seconds)
% 9.61/3.55  ----------------------
% 9.61/3.55  Preprocessing        : 0.37
% 9.61/3.55  Parsing              : 0.21
% 9.61/3.55  CNF conversion       : 0.02
% 9.61/3.55  Main loop            : 2.39
% 9.61/3.55  Inferencing          : 0.58
% 9.61/3.55  Reduction            : 1.20
% 9.61/3.55  Demodulation         : 1.02
% 9.61/3.55  BG Simplification    : 0.07
% 9.61/3.55  Subsumption          : 0.38
% 9.61/3.55  Abstraction          : 0.10
% 9.61/3.55  MUC search           : 0.00
% 9.61/3.55  Cooper               : 0.00
% 9.61/3.55  Total                : 2.82
% 9.61/3.55  Index Insertion      : 0.00
% 9.61/3.55  Index Deletion       : 0.00
% 9.61/3.55  Index Matching       : 0.00
% 9.61/3.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

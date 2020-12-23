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
% DateTime   : Thu Dec  3 10:21:19 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 285 expanded)
%              Number of leaves         :   44 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  181 ( 541 expanded)
%              Number of equality atoms :   82 ( 189 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_116,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6466,plain,(
    ! [A_284,B_285,C_286] :
      ( k7_subset_1(A_284,B_285,C_286) = k4_xboole_0(B_285,C_286)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(A_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6472,plain,(
    ! [C_286] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_286) = k4_xboole_0('#skF_2',C_286) ),
    inference(resolution,[status(thm)],[c_44,c_6466])).

tff(c_50,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_186,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_817,plain,(
    ! [A_94,B_95,C_96] :
      ( k7_subset_1(A_94,B_95,C_96) = k4_xboole_0(B_95,C_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_857,plain,(
    ! [C_98] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_98) = k4_xboole_0('#skF_2',C_98) ),
    inference(resolution,[status(thm)],[c_44,c_817])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_115,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_863,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_115])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_156,plain,(
    ! [A_61,B_62] : k1_setfam_1(k2_tarski(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_287,plain,(
    ! [A_71,B_72] : k1_setfam_1(k2_tarski(A_71,B_72)) = k3_xboole_0(B_72,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_156])).

tff(c_28,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_293,plain,(
    ! [B_72,A_71] : k3_xboole_0(B_72,A_71) = k3_xboole_0(A_71,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_28])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_136])).

tff(c_410,plain,(
    ! [A_79,B_80] : k2_xboole_0(k3_xboole_0(A_79,B_80),k4_xboole_0(A_79,B_80)) = A_79 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_428,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_8,B_9),A_8),k1_xboole_0) = k4_xboole_0(A_8,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_410])).

tff(c_1187,plain,(
    ! [A_115,B_116] : k3_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k4_xboole_0(A_115,B_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_293,c_428])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1206,plain,(
    ! [A_115,B_116] : k2_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = A_115 ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_10])).

tff(c_1309,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_863,c_1206])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1293,plain,(
    ! [A_119,B_120] :
      ( k4_subset_1(u1_struct_0(A_119),B_120,k2_tops_1(A_119,B_120)) = k2_pre_topc(A_119,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1300,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1293])).

tff(c_1305,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1300])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1096,plain,(
    ! [A_108,B_109,C_110] :
      ( k4_subset_1(A_108,B_109,C_110) = k2_xboole_0(B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(A_108))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2725,plain,(
    ! [B_163,B_164,A_165] :
      ( k4_subset_1(B_163,B_164,A_165) = k2_xboole_0(B_164,A_165)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(B_163))
      | ~ r1_tarski(A_165,B_163) ) ),
    inference(resolution,[status(thm)],[c_32,c_1096])).

tff(c_2895,plain,(
    ! [A_168] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_168) = k2_xboole_0('#skF_2',A_168)
      | ~ r1_tarski(A_168,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2725])).

tff(c_2991,plain,(
    ! [A_171] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_171) = k2_xboole_0('#skF_2',A_171)
      | k4_xboole_0(A_171,u1_struct_0('#skF_1')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_2895])).

tff(c_3024,plain,
    ( k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_2991])).

tff(c_3045,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_3024])).

tff(c_3555,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3045])).

tff(c_912,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(k2_tops_1(A_100,B_101),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k3_subset_1(A_18,k3_subset_1(A_18,B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_924,plain,(
    ! [A_100,B_101] :
      ( k3_subset_1(u1_struct_0(A_100),k3_subset_1(u1_struct_0(A_100),k2_tops_1(A_100,B_101))) = k2_tops_1(A_100,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_912,c_22])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k3_subset_1(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4909,plain,(
    ! [A_227,B_228] :
      ( k4_xboole_0(u1_struct_0(A_227),k2_tops_1(A_227,B_228)) = k3_subset_1(u1_struct_0(A_227),k2_tops_1(A_227,B_228))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(resolution,[status(thm)],[c_912,c_20])).

tff(c_4916,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_4909])).

tff(c_4921,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4916])).

tff(c_668,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k3_subset_1(A_86,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1596,plain,(
    ! [B_127,A_128] :
      ( k4_xboole_0(B_127,A_128) = k3_subset_1(B_127,A_128)
      | ~ r1_tarski(A_128,B_127) ) ),
    inference(resolution,[status(thm)],[c_32,c_668])).

tff(c_1905,plain,(
    ! [A_141,B_142] : k4_xboole_0(A_141,k4_xboole_0(A_141,B_142)) = k3_subset_1(A_141,k4_xboole_0(A_141,B_142)) ),
    inference(resolution,[status(thm)],[c_12,c_1596])).

tff(c_1933,plain,(
    ! [A_141,B_142] : r1_tarski(k3_subset_1(A_141,k4_xboole_0(A_141,B_142)),A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_1905,c_12])).

tff(c_5379,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4921,c_1933])).

tff(c_5599,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_5379])).

tff(c_5614,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_5599])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5635,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5614,c_4])).

tff(c_5651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3555,c_5635])).

tff(c_5652,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3045])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_966,plain,(
    ! [A_103,B_104] :
      ( v4_pre_topc(k2_pre_topc(A_103,B_104),A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_973,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_966])).

tff(c_978,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_973])).

tff(c_5656,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5652,c_978])).

tff(c_5658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_5656])).

tff(c_5659,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5659,c_115])).

tff(c_5802,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5871,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5802,c_50])).

tff(c_6557,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6472,c_5871])).

tff(c_6902,plain,(
    ! [A_308,B_309] :
      ( r1_tarski(k2_tops_1(A_308,B_309),B_309)
      | ~ v4_pre_topc(B_309,A_308)
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6909,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_6902])).

tff(c_6914,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5802,c_6909])).

tff(c_7144,plain,(
    ! [A_317,B_318] :
      ( k7_subset_1(u1_struct_0(A_317),B_318,k2_tops_1(A_317,B_318)) = k1_tops_1(A_317,B_318)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ l1_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7151,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_7144])).

tff(c_7156,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6472,c_7151])).

tff(c_6341,plain,(
    ! [A_279,B_280] :
      ( k4_xboole_0(A_279,B_280) = k3_subset_1(A_279,B_280)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(A_279)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7272,plain,(
    ! [B_320,A_321] :
      ( k4_xboole_0(B_320,A_321) = k3_subset_1(B_320,A_321)
      | ~ r1_tarski(A_321,B_320) ) ),
    inference(resolution,[status(thm)],[c_32,c_6341])).

tff(c_7278,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6914,c_7272])).

tff(c_7299,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7156,c_7278])).

tff(c_6185,plain,(
    ! [A_271,B_272] :
      ( k3_subset_1(A_271,k3_subset_1(A_271,B_272)) = B_272
      | ~ m1_subset_1(B_272,k1_zfmisc_1(A_271)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6190,plain,(
    ! [B_29,A_28] :
      ( k3_subset_1(B_29,k3_subset_1(B_29,A_28)) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_32,c_6185])).

tff(c_7372,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7299,c_6190])).

tff(c_7376,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6914,c_7372])).

tff(c_5824,plain,(
    ! [A_251,B_252] :
      ( k4_xboole_0(A_251,B_252) = k1_xboole_0
      | ~ r1_tarski(A_251,B_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5836,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_5824])).

tff(c_7166,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7156,c_5836])).

tff(c_7629,plain,(
    ! [B_337,A_338] :
      ( k4_xboole_0(B_337,A_338) = k3_subset_1(B_337,A_338)
      | k4_xboole_0(A_338,B_337) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_7272])).

tff(c_7633,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7166,c_7629])).

tff(c_7654,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7376,c_7633])).

tff(c_7656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6557,c_7654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.19/0.33  % DateTime   : Tue Dec  1 16:21:35 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.30/2.31  
% 6.30/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.30/2.31  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.30/2.31  
% 6.30/2.31  %Foreground sorts:
% 6.30/2.31  
% 6.30/2.31  
% 6.30/2.31  %Background operators:
% 6.30/2.31  
% 6.30/2.31  
% 6.30/2.31  %Foreground operators:
% 6.30/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.30/2.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.30/2.31  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.30/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.30/2.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.30/2.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.30/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.30/2.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.30/2.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.30/2.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.30/2.31  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.30/2.31  tff('#skF_2', type, '#skF_2': $i).
% 6.30/2.31  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.30/2.31  tff('#skF_1', type, '#skF_1': $i).
% 6.30/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.30/2.31  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.30/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.30/2.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.30/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.30/2.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.30/2.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.30/2.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.30/2.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.30/2.31  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.30/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.30/2.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.30/2.31  
% 6.30/2.34  tff(f_116, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 6.30/2.34  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.30/2.34  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.30/2.34  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.30/2.34  tff(f_63, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.30/2.34  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.30/2.34  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.30/2.34  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.30/2.34  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 6.30/2.34  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 6.30/2.34  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.30/2.34  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.30/2.34  tff(f_73, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.30/2.34  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.30/2.34  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.30/2.34  tff(f_81, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 6.30/2.34  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 6.30/2.34  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 6.30/2.34  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.30/2.34  tff(c_6466, plain, (![A_284, B_285, C_286]: (k7_subset_1(A_284, B_285, C_286)=k4_xboole_0(B_285, C_286) | ~m1_subset_1(B_285, k1_zfmisc_1(A_284)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.30/2.34  tff(c_6472, plain, (![C_286]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_286)=k4_xboole_0('#skF_2', C_286))), inference(resolution, [status(thm)], [c_44, c_6466])).
% 6.30/2.34  tff(c_50, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.30/2.34  tff(c_186, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 6.30/2.34  tff(c_817, plain, (![A_94, B_95, C_96]: (k7_subset_1(A_94, B_95, C_96)=k4_xboole_0(B_95, C_96) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.30/2.34  tff(c_857, plain, (![C_98]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_98)=k4_xboole_0('#skF_2', C_98))), inference(resolution, [status(thm)], [c_44, c_817])).
% 6.30/2.34  tff(c_56, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.30/2.34  tff(c_115, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 6.30/2.34  tff(c_863, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_857, c_115])).
% 6.30/2.34  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.30/2.34  tff(c_16, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.30/2.34  tff(c_156, plain, (![A_61, B_62]: (k1_setfam_1(k2_tarski(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.30/2.34  tff(c_287, plain, (![A_71, B_72]: (k1_setfam_1(k2_tarski(A_71, B_72))=k3_xboole_0(B_72, A_71))), inference(superposition, [status(thm), theory('equality')], [c_16, c_156])).
% 6.30/2.34  tff(c_28, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.30/2.34  tff(c_293, plain, (![B_72, A_71]: (k3_xboole_0(B_72, A_71)=k3_xboole_0(A_71, B_72))), inference(superposition, [status(thm), theory('equality')], [c_287, c_28])).
% 6.30/2.34  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.30/2.34  tff(c_136, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.30/2.34  tff(c_148, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_136])).
% 6.30/2.34  tff(c_410, plain, (![A_79, B_80]: (k2_xboole_0(k3_xboole_0(A_79, B_80), k4_xboole_0(A_79, B_80))=A_79)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.30/2.34  tff(c_428, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_8, B_9), A_8), k1_xboole_0)=k4_xboole_0(A_8, B_9))), inference(superposition, [status(thm), theory('equality')], [c_148, c_410])).
% 6.30/2.34  tff(c_1187, plain, (![A_115, B_116]: (k3_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k4_xboole_0(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_293, c_428])).
% 6.30/2.34  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.30/2.34  tff(c_1206, plain, (![A_115, B_116]: (k2_xboole_0(A_115, k4_xboole_0(A_115, B_116))=A_115)), inference(superposition, [status(thm), theory('equality')], [c_1187, c_10])).
% 6.30/2.34  tff(c_1309, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_863, c_1206])).
% 6.30/2.34  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.30/2.34  tff(c_1293, plain, (![A_119, B_120]: (k4_subset_1(u1_struct_0(A_119), B_120, k2_tops_1(A_119, B_120))=k2_pre_topc(A_119, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.30/2.34  tff(c_1300, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1293])).
% 6.30/2.34  tff(c_1305, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1300])).
% 6.30/2.34  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.30/2.34  tff(c_32, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.30/2.34  tff(c_1096, plain, (![A_108, B_109, C_110]: (k4_subset_1(A_108, B_109, C_110)=k2_xboole_0(B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(A_108)) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.30/2.34  tff(c_2725, plain, (![B_163, B_164, A_165]: (k4_subset_1(B_163, B_164, A_165)=k2_xboole_0(B_164, A_165) | ~m1_subset_1(B_164, k1_zfmisc_1(B_163)) | ~r1_tarski(A_165, B_163))), inference(resolution, [status(thm)], [c_32, c_1096])).
% 6.30/2.34  tff(c_2895, plain, (![A_168]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_168)=k2_xboole_0('#skF_2', A_168) | ~r1_tarski(A_168, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_44, c_2725])).
% 6.30/2.34  tff(c_2991, plain, (![A_171]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_171)=k2_xboole_0('#skF_2', A_171) | k4_xboole_0(A_171, u1_struct_0('#skF_1'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_2895])).
% 6.30/2.34  tff(c_3024, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1305, c_2991])).
% 6.30/2.34  tff(c_3045, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1309, c_3024])).
% 6.30/2.34  tff(c_3555, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3045])).
% 6.30/2.34  tff(c_912, plain, (![A_100, B_101]: (m1_subset_1(k2_tops_1(A_100, B_101), k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.30/2.34  tff(c_22, plain, (![A_18, B_19]: (k3_subset_1(A_18, k3_subset_1(A_18, B_19))=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.30/2.34  tff(c_924, plain, (![A_100, B_101]: (k3_subset_1(u1_struct_0(A_100), k3_subset_1(u1_struct_0(A_100), k2_tops_1(A_100, B_101)))=k2_tops_1(A_100, B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_912, c_22])).
% 6.30/2.34  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k3_subset_1(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.30/2.34  tff(c_4909, plain, (![A_227, B_228]: (k4_xboole_0(u1_struct_0(A_227), k2_tops_1(A_227, B_228))=k3_subset_1(u1_struct_0(A_227), k2_tops_1(A_227, B_228)) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(resolution, [status(thm)], [c_912, c_20])).
% 6.30/2.34  tff(c_4916, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_4909])).
% 6.30/2.34  tff(c_4921, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4916])).
% 6.30/2.34  tff(c_668, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k3_subset_1(A_86, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.30/2.34  tff(c_1596, plain, (![B_127, A_128]: (k4_xboole_0(B_127, A_128)=k3_subset_1(B_127, A_128) | ~r1_tarski(A_128, B_127))), inference(resolution, [status(thm)], [c_32, c_668])).
% 6.30/2.34  tff(c_1905, plain, (![A_141, B_142]: (k4_xboole_0(A_141, k4_xboole_0(A_141, B_142))=k3_subset_1(A_141, k4_xboole_0(A_141, B_142)))), inference(resolution, [status(thm)], [c_12, c_1596])).
% 6.30/2.34  tff(c_1933, plain, (![A_141, B_142]: (r1_tarski(k3_subset_1(A_141, k4_xboole_0(A_141, B_142)), A_141))), inference(superposition, [status(thm), theory('equality')], [c_1905, c_12])).
% 6.30/2.34  tff(c_5379, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4921, c_1933])).
% 6.30/2.34  tff(c_5599, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_924, c_5379])).
% 6.30/2.34  tff(c_5614, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_5599])).
% 6.30/2.34  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.30/2.34  tff(c_5635, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_5614, c_4])).
% 6.30/2.34  tff(c_5651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3555, c_5635])).
% 6.30/2.34  tff(c_5652, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_3045])).
% 6.30/2.34  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.30/2.34  tff(c_966, plain, (![A_103, B_104]: (v4_pre_topc(k2_pre_topc(A_103, B_104), A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.30/2.34  tff(c_973, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_966])).
% 6.30/2.34  tff(c_978, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_973])).
% 6.30/2.34  tff(c_5656, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5652, c_978])).
% 6.30/2.34  tff(c_5658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_5656])).
% 6.30/2.34  tff(c_5659, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 6.30/2.34  tff(c_5801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5659, c_115])).
% 6.30/2.34  tff(c_5802, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 6.30/2.34  tff(c_5871, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5802, c_50])).
% 6.30/2.34  tff(c_6557, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6472, c_5871])).
% 6.30/2.34  tff(c_6902, plain, (![A_308, B_309]: (r1_tarski(k2_tops_1(A_308, B_309), B_309) | ~v4_pre_topc(B_309, A_308) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.30/2.34  tff(c_6909, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_6902])).
% 6.30/2.34  tff(c_6914, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5802, c_6909])).
% 6.30/2.34  tff(c_7144, plain, (![A_317, B_318]: (k7_subset_1(u1_struct_0(A_317), B_318, k2_tops_1(A_317, B_318))=k1_tops_1(A_317, B_318) | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0(A_317))) | ~l1_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.30/2.34  tff(c_7151, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_7144])).
% 6.30/2.34  tff(c_7156, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6472, c_7151])).
% 6.30/2.34  tff(c_6341, plain, (![A_279, B_280]: (k4_xboole_0(A_279, B_280)=k3_subset_1(A_279, B_280) | ~m1_subset_1(B_280, k1_zfmisc_1(A_279)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.30/2.34  tff(c_7272, plain, (![B_320, A_321]: (k4_xboole_0(B_320, A_321)=k3_subset_1(B_320, A_321) | ~r1_tarski(A_321, B_320))), inference(resolution, [status(thm)], [c_32, c_6341])).
% 6.30/2.34  tff(c_7278, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_6914, c_7272])).
% 6.30/2.34  tff(c_7299, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7156, c_7278])).
% 6.30/2.34  tff(c_6185, plain, (![A_271, B_272]: (k3_subset_1(A_271, k3_subset_1(A_271, B_272))=B_272 | ~m1_subset_1(B_272, k1_zfmisc_1(A_271)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.30/2.34  tff(c_6190, plain, (![B_29, A_28]: (k3_subset_1(B_29, k3_subset_1(B_29, A_28))=A_28 | ~r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_32, c_6185])).
% 6.30/2.34  tff(c_7372, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7299, c_6190])).
% 6.30/2.34  tff(c_7376, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6914, c_7372])).
% 6.30/2.34  tff(c_5824, plain, (![A_251, B_252]: (k4_xboole_0(A_251, B_252)=k1_xboole_0 | ~r1_tarski(A_251, B_252))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.30/2.34  tff(c_5836, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_5824])).
% 6.30/2.34  tff(c_7166, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7156, c_5836])).
% 6.30/2.34  tff(c_7629, plain, (![B_337, A_338]: (k4_xboole_0(B_337, A_338)=k3_subset_1(B_337, A_338) | k4_xboole_0(A_338, B_337)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_7272])).
% 6.30/2.34  tff(c_7633, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7166, c_7629])).
% 6.30/2.34  tff(c_7654, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7376, c_7633])).
% 6.30/2.34  tff(c_7656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6557, c_7654])).
% 6.30/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.30/2.34  
% 6.30/2.34  Inference rules
% 6.30/2.34  ----------------------
% 6.30/2.34  #Ref     : 0
% 6.30/2.34  #Sup     : 1869
% 6.30/2.34  #Fact    : 0
% 6.30/2.34  #Define  : 0
% 6.30/2.34  #Split   : 7
% 6.30/2.34  #Chain   : 0
% 6.30/2.34  #Close   : 0
% 6.30/2.34  
% 6.30/2.34  Ordering : KBO
% 6.30/2.34  
% 6.30/2.34  Simplification rules
% 6.30/2.34  ----------------------
% 6.30/2.34  #Subsume      : 28
% 6.30/2.34  #Demod        : 2160
% 6.30/2.34  #Tautology    : 1424
% 6.30/2.34  #SimpNegUnit  : 4
% 6.30/2.34  #BackRed      : 11
% 6.30/2.34  
% 6.30/2.34  #Partial instantiations: 0
% 6.30/2.34  #Strategies tried      : 1
% 6.30/2.34  
% 6.30/2.34  Timing (in seconds)
% 6.30/2.34  ----------------------
% 6.30/2.34  Preprocessing        : 0.34
% 6.30/2.34  Parsing              : 0.18
% 6.30/2.34  CNF conversion       : 0.02
% 6.30/2.34  Main loop            : 1.23
% 6.30/2.34  Inferencing          : 0.38
% 6.30/2.34  Reduction            : 0.56
% 6.30/2.34  Demodulation         : 0.45
% 6.30/2.34  BG Simplification    : 0.04
% 6.30/2.34  Subsumption          : 0.18
% 6.30/2.34  Abstraction          : 0.06
% 6.30/2.34  MUC search           : 0.00
% 6.30/2.34  Cooper               : 0.00
% 6.30/2.34  Total                : 1.62
% 6.30/2.34  Index Insertion      : 0.00
% 6.30/2.34  Index Deletion       : 0.00
% 6.30/2.34  Index Matching       : 0.00
% 6.30/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

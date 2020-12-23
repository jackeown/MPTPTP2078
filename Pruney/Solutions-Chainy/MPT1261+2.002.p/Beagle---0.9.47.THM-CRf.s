%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:11 EST 2020

% Result     : Theorem 6.17s
% Output     : CNFRefutation 6.35s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 666 expanded)
%              Number of leaves         :   42 ( 240 expanded)
%              Depth                    :   16
%              Number of atoms          :  203 (1387 expanded)
%              Number of equality atoms :   87 ( 439 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4692,plain,(
    ! [A_252,B_253,C_254] :
      ( k7_subset_1(A_252,B_253,C_254) = k4_xboole_0(B_253,C_254)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(A_252)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4701,plain,(
    ! [C_254] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_254) = k4_xboole_0('#skF_2',C_254) ),
    inference(resolution,[status(thm)],[c_44,c_4692])).

tff(c_50,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_154,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_829,plain,(
    ! [A_99,B_100,C_101] :
      ( k7_subset_1(A_99,B_100,C_101) = k4_xboole_0(B_100,C_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_839,plain,(
    ! [C_102] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_102) = k4_xboole_0('#skF_2',C_102) ),
    inference(resolution,[status(thm)],[c_44,c_829])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_238,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_56])).

tff(c_845,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_238])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_875,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_10])).

tff(c_885,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_875])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_878,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_8])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_388,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k3_subset_1(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_455,plain,(
    ! [B_79,A_80] :
      ( k4_xboole_0(B_79,A_80) = k3_subset_1(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(resolution,[status(thm)],[c_32,c_388])).

tff(c_473,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_8,c_455])).

tff(c_866,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_473])).

tff(c_882,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_866])).

tff(c_838,plain,(
    ! [C_101] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_101) = k4_xboole_0('#skF_2',C_101) ),
    inference(resolution,[status(thm)],[c_44,c_829])).

tff(c_1478,plain,(
    ! [A_131,B_132] :
      ( k7_subset_1(u1_struct_0(A_131),B_132,k2_tops_1(A_131,B_132)) = k1_tops_1(A_131,B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1488,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1478])).

tff(c_1494,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_882,c_838,c_1488])).

tff(c_307,plain,(
    ! [A_71,B_72] :
      ( k3_subset_1(A_71,k3_subset_1(A_71,B_72)) = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_312,plain,(
    ! [B_31,A_30] :
      ( k3_subset_1(B_31,k3_subset_1(B_31,A_30)) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_32,c_307])).

tff(c_1527,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1494,c_312])).

tff(c_1535,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_1527])).

tff(c_1509,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1494,c_882])).

tff(c_565,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k4_xboole_0(A_87,B_88)) = k3_subset_1(A_87,k4_xboole_0(A_87,B_88)) ),
    inference(resolution,[status(thm)],[c_8,c_455])).

tff(c_583,plain,(
    ! [A_87,B_88] : r1_tarski(k3_subset_1(A_87,k4_xboole_0(A_87,B_88)),A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_8])).

tff(c_1215,plain,(
    ! [A_118,B_119,C_120] :
      ( k4_subset_1(A_118,B_119,C_120) = k2_xboole_0(B_119,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2215,plain,(
    ! [B_152,B_153,A_154] :
      ( k4_subset_1(B_152,B_153,A_154) = k2_xboole_0(B_153,A_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(B_152))
      | ~ r1_tarski(A_154,B_152) ) ),
    inference(resolution,[status(thm)],[c_32,c_1215])).

tff(c_2866,plain,(
    ! [B_174,A_175,A_176] :
      ( k4_subset_1(B_174,A_175,A_176) = k2_xboole_0(A_175,A_176)
      | ~ r1_tarski(A_176,B_174)
      | ~ r1_tarski(A_175,B_174) ) ),
    inference(resolution,[status(thm)],[c_32,c_2215])).

tff(c_3324,plain,(
    ! [A_194,A_195,B_196] :
      ( k4_subset_1(A_194,A_195,k4_xboole_0(A_194,B_196)) = k2_xboole_0(A_195,k4_xboole_0(A_194,B_196))
      | ~ r1_tarski(A_195,A_194) ) ),
    inference(resolution,[status(thm)],[c_8,c_2866])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k3_subset_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( k4_subset_1(A_26,B_27,k3_subset_1(A_26,B_27)) = k2_subset_1(A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_740,plain,(
    ! [A_93,B_94] :
      ( k4_subset_1(A_93,B_94,k3_subset_1(A_93,B_94)) = A_93
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_2393,plain,(
    ! [A_160,B_161] :
      ( k4_subset_1(A_160,k3_subset_1(A_160,B_161),k3_subset_1(A_160,k3_subset_1(A_160,B_161))) = A_160
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160)) ) ),
    inference(resolution,[status(thm)],[c_18,c_740])).

tff(c_3198,plain,(
    ! [B_187,A_188] :
      ( k4_subset_1(B_187,k3_subset_1(B_187,A_188),A_188) = B_187
      | ~ m1_subset_1(A_188,k1_zfmisc_1(B_187))
      | ~ r1_tarski(A_188,B_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_2393])).

tff(c_3219,plain,(
    ! [B_31,A_30] :
      ( k4_subset_1(B_31,k3_subset_1(B_31,A_30),A_30) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_32,c_3198])).

tff(c_3331,plain,(
    ! [A_194,B_196] :
      ( k2_xboole_0(k3_subset_1(A_194,k4_xboole_0(A_194,B_196)),k4_xboole_0(A_194,B_196)) = A_194
      | ~ r1_tarski(k4_xboole_0(A_194,B_196),A_194)
      | ~ r1_tarski(k3_subset_1(A_194,k4_xboole_0(A_194,B_196)),A_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3324,c_3219])).

tff(c_3389,plain,(
    ! [A_197,B_198] : k2_xboole_0(k4_xboole_0(A_197,B_198),k3_subset_1(A_197,k4_xboole_0(A_197,B_198))) = A_197 ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_8,c_2,c_3331])).

tff(c_3404,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_3389])).

tff(c_3446,plain,(
    k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_1535,c_1509,c_3404])).

tff(c_1662,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_10])).

tff(c_1676,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1662])).

tff(c_2313,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1676,c_2])).

tff(c_2325,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_2313])).

tff(c_3462,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3446,c_2325])).

tff(c_1601,plain,(
    ! [A_133,B_134] :
      ( k4_subset_1(u1_struct_0(A_133),B_134,k2_tops_1(A_133,B_134)) = k2_pre_topc(A_133,B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1611,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1601])).

tff(c_1617,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1611])).

tff(c_954,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1(k2_tops_1(A_103,B_104),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k3_subset_1(A_18,k3_subset_1(A_18,B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3831,plain,(
    ! [A_208,B_209] :
      ( k3_subset_1(u1_struct_0(A_208),k3_subset_1(u1_struct_0(A_208),k2_tops_1(A_208,B_209))) = k2_tops_1(A_208,B_209)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(resolution,[status(thm)],[c_954,c_20])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k3_subset_1(A_14,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3582,plain,(
    ! [A_203,B_204] :
      ( k4_xboole_0(u1_struct_0(A_203),k2_tops_1(A_203,B_204)) = k3_subset_1(u1_struct_0(A_203),k2_tops_1(A_203,B_204))
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(resolution,[status(thm)],[c_954,c_16])).

tff(c_3592,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_3582])).

tff(c_3598,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3592])).

tff(c_3648,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3598,c_583])).

tff(c_3837,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3831,c_3648])).

tff(c_3929,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3837])).

tff(c_2233,plain,(
    ! [A_154] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_154) = k2_xboole_0('#skF_2',A_154)
      | ~ r1_tarski(A_154,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2215])).

tff(c_3958,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3929,c_2233])).

tff(c_3972,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3462,c_1617,c_3958])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1066,plain,(
    ! [A_108,B_109] :
      ( v4_pre_topc(k2_pre_topc(A_108,B_109),A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1076,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1066])).

tff(c_1082,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1076])).

tff(c_4026,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_1082])).

tff(c_4028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_4026])).

tff(c_4029,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_4702,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4701,c_4029])).

tff(c_4030,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5223,plain,(
    ! [A_285,B_286] :
      ( r1_tarski(k2_tops_1(A_285,B_286),B_286)
      | ~ v4_pre_topc(B_286,A_285)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5233,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_5223])).

tff(c_5239,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4030,c_5233])).

tff(c_4246,plain,(
    ! [A_230,B_231] :
      ( k4_xboole_0(A_230,B_231) = k3_subset_1(A_230,B_231)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(A_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4253,plain,(
    ! [B_31,A_30] :
      ( k4_xboole_0(B_31,A_30) = k3_subset_1(B_31,A_30)
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_32,c_4246])).

tff(c_5249,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_5239,c_4253])).

tff(c_5369,plain,(
    ! [A_287,B_288] :
      ( k7_subset_1(u1_struct_0(A_287),B_288,k2_tops_1(A_287,B_288)) = k1_tops_1(A_287,B_288)
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ l1_pre_topc(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5379,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_5369])).

tff(c_5385,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5249,c_4701,c_5379])).

tff(c_4149,plain,(
    ! [A_222,B_223] :
      ( k3_subset_1(A_222,k3_subset_1(A_222,B_223)) = B_223
      | ~ m1_subset_1(B_223,k1_zfmisc_1(A_222)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4154,plain,(
    ! [B_31,A_30] :
      ( k3_subset_1(B_31,k3_subset_1(B_31,A_30)) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_32,c_4149])).

tff(c_5400,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5385,c_4154])).

tff(c_5411,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5239,c_5400])).

tff(c_5387,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5385,c_5249])).

tff(c_4323,plain,(
    ! [B_232,A_233] :
      ( k4_xboole_0(B_232,A_233) = k3_subset_1(B_232,A_233)
      | ~ r1_tarski(A_233,B_232) ) ),
    inference(resolution,[status(thm)],[c_32,c_4246])).

tff(c_4341,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_8,c_4323])).

tff(c_5454,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5387,c_4341])).

tff(c_5475,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5387,c_5454])).

tff(c_5607,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5411,c_5475])).

tff(c_5608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4702,c_5607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:48:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.17/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.17/2.29  
% 6.17/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.35/2.30  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 6.35/2.30  
% 6.35/2.30  %Foreground sorts:
% 6.35/2.30  
% 6.35/2.30  
% 6.35/2.30  %Background operators:
% 6.35/2.30  
% 6.35/2.30  
% 6.35/2.30  %Foreground operators:
% 6.35/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.35/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.35/2.30  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.35/2.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.35/2.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.35/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.35/2.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.35/2.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.35/2.30  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.35/2.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.35/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.35/2.30  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.35/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.35/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.35/2.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.35/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.35/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.35/2.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.35/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.35/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.35/2.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.35/2.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.35/2.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.35/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.35/2.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.35/2.30  
% 6.35/2.32  tff(f_122, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 6.35/2.32  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.35/2.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.35/2.32  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.35/2.32  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.35/2.32  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.35/2.32  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.35/2.32  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 6.35/2.32  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.35/2.32  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.35/2.32  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.35/2.32  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.35/2.32  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 6.35/2.32  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 6.35/2.32  tff(f_79, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.35/2.32  tff(f_87, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 6.35/2.32  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 6.35/2.32  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.35/2.32  tff(c_4692, plain, (![A_252, B_253, C_254]: (k7_subset_1(A_252, B_253, C_254)=k4_xboole_0(B_253, C_254) | ~m1_subset_1(B_253, k1_zfmisc_1(A_252)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.35/2.32  tff(c_4701, plain, (![C_254]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_254)=k4_xboole_0('#skF_2', C_254))), inference(resolution, [status(thm)], [c_44, c_4692])).
% 6.35/2.32  tff(c_50, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.35/2.32  tff(c_154, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 6.35/2.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.35/2.32  tff(c_829, plain, (![A_99, B_100, C_101]: (k7_subset_1(A_99, B_100, C_101)=k4_xboole_0(B_100, C_101) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.35/2.32  tff(c_839, plain, (![C_102]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_102)=k4_xboole_0('#skF_2', C_102))), inference(resolution, [status(thm)], [c_44, c_829])).
% 6.35/2.32  tff(c_56, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.35/2.32  tff(c_238, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_154, c_56])).
% 6.35/2.32  tff(c_845, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_839, c_238])).
% 6.35/2.32  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.35/2.32  tff(c_875, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_845, c_10])).
% 6.35/2.32  tff(c_885, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_875])).
% 6.35/2.32  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.35/2.32  tff(c_878, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_845, c_8])).
% 6.35/2.32  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.35/2.32  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.35/2.32  tff(c_388, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k3_subset_1(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.35/2.32  tff(c_455, plain, (![B_79, A_80]: (k4_xboole_0(B_79, A_80)=k3_subset_1(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(resolution, [status(thm)], [c_32, c_388])).
% 6.35/2.32  tff(c_473, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_subset_1(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_8, c_455])).
% 6.35/2.32  tff(c_866, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_845, c_473])).
% 6.35/2.32  tff(c_882, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_845, c_866])).
% 6.35/2.32  tff(c_838, plain, (![C_101]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_101)=k4_xboole_0('#skF_2', C_101))), inference(resolution, [status(thm)], [c_44, c_829])).
% 6.35/2.32  tff(c_1478, plain, (![A_131, B_132]: (k7_subset_1(u1_struct_0(A_131), B_132, k2_tops_1(A_131, B_132))=k1_tops_1(A_131, B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.35/2.32  tff(c_1488, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1478])).
% 6.35/2.32  tff(c_1494, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_882, c_838, c_1488])).
% 6.35/2.32  tff(c_307, plain, (![A_71, B_72]: (k3_subset_1(A_71, k3_subset_1(A_71, B_72))=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.35/2.32  tff(c_312, plain, (![B_31, A_30]: (k3_subset_1(B_31, k3_subset_1(B_31, A_30))=A_30 | ~r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_32, c_307])).
% 6.35/2.32  tff(c_1527, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1494, c_312])).
% 6.35/2.32  tff(c_1535, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_878, c_1527])).
% 6.35/2.32  tff(c_1509, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1494, c_882])).
% 6.35/2.32  tff(c_565, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k4_xboole_0(A_87, B_88))=k3_subset_1(A_87, k4_xboole_0(A_87, B_88)))), inference(resolution, [status(thm)], [c_8, c_455])).
% 6.35/2.32  tff(c_583, plain, (![A_87, B_88]: (r1_tarski(k3_subset_1(A_87, k4_xboole_0(A_87, B_88)), A_87))), inference(superposition, [status(thm), theory('equality')], [c_565, c_8])).
% 6.35/2.32  tff(c_1215, plain, (![A_118, B_119, C_120]: (k4_subset_1(A_118, B_119, C_120)=k2_xboole_0(B_119, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(A_118)) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.35/2.32  tff(c_2215, plain, (![B_152, B_153, A_154]: (k4_subset_1(B_152, B_153, A_154)=k2_xboole_0(B_153, A_154) | ~m1_subset_1(B_153, k1_zfmisc_1(B_152)) | ~r1_tarski(A_154, B_152))), inference(resolution, [status(thm)], [c_32, c_1215])).
% 6.35/2.32  tff(c_2866, plain, (![B_174, A_175, A_176]: (k4_subset_1(B_174, A_175, A_176)=k2_xboole_0(A_175, A_176) | ~r1_tarski(A_176, B_174) | ~r1_tarski(A_175, B_174))), inference(resolution, [status(thm)], [c_32, c_2215])).
% 6.35/2.32  tff(c_3324, plain, (![A_194, A_195, B_196]: (k4_subset_1(A_194, A_195, k4_xboole_0(A_194, B_196))=k2_xboole_0(A_195, k4_xboole_0(A_194, B_196)) | ~r1_tarski(A_195, A_194))), inference(resolution, [status(thm)], [c_8, c_2866])).
% 6.35/2.32  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(k3_subset_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.35/2.32  tff(c_14, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.35/2.32  tff(c_26, plain, (![A_26, B_27]: (k4_subset_1(A_26, B_27, k3_subset_1(A_26, B_27))=k2_subset_1(A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.35/2.32  tff(c_740, plain, (![A_93, B_94]: (k4_subset_1(A_93, B_94, k3_subset_1(A_93, B_94))=A_93 | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 6.35/2.32  tff(c_2393, plain, (![A_160, B_161]: (k4_subset_1(A_160, k3_subset_1(A_160, B_161), k3_subset_1(A_160, k3_subset_1(A_160, B_161)))=A_160 | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)))), inference(resolution, [status(thm)], [c_18, c_740])).
% 6.35/2.32  tff(c_3198, plain, (![B_187, A_188]: (k4_subset_1(B_187, k3_subset_1(B_187, A_188), A_188)=B_187 | ~m1_subset_1(A_188, k1_zfmisc_1(B_187)) | ~r1_tarski(A_188, B_187))), inference(superposition, [status(thm), theory('equality')], [c_312, c_2393])).
% 6.35/2.32  tff(c_3219, plain, (![B_31, A_30]: (k4_subset_1(B_31, k3_subset_1(B_31, A_30), A_30)=B_31 | ~r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_32, c_3198])).
% 6.35/2.32  tff(c_3331, plain, (![A_194, B_196]: (k2_xboole_0(k3_subset_1(A_194, k4_xboole_0(A_194, B_196)), k4_xboole_0(A_194, B_196))=A_194 | ~r1_tarski(k4_xboole_0(A_194, B_196), A_194) | ~r1_tarski(k3_subset_1(A_194, k4_xboole_0(A_194, B_196)), A_194))), inference(superposition, [status(thm), theory('equality')], [c_3324, c_3219])).
% 6.35/2.32  tff(c_3389, plain, (![A_197, B_198]: (k2_xboole_0(k4_xboole_0(A_197, B_198), k3_subset_1(A_197, k4_xboole_0(A_197, B_198)))=A_197)), inference(demodulation, [status(thm), theory('equality')], [c_583, c_8, c_2, c_3331])).
% 6.35/2.32  tff(c_3404, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1509, c_3389])).
% 6.35/2.32  tff(c_3446, plain, (k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_885, c_1535, c_1509, c_3404])).
% 6.35/2.32  tff(c_1662, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1509, c_10])).
% 6.35/2.32  tff(c_1676, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1662])).
% 6.35/2.32  tff(c_2313, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1676, c_2])).
% 6.35/2.32  tff(c_2325, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_2313])).
% 6.35/2.32  tff(c_3462, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3446, c_2325])).
% 6.35/2.32  tff(c_1601, plain, (![A_133, B_134]: (k4_subset_1(u1_struct_0(A_133), B_134, k2_tops_1(A_133, B_134))=k2_pre_topc(A_133, B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.35/2.32  tff(c_1611, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1601])).
% 6.35/2.32  tff(c_1617, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1611])).
% 6.35/2.32  tff(c_954, plain, (![A_103, B_104]: (m1_subset_1(k2_tops_1(A_103, B_104), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.35/2.32  tff(c_20, plain, (![A_18, B_19]: (k3_subset_1(A_18, k3_subset_1(A_18, B_19))=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.35/2.32  tff(c_3831, plain, (![A_208, B_209]: (k3_subset_1(u1_struct_0(A_208), k3_subset_1(u1_struct_0(A_208), k2_tops_1(A_208, B_209)))=k2_tops_1(A_208, B_209) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(resolution, [status(thm)], [c_954, c_20])).
% 6.35/2.32  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k3_subset_1(A_14, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.35/2.32  tff(c_3582, plain, (![A_203, B_204]: (k4_xboole_0(u1_struct_0(A_203), k2_tops_1(A_203, B_204))=k3_subset_1(u1_struct_0(A_203), k2_tops_1(A_203, B_204)) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(resolution, [status(thm)], [c_954, c_16])).
% 6.35/2.32  tff(c_3592, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_3582])).
% 6.35/2.32  tff(c_3598, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3592])).
% 6.35/2.32  tff(c_3648, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3598, c_583])).
% 6.35/2.32  tff(c_3837, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3831, c_3648])).
% 6.35/2.32  tff(c_3929, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3837])).
% 6.35/2.32  tff(c_2233, plain, (![A_154]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_154)=k2_xboole_0('#skF_2', A_154) | ~r1_tarski(A_154, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_44, c_2215])).
% 6.35/2.32  tff(c_3958, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3929, c_2233])).
% 6.35/2.32  tff(c_3972, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3462, c_1617, c_3958])).
% 6.35/2.32  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.35/2.32  tff(c_1066, plain, (![A_108, B_109]: (v4_pre_topc(k2_pre_topc(A_108, B_109), A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.35/2.32  tff(c_1076, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1066])).
% 6.35/2.32  tff(c_1082, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1076])).
% 6.35/2.32  tff(c_4026, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_1082])).
% 6.35/2.32  tff(c_4028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_4026])).
% 6.35/2.32  tff(c_4029, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 6.35/2.32  tff(c_4702, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4701, c_4029])).
% 6.35/2.32  tff(c_4030, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 6.35/2.32  tff(c_5223, plain, (![A_285, B_286]: (r1_tarski(k2_tops_1(A_285, B_286), B_286) | ~v4_pre_topc(B_286, A_285) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(A_285))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.35/2.32  tff(c_5233, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_5223])).
% 6.35/2.32  tff(c_5239, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4030, c_5233])).
% 6.35/2.32  tff(c_4246, plain, (![A_230, B_231]: (k4_xboole_0(A_230, B_231)=k3_subset_1(A_230, B_231) | ~m1_subset_1(B_231, k1_zfmisc_1(A_230)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.35/2.32  tff(c_4253, plain, (![B_31, A_30]: (k4_xboole_0(B_31, A_30)=k3_subset_1(B_31, A_30) | ~r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_32, c_4246])).
% 6.35/2.32  tff(c_5249, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_5239, c_4253])).
% 6.35/2.32  tff(c_5369, plain, (![A_287, B_288]: (k7_subset_1(u1_struct_0(A_287), B_288, k2_tops_1(A_287, B_288))=k1_tops_1(A_287, B_288) | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0(A_287))) | ~l1_pre_topc(A_287))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.35/2.32  tff(c_5379, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_5369])).
% 6.35/2.32  tff(c_5385, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5249, c_4701, c_5379])).
% 6.35/2.32  tff(c_4149, plain, (![A_222, B_223]: (k3_subset_1(A_222, k3_subset_1(A_222, B_223))=B_223 | ~m1_subset_1(B_223, k1_zfmisc_1(A_222)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.35/2.32  tff(c_4154, plain, (![B_31, A_30]: (k3_subset_1(B_31, k3_subset_1(B_31, A_30))=A_30 | ~r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_32, c_4149])).
% 6.35/2.32  tff(c_5400, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5385, c_4154])).
% 6.35/2.32  tff(c_5411, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5239, c_5400])).
% 6.35/2.32  tff(c_5387, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5385, c_5249])).
% 6.35/2.32  tff(c_4323, plain, (![B_232, A_233]: (k4_xboole_0(B_232, A_233)=k3_subset_1(B_232, A_233) | ~r1_tarski(A_233, B_232))), inference(resolution, [status(thm)], [c_32, c_4246])).
% 6.35/2.32  tff(c_4341, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_subset_1(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_8, c_4323])).
% 6.35/2.32  tff(c_5454, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5387, c_4341])).
% 6.35/2.32  tff(c_5475, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5387, c_5454])).
% 6.35/2.32  tff(c_5607, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5411, c_5475])).
% 6.35/2.32  tff(c_5608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4702, c_5607])).
% 6.35/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.35/2.32  
% 6.35/2.32  Inference rules
% 6.35/2.32  ----------------------
% 6.35/2.32  #Ref     : 0
% 6.35/2.32  #Sup     : 1426
% 6.35/2.32  #Fact    : 0
% 6.35/2.32  #Define  : 0
% 6.35/2.32  #Split   : 2
% 6.35/2.32  #Chain   : 0
% 6.35/2.32  #Close   : 0
% 6.35/2.32  
% 6.35/2.32  Ordering : KBO
% 6.35/2.32  
% 6.35/2.32  Simplification rules
% 6.35/2.32  ----------------------
% 6.35/2.32  #Subsume      : 30
% 6.35/2.32  #Demod        : 1047
% 6.35/2.32  #Tautology    : 801
% 6.35/2.32  #SimpNegUnit  : 3
% 6.35/2.32  #BackRed      : 28
% 6.35/2.32  
% 6.35/2.32  #Partial instantiations: 0
% 6.35/2.32  #Strategies tried      : 1
% 6.35/2.32  
% 6.35/2.32  Timing (in seconds)
% 6.35/2.32  ----------------------
% 6.35/2.33  Preprocessing        : 0.33
% 6.35/2.33  Parsing              : 0.18
% 6.35/2.33  CNF conversion       : 0.02
% 6.35/2.33  Main loop            : 1.21
% 6.35/2.33  Inferencing          : 0.38
% 6.35/2.33  Reduction            : 0.49
% 6.35/2.33  Demodulation         : 0.39
% 6.35/2.33  BG Simplification    : 0.05
% 6.35/2.33  Subsumption          : 0.20
% 6.35/2.33  Abstraction          : 0.06
% 6.35/2.33  MUC search           : 0.00
% 6.35/2.33  Cooper               : 0.00
% 6.35/2.33  Total                : 1.60
% 6.35/2.33  Index Insertion      : 0.00
% 6.35/2.33  Index Deletion       : 0.00
% 6.35/2.33  Index Matching       : 0.00
% 6.35/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

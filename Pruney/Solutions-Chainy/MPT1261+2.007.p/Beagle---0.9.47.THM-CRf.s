%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:12 EST 2020

% Result     : Theorem 13.69s
% Output     : CNFRefutation 13.93s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 397 expanded)
%              Number of leaves         :   53 ( 153 expanded)
%              Depth                    :   13
%              Number of atoms          :  205 ( 765 expanded)
%              Number of equality atoms :   91 ( 246 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_175,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_120,axiom,(
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

tff(f_147,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_101,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_156,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_91,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_79,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_24545,plain,(
    ! [A_600,B_601,C_602] :
      ( k7_subset_1(A_600,B_601,C_602) = k4_xboole_0(B_601,C_602)
      | ~ m1_subset_1(B_601,k1_zfmisc_1(A_600)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24567,plain,(
    ! [C_602] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_602) = k4_xboole_0('#skF_2',C_602) ),
    inference(resolution,[status(thm)],[c_76,c_24545])).

tff(c_88,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_114,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_82,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_207,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_78,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_80,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_4585,plain,(
    ! [B_256,A_257] :
      ( v4_pre_topc(B_256,A_257)
      | k2_pre_topc(A_257,B_256) != B_256
      | ~ v2_pre_topc(A_257)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ l1_pre_topc(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4614,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_4585])).

tff(c_4626,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_80,c_4614])).

tff(c_4627,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_4626])).

tff(c_5361,plain,(
    ! [A_267,B_268] :
      ( k4_subset_1(u1_struct_0(A_267),B_268,k2_tops_1(A_267,B_268)) = k2_pre_topc(A_267,B_268)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_5382,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_5361])).

tff(c_5394,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5382])).

tff(c_16,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_209,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,B_98) = k1_xboole_0
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_230,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_209])).

tff(c_453,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k4_xboole_0(B_113,A_112)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_471,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_453])).

tff(c_480,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_471])).

tff(c_2382,plain,(
    ! [A_189,B_190,C_191] :
      ( k7_subset_1(A_189,B_190,C_191) = k4_xboole_0(B_190,C_191)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(A_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2447,plain,(
    ! [C_195] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_195) = k4_xboole_0('#skF_2',C_195) ),
    inference(resolution,[status(thm)],[c_76,c_2382])).

tff(c_2453,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2447,c_114])).

tff(c_24,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_227,plain,(
    ! [A_16,B_17] : k4_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_209])).

tff(c_4796,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2453,c_227])).

tff(c_30,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4852,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4796,c_30])).

tff(c_4876,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_4852])).

tff(c_32,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_192,plain,(
    ! [A_93,B_94] : k3_tarski(k2_tarski(A_93,B_94)) = k2_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2156,plain,(
    ! [B_181,A_182] : k3_tarski(k2_tarski(B_181,A_182)) = k2_xboole_0(A_182,B_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_192])).

tff(c_34,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2228,plain,(
    ! [B_187,A_188] : k2_xboole_0(B_187,A_188) = k2_xboole_0(A_188,B_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_34])).

tff(c_331,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(A_106,B_107)
      | ~ m1_subset_1(A_106,k1_zfmisc_1(B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_349,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_331])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_353,plain,(
    k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_349,c_10])).

tff(c_462,plain,(
    k5_xboole_0(u1_struct_0('#skF_1'),k1_xboole_0) = k2_xboole_0(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_453])).

tff(c_537,plain,(
    k2_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_462])).

tff(c_2287,plain,(
    k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2228,c_537])).

tff(c_277,plain,(
    ! [A_102,B_103] : k1_setfam_1(k2_tarski(A_102,B_103)) = k3_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_514,plain,(
    ! [B_116,A_117] : k1_setfam_1(k2_tarski(B_116,A_117)) = k3_xboole_0(A_117,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_277])).

tff(c_54,plain,(
    ! [A_48,B_49] : k1_setfam_1(k2_tarski(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_546,plain,(
    ! [B_118,A_119] : k3_xboole_0(B_118,A_119) = k3_xboole_0(A_119,B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_54])).

tff(c_374,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(A_108,B_109) = A_108
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_398,plain,(
    ! [A_15] : k3_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_374])).

tff(c_562,plain,(
    ! [B_118] : k3_xboole_0(B_118,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_398])).

tff(c_659,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k3_xboole_0(A_121,B_122)) = k4_xboole_0(A_121,B_122) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_668,plain,(
    ! [B_118] : k5_xboole_0(B_118,k1_xboole_0) = k4_xboole_0(B_118,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_659])).

tff(c_686,plain,(
    ! [B_118] : k4_xboole_0(B_118,k1_xboole_0) = B_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_668])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_873,plain,(
    ! [A_131,C_132,B_133] :
      ( r1_tarski(A_131,C_132)
      | ~ r1_tarski(B_133,C_132)
      | ~ r1_tarski(A_131,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_895,plain,(
    ! [A_134,A_135] :
      ( r1_tarski(A_134,A_135)
      | ~ r1_tarski(A_134,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_873])).

tff(c_901,plain,(
    ! [A_3,A_135] :
      ( r1_tarski(A_3,A_135)
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_895])).

tff(c_926,plain,(
    ! [A_135] : r1_tarski(k1_xboole_0,A_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_901])).

tff(c_1185,plain,(
    ! [A_146,B_147,C_148] :
      ( r1_tarski(A_146,k2_xboole_0(B_147,C_148))
      | ~ r1_tarski(k4_xboole_0(A_146,B_147),C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1205,plain,(
    ! [A_16,B_17,C_148] :
      ( r1_tarski(k4_xboole_0(A_16,B_17),k2_xboole_0(A_16,C_148))
      | ~ r1_tarski(k1_xboole_0,C_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_1185])).

tff(c_3294,plain,(
    ! [A_220,B_221,C_222] : r1_tarski(k4_xboole_0(A_220,B_221),k2_xboole_0(A_220,C_222)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_1205])).

tff(c_3319,plain,(
    ! [B_221] : r1_tarski(k4_xboole_0('#skF_2',B_221),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2287,c_3294])).

tff(c_4778,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2453,c_3319])).

tff(c_58,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(A_50,k1_zfmisc_1(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3447,plain,(
    ! [A_224,B_225,C_226] :
      ( k4_subset_1(A_224,B_225,C_226) = k2_xboole_0(B_225,C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(A_224))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(A_224)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_21419,plain,(
    ! [B_461,B_462,A_463] :
      ( k4_subset_1(B_461,B_462,A_463) = k2_xboole_0(B_462,A_463)
      | ~ m1_subset_1(B_462,k1_zfmisc_1(B_461))
      | ~ r1_tarski(A_463,B_461) ) ),
    inference(resolution,[status(thm)],[c_58,c_3447])).

tff(c_21579,plain,(
    ! [A_466] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_466) = k2_xboole_0('#skF_2',A_466)
      | ~ r1_tarski(A_466,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_76,c_21419])).

tff(c_21663,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4778,c_21579])).

tff(c_21737,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5394,c_4876,c_21663])).

tff(c_21739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4627,c_21737])).

tff(c_21740,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_22088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_21740])).

tff(c_22089,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_22169,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22089,c_82])).

tff(c_24576,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24567,c_22169])).

tff(c_25716,plain,(
    ! [A_641,B_642] :
      ( r1_tarski(k2_tops_1(A_641,B_642),B_642)
      | ~ v4_pre_topc(B_642,A_641)
      | ~ m1_subset_1(B_642,k1_zfmisc_1(u1_struct_0(A_641)))
      | ~ l1_pre_topc(A_641) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_25737,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_25716])).

tff(c_25749,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_22089,c_25737])).

tff(c_27649,plain,(
    ! [A_686,B_687] :
      ( k7_subset_1(u1_struct_0(A_686),B_687,k2_tops_1(A_686,B_687)) = k1_tops_1(A_686,B_687)
      | ~ m1_subset_1(B_687,k1_zfmisc_1(u1_struct_0(A_686)))
      | ~ l1_pre_topc(A_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_27672,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_27649])).

tff(c_27688,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_24567,c_27672])).

tff(c_23215,plain,(
    ! [A_555,B_556] :
      ( k4_xboole_0(A_555,B_556) = k3_subset_1(A_555,B_556)
      | ~ m1_subset_1(B_556,k1_zfmisc_1(A_555)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_31409,plain,(
    ! [B_748,A_749] :
      ( k4_xboole_0(B_748,A_749) = k3_subset_1(B_748,A_749)
      | ~ r1_tarski(A_749,B_748) ) ),
    inference(resolution,[status(thm)],[c_58,c_23215])).

tff(c_31499,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_25749,c_31409])).

tff(c_31614,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27688,c_31499])).

tff(c_24082,plain,(
    ! [A_584,B_585] :
      ( k3_subset_1(A_584,k3_subset_1(A_584,B_585)) = B_585
      | ~ m1_subset_1(B_585,k1_zfmisc_1(A_584)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24101,plain,(
    ! [B_51,A_50] :
      ( k3_subset_1(B_51,k3_subset_1(B_51,A_50)) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_58,c_24082])).

tff(c_34115,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_31614,c_24101])).

tff(c_34123,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25749,c_34115])).

tff(c_48,plain,(
    ! [A_41,B_42] : k6_subset_1(A_41,B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    ! [A_34,B_35] : m1_subset_1(k6_subset_1(A_34,B_35),k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,(
    ! [A_34,B_35] : m1_subset_1(k4_xboole_0(A_34,B_35),k1_zfmisc_1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42])).

tff(c_33434,plain,(
    ! [A_780,B_781] : k4_xboole_0(A_780,k4_xboole_0(A_780,B_781)) = k3_subset_1(A_780,k4_xboole_0(A_780,B_781)) ),
    inference(resolution,[status(thm)],[c_89,c_23215])).

tff(c_36338,plain,(
    ! [A_807,B_808] : m1_subset_1(k3_subset_1(A_807,k4_xboole_0(A_807,B_808)),k1_zfmisc_1(A_807)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33434,c_89])).

tff(c_36414,plain,(
    m1_subset_1(k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27688,c_36338])).

tff(c_39577,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34123,c_36414])).

tff(c_23741,plain,(
    ! [A_575,B_576] :
      ( m1_subset_1(k3_subset_1(A_575,B_576),k1_zfmisc_1(A_575))
      | ~ m1_subset_1(B_576,k1_zfmisc_1(A_575)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k3_subset_1(A_30,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_45212,plain,(
    ! [A_885,B_886] :
      ( k4_xboole_0(A_885,k3_subset_1(A_885,B_886)) = k3_subset_1(A_885,k3_subset_1(A_885,B_886))
      | ~ m1_subset_1(B_886,k1_zfmisc_1(A_885)) ) ),
    inference(resolution,[status(thm)],[c_23741,c_38])).

tff(c_45214,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_39577,c_45212])).

tff(c_45238,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34123,c_31614,c_31614,c_45214])).

tff(c_45240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24576,c_45238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.69/6.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.69/6.39  
% 13.69/6.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.69/6.39  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 13.69/6.39  
% 13.69/6.39  %Foreground sorts:
% 13.69/6.39  
% 13.69/6.39  
% 13.69/6.39  %Background operators:
% 13.69/6.39  
% 13.69/6.39  
% 13.69/6.39  %Foreground operators:
% 13.69/6.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.69/6.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.69/6.39  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 13.69/6.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.69/6.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.69/6.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.69/6.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.69/6.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.69/6.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.69/6.39  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.69/6.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 13.69/6.39  tff('#skF_2', type, '#skF_2': $i).
% 13.69/6.39  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 13.69/6.39  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.69/6.39  tff('#skF_1', type, '#skF_1': $i).
% 13.69/6.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.69/6.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 13.69/6.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.69/6.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.69/6.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.69/6.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.69/6.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.69/6.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.69/6.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.69/6.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 13.69/6.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 13.69/6.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.69/6.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.69/6.39  
% 13.93/6.42  tff(f_175, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 13.93/6.42  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 13.93/6.42  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 13.93/6.42  tff(f_147, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 13.93/6.42  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.93/6.42  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.93/6.42  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.93/6.42  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 13.93/6.42  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.93/6.42  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.93/6.42  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.93/6.42  tff(f_105, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.93/6.42  tff(f_101, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 13.93/6.42  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.93/6.42  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.93/6.42  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.93/6.42  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 13.93/6.42  tff(f_89, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 13.93/6.42  tff(f_156, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 13.93/6.42  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 13.93/6.42  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 13.93/6.42  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 13.93/6.42  tff(f_91, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 13.93/6.42  tff(f_79, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 13.93/6.42  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 13.93/6.42  tff(c_76, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 13.93/6.42  tff(c_24545, plain, (![A_600, B_601, C_602]: (k7_subset_1(A_600, B_601, C_602)=k4_xboole_0(B_601, C_602) | ~m1_subset_1(B_601, k1_zfmisc_1(A_600)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.93/6.42  tff(c_24567, plain, (![C_602]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_602)=k4_xboole_0('#skF_2', C_602))), inference(resolution, [status(thm)], [c_76, c_24545])).
% 13.93/6.42  tff(c_88, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 13.93/6.42  tff(c_114, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_88])).
% 13.93/6.42  tff(c_82, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 13.93/6.42  tff(c_207, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_82])).
% 13.93/6.42  tff(c_78, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 13.93/6.42  tff(c_80, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 13.93/6.42  tff(c_4585, plain, (![B_256, A_257]: (v4_pre_topc(B_256, A_257) | k2_pre_topc(A_257, B_256)!=B_256 | ~v2_pre_topc(A_257) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_257))) | ~l1_pre_topc(A_257))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.93/6.42  tff(c_4614, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_4585])).
% 13.93/6.42  tff(c_4626, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_80, c_4614])).
% 13.93/6.42  tff(c_4627, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_207, c_4626])).
% 13.93/6.42  tff(c_5361, plain, (![A_267, B_268]: (k4_subset_1(u1_struct_0(A_267), B_268, k2_tops_1(A_267, B_268))=k2_pre_topc(A_267, B_268) | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267))), inference(cnfTransformation, [status(thm)], [f_147])).
% 13.93/6.42  tff(c_5382, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_5361])).
% 13.93/6.42  tff(c_5394, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5382])).
% 13.93/6.42  tff(c_16, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.93/6.42  tff(c_22, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.93/6.42  tff(c_209, plain, (![A_97, B_98]: (k4_xboole_0(A_97, B_98)=k1_xboole_0 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.93/6.42  tff(c_230, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_209])).
% 13.93/6.42  tff(c_453, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k4_xboole_0(B_113, A_112))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.93/6.42  tff(c_471, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_230, c_453])).
% 13.93/6.42  tff(c_480, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_471])).
% 13.93/6.42  tff(c_2382, plain, (![A_189, B_190, C_191]: (k7_subset_1(A_189, B_190, C_191)=k4_xboole_0(B_190, C_191) | ~m1_subset_1(B_190, k1_zfmisc_1(A_189)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.93/6.42  tff(c_2447, plain, (![C_195]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_195)=k4_xboole_0('#skF_2', C_195))), inference(resolution, [status(thm)], [c_76, c_2382])).
% 13.93/6.42  tff(c_2453, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2447, c_114])).
% 13.93/6.42  tff(c_24, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.93/6.42  tff(c_227, plain, (![A_16, B_17]: (k4_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_209])).
% 13.93/6.42  tff(c_4796, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2453, c_227])).
% 13.93/6.42  tff(c_30, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.93/6.42  tff(c_4852, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4796, c_30])).
% 13.93/6.42  tff(c_4876, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_4852])).
% 13.93/6.42  tff(c_32, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.93/6.42  tff(c_192, plain, (![A_93, B_94]: (k3_tarski(k2_tarski(A_93, B_94))=k2_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.93/6.42  tff(c_2156, plain, (![B_181, A_182]: (k3_tarski(k2_tarski(B_181, A_182))=k2_xboole_0(A_182, B_181))), inference(superposition, [status(thm), theory('equality')], [c_32, c_192])).
% 13.93/6.42  tff(c_34, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.93/6.42  tff(c_2228, plain, (![B_187, A_188]: (k2_xboole_0(B_187, A_188)=k2_xboole_0(A_188, B_187))), inference(superposition, [status(thm), theory('equality')], [c_2156, c_34])).
% 13.93/6.42  tff(c_331, plain, (![A_106, B_107]: (r1_tarski(A_106, B_107) | ~m1_subset_1(A_106, k1_zfmisc_1(B_107)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.93/6.42  tff(c_349, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_76, c_331])).
% 13.93/6.42  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.93/6.42  tff(c_353, plain, (k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_349, c_10])).
% 13.93/6.42  tff(c_462, plain, (k5_xboole_0(u1_struct_0('#skF_1'), k1_xboole_0)=k2_xboole_0(u1_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_353, c_453])).
% 13.93/6.42  tff(c_537, plain, (k2_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_462])).
% 13.93/6.42  tff(c_2287, plain, (k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))=u1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2228, c_537])).
% 13.93/6.42  tff(c_277, plain, (![A_102, B_103]: (k1_setfam_1(k2_tarski(A_102, B_103))=k3_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.93/6.42  tff(c_514, plain, (![B_116, A_117]: (k1_setfam_1(k2_tarski(B_116, A_117))=k3_xboole_0(A_117, B_116))), inference(superposition, [status(thm), theory('equality')], [c_32, c_277])).
% 13.93/6.42  tff(c_54, plain, (![A_48, B_49]: (k1_setfam_1(k2_tarski(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.93/6.42  tff(c_546, plain, (![B_118, A_119]: (k3_xboole_0(B_118, A_119)=k3_xboole_0(A_119, B_118))), inference(superposition, [status(thm), theory('equality')], [c_514, c_54])).
% 13.93/6.42  tff(c_374, plain, (![A_108, B_109]: (k3_xboole_0(A_108, B_109)=A_108 | ~r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.93/6.42  tff(c_398, plain, (![A_15]: (k3_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_374])).
% 13.93/6.42  tff(c_562, plain, (![B_118]: (k3_xboole_0(B_118, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_546, c_398])).
% 13.93/6.42  tff(c_659, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k3_xboole_0(A_121, B_122))=k4_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.93/6.42  tff(c_668, plain, (![B_118]: (k5_xboole_0(B_118, k1_xboole_0)=k4_xboole_0(B_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_562, c_659])).
% 13.93/6.42  tff(c_686, plain, (![B_118]: (k4_xboole_0(B_118, k1_xboole_0)=B_118)), inference(demodulation, [status(thm), theory('equality')], [c_480, c_668])).
% 13.93/6.42  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.93/6.42  tff(c_873, plain, (![A_131, C_132, B_133]: (r1_tarski(A_131, C_132) | ~r1_tarski(B_133, C_132) | ~r1_tarski(A_131, B_133))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.93/6.42  tff(c_895, plain, (![A_134, A_135]: (r1_tarski(A_134, A_135) | ~r1_tarski(A_134, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_873])).
% 13.93/6.42  tff(c_901, plain, (![A_3, A_135]: (r1_tarski(A_3, A_135) | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_895])).
% 13.93/6.42  tff(c_926, plain, (![A_135]: (r1_tarski(k1_xboole_0, A_135))), inference(demodulation, [status(thm), theory('equality')], [c_686, c_901])).
% 13.93/6.42  tff(c_1185, plain, (![A_146, B_147, C_148]: (r1_tarski(A_146, k2_xboole_0(B_147, C_148)) | ~r1_tarski(k4_xboole_0(A_146, B_147), C_148))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.93/6.42  tff(c_1205, plain, (![A_16, B_17, C_148]: (r1_tarski(k4_xboole_0(A_16, B_17), k2_xboole_0(A_16, C_148)) | ~r1_tarski(k1_xboole_0, C_148))), inference(superposition, [status(thm), theory('equality')], [c_227, c_1185])).
% 13.93/6.42  tff(c_3294, plain, (![A_220, B_221, C_222]: (r1_tarski(k4_xboole_0(A_220, B_221), k2_xboole_0(A_220, C_222)))), inference(demodulation, [status(thm), theory('equality')], [c_926, c_1205])).
% 13.93/6.42  tff(c_3319, plain, (![B_221]: (r1_tarski(k4_xboole_0('#skF_2', B_221), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2287, c_3294])).
% 13.93/6.42  tff(c_4778, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2453, c_3319])).
% 13.93/6.42  tff(c_58, plain, (![A_50, B_51]: (m1_subset_1(A_50, k1_zfmisc_1(B_51)) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.93/6.42  tff(c_3447, plain, (![A_224, B_225, C_226]: (k4_subset_1(A_224, B_225, C_226)=k2_xboole_0(B_225, C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(A_224)) | ~m1_subset_1(B_225, k1_zfmisc_1(A_224)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.93/6.42  tff(c_21419, plain, (![B_461, B_462, A_463]: (k4_subset_1(B_461, B_462, A_463)=k2_xboole_0(B_462, A_463) | ~m1_subset_1(B_462, k1_zfmisc_1(B_461)) | ~r1_tarski(A_463, B_461))), inference(resolution, [status(thm)], [c_58, c_3447])).
% 13.93/6.42  tff(c_21579, plain, (![A_466]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_466)=k2_xboole_0('#skF_2', A_466) | ~r1_tarski(A_466, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_76, c_21419])).
% 13.93/6.42  tff(c_21663, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4778, c_21579])).
% 13.93/6.42  tff(c_21737, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5394, c_4876, c_21663])).
% 13.93/6.42  tff(c_21739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4627, c_21737])).
% 13.93/6.42  tff(c_21740, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_82])).
% 13.93/6.42  tff(c_22088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_21740])).
% 13.93/6.42  tff(c_22089, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_88])).
% 13.93/6.42  tff(c_22169, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22089, c_82])).
% 13.93/6.42  tff(c_24576, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24567, c_22169])).
% 13.93/6.42  tff(c_25716, plain, (![A_641, B_642]: (r1_tarski(k2_tops_1(A_641, B_642), B_642) | ~v4_pre_topc(B_642, A_641) | ~m1_subset_1(B_642, k1_zfmisc_1(u1_struct_0(A_641))) | ~l1_pre_topc(A_641))), inference(cnfTransformation, [status(thm)], [f_156])).
% 13.93/6.42  tff(c_25737, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_25716])).
% 13.93/6.42  tff(c_25749, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_22089, c_25737])).
% 13.93/6.42  tff(c_27649, plain, (![A_686, B_687]: (k7_subset_1(u1_struct_0(A_686), B_687, k2_tops_1(A_686, B_687))=k1_tops_1(A_686, B_687) | ~m1_subset_1(B_687, k1_zfmisc_1(u1_struct_0(A_686))) | ~l1_pre_topc(A_686))), inference(cnfTransformation, [status(thm)], [f_163])).
% 13.93/6.42  tff(c_27672, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_27649])).
% 13.93/6.42  tff(c_27688, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_24567, c_27672])).
% 13.93/6.42  tff(c_23215, plain, (![A_555, B_556]: (k4_xboole_0(A_555, B_556)=k3_subset_1(A_555, B_556) | ~m1_subset_1(B_556, k1_zfmisc_1(A_555)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.93/6.42  tff(c_31409, plain, (![B_748, A_749]: (k4_xboole_0(B_748, A_749)=k3_subset_1(B_748, A_749) | ~r1_tarski(A_749, B_748))), inference(resolution, [status(thm)], [c_58, c_23215])).
% 13.93/6.42  tff(c_31499, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_25749, c_31409])).
% 13.93/6.42  tff(c_31614, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27688, c_31499])).
% 13.93/6.42  tff(c_24082, plain, (![A_584, B_585]: (k3_subset_1(A_584, k3_subset_1(A_584, B_585))=B_585 | ~m1_subset_1(B_585, k1_zfmisc_1(A_584)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.93/6.42  tff(c_24101, plain, (![B_51, A_50]: (k3_subset_1(B_51, k3_subset_1(B_51, A_50))=A_50 | ~r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_58, c_24082])).
% 13.93/6.42  tff(c_34115, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_31614, c_24101])).
% 13.93/6.42  tff(c_34123, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25749, c_34115])).
% 13.93/6.42  tff(c_48, plain, (![A_41, B_42]: (k6_subset_1(A_41, B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.93/6.42  tff(c_42, plain, (![A_34, B_35]: (m1_subset_1(k6_subset_1(A_34, B_35), k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.93/6.42  tff(c_89, plain, (![A_34, B_35]: (m1_subset_1(k4_xboole_0(A_34, B_35), k1_zfmisc_1(A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42])).
% 13.93/6.42  tff(c_33434, plain, (![A_780, B_781]: (k4_xboole_0(A_780, k4_xboole_0(A_780, B_781))=k3_subset_1(A_780, k4_xboole_0(A_780, B_781)))), inference(resolution, [status(thm)], [c_89, c_23215])).
% 13.93/6.42  tff(c_36338, plain, (![A_807, B_808]: (m1_subset_1(k3_subset_1(A_807, k4_xboole_0(A_807, B_808)), k1_zfmisc_1(A_807)))), inference(superposition, [status(thm), theory('equality')], [c_33434, c_89])).
% 13.93/6.42  tff(c_36414, plain, (m1_subset_1(k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_27688, c_36338])).
% 13.93/6.42  tff(c_39577, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34123, c_36414])).
% 13.93/6.42  tff(c_23741, plain, (![A_575, B_576]: (m1_subset_1(k3_subset_1(A_575, B_576), k1_zfmisc_1(A_575)) | ~m1_subset_1(B_576, k1_zfmisc_1(A_575)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.93/6.42  tff(c_38, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k3_subset_1(A_30, B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.93/6.42  tff(c_45212, plain, (![A_885, B_886]: (k4_xboole_0(A_885, k3_subset_1(A_885, B_886))=k3_subset_1(A_885, k3_subset_1(A_885, B_886)) | ~m1_subset_1(B_886, k1_zfmisc_1(A_885)))), inference(resolution, [status(thm)], [c_23741, c_38])).
% 13.93/6.42  tff(c_45214, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_39577, c_45212])).
% 13.93/6.42  tff(c_45238, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34123, c_31614, c_31614, c_45214])).
% 13.93/6.42  tff(c_45240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24576, c_45238])).
% 13.93/6.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.93/6.42  
% 13.93/6.42  Inference rules
% 13.93/6.42  ----------------------
% 13.93/6.42  #Ref     : 2
% 13.93/6.42  #Sup     : 11263
% 13.93/6.42  #Fact    : 0
% 13.93/6.42  #Define  : 0
% 13.93/6.42  #Split   : 9
% 13.93/6.42  #Chain   : 0
% 13.93/6.42  #Close   : 0
% 13.93/6.42  
% 13.93/6.42  Ordering : KBO
% 13.93/6.42  
% 13.93/6.42  Simplification rules
% 13.93/6.42  ----------------------
% 13.93/6.42  #Subsume      : 1653
% 13.93/6.42  #Demod        : 8342
% 13.93/6.42  #Tautology    : 6422
% 13.93/6.42  #SimpNegUnit  : 148
% 13.93/6.42  #BackRed      : 13
% 13.93/6.42  
% 13.93/6.42  #Partial instantiations: 0
% 13.93/6.42  #Strategies tried      : 1
% 13.93/6.42  
% 13.93/6.42  Timing (in seconds)
% 13.93/6.42  ----------------------
% 13.93/6.42  Preprocessing        : 0.39
% 13.93/6.42  Parsing              : 0.22
% 13.93/6.42  CNF conversion       : 0.02
% 13.93/6.42  Main loop            : 5.18
% 13.93/6.42  Inferencing          : 0.90
% 13.93/6.42  Reduction            : 2.85
% 13.93/6.42  Demodulation         : 2.42
% 13.93/6.42  BG Simplification    : 0.10
% 13.93/6.42  Subsumption          : 1.04
% 13.93/6.42  Abstraction          : 0.16
% 13.93/6.42  MUC search           : 0.00
% 13.93/6.42  Cooper               : 0.00
% 13.93/6.42  Total                : 5.62
% 13.93/6.42  Index Insertion      : 0.00
% 13.93/6.42  Index Deletion       : 0.00
% 13.93/6.42  Index Matching       : 0.00
% 13.93/6.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:21:33 EST 2020

% Result     : Theorem 9.70s
% Output     : CNFRefutation 9.94s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 192 expanded)
%              Number of leaves         :   40 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  147 ( 332 expanded)
%              Number of equality atoms :   59 ( 115 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_110,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_9786,plain,(
    ! [A_307,B_308,C_309] :
      ( k7_subset_1(A_307,B_308,C_309) = k4_xboole_0(B_308,C_309)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(A_307)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9792,plain,(
    ! [C_309] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_309) = k4_xboole_0('#skF_2',C_309) ),
    inference(resolution,[status(thm)],[c_40,c_9786])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_258,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2337,plain,(
    ! [A_144,B_145] :
      ( k4_subset_1(u1_struct_0(A_144),B_145,k2_tops_1(A_144,B_145)) = k2_pre_topc(A_144,B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2342,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2337])).

tff(c_2346,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2342])).

tff(c_14,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_343,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_361,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k2_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_343])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_237,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_259,plain,(
    ! [A_61] : k3_xboole_0(k1_xboole_0,A_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_237])).

tff(c_277,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_259])).

tff(c_725,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_745,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k4_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_725])).

tff(c_763,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_18,c_745])).

tff(c_816,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_361])).

tff(c_1241,plain,(
    ! [A_102,B_103,C_104] :
      ( k7_subset_1(A_102,B_103,C_104) = k4_xboole_0(B_103,C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1276,plain,(
    ! [C_107] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_107) = k4_xboole_0('#skF_2',C_107) ),
    inference(resolution,[status(thm)],[c_40,c_1241])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_102,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1282,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_102])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [A_13,B_14] : k4_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_108])).

tff(c_1389,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_127])).

tff(c_22,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1419,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_22])).

tff(c_1433,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_1419])).

tff(c_103,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_107,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_103])).

tff(c_253,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_107,c_237])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_877,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(A_86,C_87)
      | ~ r1_tarski(B_88,C_87)
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1721,plain,(
    ! [A_126,A_127,B_128] :
      ( r1_tarski(A_126,A_127)
      | ~ r1_tarski(A_126,k4_xboole_0(A_127,B_128)) ) ),
    inference(resolution,[status(thm)],[c_16,c_877])).

tff(c_1880,plain,(
    ! [A_132,B_133,B_134] : r1_tarski(k4_xboole_0(k4_xboole_0(A_132,B_133),B_134),A_132) ),
    inference(resolution,[status(thm)],[c_16,c_1721])).

tff(c_2078,plain,(
    ! [A_140,B_141,B_142] : r1_tarski(k4_xboole_0(k3_xboole_0(A_140,B_141),B_142),A_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1880])).

tff(c_2997,plain,(
    ! [A_164,B_165,B_166] : r1_tarski(k4_xboole_0(k3_xboole_0(A_164,B_165),B_166),B_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2078])).

tff(c_3086,plain,(
    ! [B_167] : r1_tarski(k4_xboole_0('#skF_2',B_167),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_2997])).

tff(c_3109,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_3086])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1561,plain,(
    ! [A_118,B_119,C_120] :
      ( k4_subset_1(A_118,B_119,C_120) = k2_xboole_0(B_119,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8447,plain,(
    ! [B_242,B_243,A_244] :
      ( k4_subset_1(B_242,B_243,A_244) = k2_xboole_0(B_243,A_244)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(B_242))
      | ~ r1_tarski(A_244,B_242) ) ),
    inference(resolution,[status(thm)],[c_30,c_1561])).

tff(c_8457,plain,(
    ! [A_245] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_245) = k2_xboole_0('#skF_2',A_245)
      | ~ r1_tarski(A_245,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_8447])).

tff(c_8480,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3109,c_8457])).

tff(c_8561,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2346,c_1433,c_8480])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1367,plain,(
    ! [A_110,B_111] :
      ( v4_pre_topc(k2_pre_topc(A_110,B_111),A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1372,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1367])).

tff(c_1376,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1372])).

tff(c_8588,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8561,c_1376])).

tff(c_8590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_8588])).

tff(c_8591,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_8922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8591,c_102])).

tff(c_8923,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_9060,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8923,c_46])).

tff(c_9975,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_9060])).

tff(c_10172,plain,(
    ! [A_325,B_326] :
      ( r1_tarski(k2_tops_1(A_325,B_326),B_326)
      | ~ v4_pre_topc(B_326,A_325)
      | ~ m1_subset_1(B_326,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ l1_pre_topc(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10177,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_10172])).

tff(c_10181,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8923,c_10177])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10191,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_10181,c_12])).

tff(c_12409,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10191])).

tff(c_10540,plain,(
    ! [A_339,B_340] :
      ( k7_subset_1(u1_struct_0(A_339),B_340,k2_tops_1(A_339,B_340)) = k1_tops_1(A_339,B_340)
      | ~ m1_subset_1(B_340,k1_zfmisc_1(u1_struct_0(A_339)))
      | ~ l1_pre_topc(A_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10545,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_10540])).

tff(c_10549,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_9792,c_10545])).

tff(c_10786,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10549,c_20])).

tff(c_24772,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12409,c_10786])).

tff(c_24773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9975,c_24772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.70/3.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.70/3.87  
% 9.70/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.70/3.87  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.70/3.87  
% 9.70/3.87  %Foreground sorts:
% 9.70/3.87  
% 9.70/3.87  
% 9.70/3.87  %Background operators:
% 9.70/3.87  
% 9.70/3.87  
% 9.70/3.87  %Foreground operators:
% 9.70/3.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.70/3.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.70/3.87  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.70/3.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.70/3.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.70/3.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.70/3.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.70/3.87  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.70/3.87  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.70/3.87  tff('#skF_2', type, '#skF_2': $i).
% 9.70/3.87  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.70/3.87  tff('#skF_1', type, '#skF_1': $i).
% 9.70/3.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.70/3.87  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.70/3.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.70/3.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.70/3.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.70/3.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.70/3.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.70/3.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.70/3.87  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.70/3.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.70/3.87  
% 9.94/3.89  tff(f_110, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 9.94/3.89  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.94/3.89  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 9.94/3.89  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.94/3.89  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.94/3.89  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.94/3.89  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.94/3.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.94/3.89  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.94/3.89  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.94/3.89  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.94/3.89  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.94/3.89  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.94/3.89  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.94/3.89  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.94/3.89  tff(f_75, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 9.94/3.89  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 9.94/3.89  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 9.94/3.89  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.94/3.89  tff(c_9786, plain, (![A_307, B_308, C_309]: (k7_subset_1(A_307, B_308, C_309)=k4_xboole_0(B_308, C_309) | ~m1_subset_1(B_308, k1_zfmisc_1(A_307)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.94/3.89  tff(c_9792, plain, (![C_309]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_309)=k4_xboole_0('#skF_2', C_309))), inference(resolution, [status(thm)], [c_40, c_9786])).
% 9.94/3.89  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.94/3.89  tff(c_258, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 9.94/3.89  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.94/3.89  tff(c_2337, plain, (![A_144, B_145]: (k4_subset_1(u1_struct_0(A_144), B_145, k2_tops_1(A_144, B_145))=k2_pre_topc(A_144, B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.94/3.89  tff(c_2342, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2337])).
% 9.94/3.89  tff(c_2346, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2342])).
% 9.94/3.89  tff(c_14, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.94/3.89  tff(c_108, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.94/3.89  tff(c_128, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_108])).
% 9.94/3.89  tff(c_343, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.94/3.89  tff(c_361, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k2_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_128, c_343])).
% 9.94/3.89  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.94/3.89  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.94/3.89  tff(c_237, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.94/3.89  tff(c_259, plain, (![A_61]: (k3_xboole_0(k1_xboole_0, A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_237])).
% 9.94/3.89  tff(c_277, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_259])).
% 9.94/3.89  tff(c_725, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.94/3.89  tff(c_745, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k4_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_277, c_725])).
% 9.94/3.89  tff(c_763, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_361, c_18, c_745])).
% 9.94/3.89  tff(c_816, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_763, c_361])).
% 9.94/3.89  tff(c_1241, plain, (![A_102, B_103, C_104]: (k7_subset_1(A_102, B_103, C_104)=k4_xboole_0(B_103, C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.94/3.89  tff(c_1276, plain, (![C_107]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_107)=k4_xboole_0('#skF_2', C_107))), inference(resolution, [status(thm)], [c_40, c_1241])).
% 9.94/3.89  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.94/3.89  tff(c_102, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 9.94/3.89  tff(c_1282, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1276, c_102])).
% 9.94/3.89  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.94/3.89  tff(c_127, plain, (![A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_108])).
% 9.94/3.89  tff(c_1389, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1282, c_127])).
% 9.94/3.89  tff(c_22, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.94/3.89  tff(c_1419, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1389, c_22])).
% 9.94/3.89  tff(c_1433, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_816, c_1419])).
% 9.94/3.89  tff(c_103, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.94/3.89  tff(c_107, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_103])).
% 9.94/3.89  tff(c_253, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_107, c_237])).
% 9.94/3.89  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.94/3.89  tff(c_877, plain, (![A_86, C_87, B_88]: (r1_tarski(A_86, C_87) | ~r1_tarski(B_88, C_87) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.94/3.89  tff(c_1721, plain, (![A_126, A_127, B_128]: (r1_tarski(A_126, A_127) | ~r1_tarski(A_126, k4_xboole_0(A_127, B_128)))), inference(resolution, [status(thm)], [c_16, c_877])).
% 9.94/3.89  tff(c_1880, plain, (![A_132, B_133, B_134]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_132, B_133), B_134), A_132))), inference(resolution, [status(thm)], [c_16, c_1721])).
% 9.94/3.89  tff(c_2078, plain, (![A_140, B_141, B_142]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_140, B_141), B_142), A_140))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1880])).
% 9.94/3.89  tff(c_2997, plain, (![A_164, B_165, B_166]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_164, B_165), B_166), B_165))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2078])).
% 9.94/3.89  tff(c_3086, plain, (![B_167]: (r1_tarski(k4_xboole_0('#skF_2', B_167), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_253, c_2997])).
% 9.94/3.89  tff(c_3109, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1282, c_3086])).
% 9.94/3.89  tff(c_30, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.94/3.89  tff(c_1561, plain, (![A_118, B_119, C_120]: (k4_subset_1(A_118, B_119, C_120)=k2_xboole_0(B_119, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(A_118)) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.94/3.89  tff(c_8447, plain, (![B_242, B_243, A_244]: (k4_subset_1(B_242, B_243, A_244)=k2_xboole_0(B_243, A_244) | ~m1_subset_1(B_243, k1_zfmisc_1(B_242)) | ~r1_tarski(A_244, B_242))), inference(resolution, [status(thm)], [c_30, c_1561])).
% 9.94/3.89  tff(c_8457, plain, (![A_245]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_245)=k2_xboole_0('#skF_2', A_245) | ~r1_tarski(A_245, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_8447])).
% 9.94/3.89  tff(c_8480, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3109, c_8457])).
% 9.94/3.89  tff(c_8561, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2346, c_1433, c_8480])).
% 9.94/3.89  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.94/3.89  tff(c_1367, plain, (![A_110, B_111]: (v4_pre_topc(k2_pre_topc(A_110, B_111), A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.94/3.89  tff(c_1372, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1367])).
% 9.94/3.89  tff(c_1376, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1372])).
% 9.94/3.89  tff(c_8588, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8561, c_1376])).
% 9.94/3.89  tff(c_8590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_8588])).
% 9.94/3.89  tff(c_8591, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 9.94/3.89  tff(c_8922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8591, c_102])).
% 9.94/3.89  tff(c_8923, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 9.94/3.89  tff(c_9060, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8923, c_46])).
% 9.94/3.89  tff(c_9975, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_9060])).
% 9.94/3.89  tff(c_10172, plain, (![A_325, B_326]: (r1_tarski(k2_tops_1(A_325, B_326), B_326) | ~v4_pre_topc(B_326, A_325) | ~m1_subset_1(B_326, k1_zfmisc_1(u1_struct_0(A_325))) | ~l1_pre_topc(A_325))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.94/3.89  tff(c_10177, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_10172])).
% 9.94/3.89  tff(c_10181, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8923, c_10177])).
% 9.94/3.89  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.94/3.89  tff(c_10191, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_10181, c_12])).
% 9.94/3.89  tff(c_12409, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2, c_10191])).
% 9.94/3.89  tff(c_10540, plain, (![A_339, B_340]: (k7_subset_1(u1_struct_0(A_339), B_340, k2_tops_1(A_339, B_340))=k1_tops_1(A_339, B_340) | ~m1_subset_1(B_340, k1_zfmisc_1(u1_struct_0(A_339))) | ~l1_pre_topc(A_339))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.94/3.89  tff(c_10545, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_10540])).
% 9.94/3.89  tff(c_10549, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_9792, c_10545])).
% 9.94/3.89  tff(c_10786, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10549, c_20])).
% 9.94/3.89  tff(c_24772, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12409, c_10786])).
% 9.94/3.89  tff(c_24773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9975, c_24772])).
% 9.94/3.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.94/3.89  
% 9.94/3.89  Inference rules
% 9.94/3.89  ----------------------
% 9.94/3.89  #Ref     : 2
% 9.94/3.89  #Sup     : 6143
% 9.94/3.89  #Fact    : 0
% 9.94/3.89  #Define  : 0
% 9.94/3.89  #Split   : 9
% 9.94/3.89  #Chain   : 0
% 9.94/3.89  #Close   : 0
% 9.94/3.89  
% 9.94/3.89  Ordering : KBO
% 9.94/3.89  
% 9.94/3.89  Simplification rules
% 9.94/3.89  ----------------------
% 9.94/3.89  #Subsume      : 983
% 9.94/3.89  #Demod        : 4665
% 9.94/3.89  #Tautology    : 3813
% 9.94/3.89  #SimpNegUnit  : 27
% 9.94/3.89  #BackRed      : 11
% 9.94/3.89  
% 9.94/3.89  #Partial instantiations: 0
% 9.94/3.89  #Strategies tried      : 1
% 9.94/3.89  
% 9.94/3.89  Timing (in seconds)
% 9.94/3.89  ----------------------
% 9.94/3.89  Preprocessing        : 0.35
% 9.94/3.89  Parsing              : 0.19
% 9.94/3.89  CNF conversion       : 0.02
% 9.94/3.89  Main loop            : 2.76
% 9.94/3.89  Inferencing          : 0.63
% 9.94/3.89  Reduction            : 1.42
% 9.94/3.89  Demodulation         : 1.20
% 9.94/3.89  BG Simplification    : 0.07
% 9.94/3.89  Subsumption          : 0.48
% 9.94/3.89  Abstraction          : 0.11
% 9.94/3.89  MUC search           : 0.00
% 9.94/3.89  Cooper               : 0.00
% 9.94/3.89  Total                : 3.15
% 9.94/3.89  Index Insertion      : 0.00
% 9.94/3.89  Index Deletion       : 0.00
% 9.94/3.89  Index Matching       : 0.00
% 9.94/3.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------

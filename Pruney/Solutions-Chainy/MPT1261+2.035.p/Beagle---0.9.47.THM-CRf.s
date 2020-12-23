%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:16 EST 2020

% Result     : Theorem 21.67s
% Output     : CNFRefutation 21.67s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 408 expanded)
%              Number of leaves         :   47 ( 154 expanded)
%              Depth                    :   16
%              Number of atoms          :  245 ( 643 expanded)
%              Number of equality atoms :  115 ( 269 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_108,axiom,(
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

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_39751,plain,(
    ! [A_786,B_787,C_788] :
      ( k7_subset_1(A_786,B_787,C_788) = k4_xboole_0(B_787,C_788)
      | ~ m1_subset_1(B_787,k1_zfmisc_1(A_786)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_39760,plain,(
    ! [C_788] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_788) = k4_xboole_0('#skF_2',C_788) ),
    inference(resolution,[status(thm)],[c_60,c_39751])).

tff(c_41360,plain,(
    ! [A_856,B_857] :
      ( k7_subset_1(u1_struct_0(A_856),B_857,k2_tops_1(A_856,B_857)) = k1_tops_1(A_856,B_857)
      | ~ m1_subset_1(B_857,k1_zfmisc_1(u1_struct_0(A_856)))
      | ~ l1_pre_topc(A_856) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_41370,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_41360])).

tff(c_41376,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_39760,c_41370])).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_41416,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41376,c_20])).

tff(c_66,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_239,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3161,plain,(
    ! [B_234,A_235] :
      ( v4_pre_topc(B_234,A_235)
      | k2_pre_topc(A_235,B_234) != B_234
      | ~ v2_pre_topc(A_235)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ l1_pre_topc(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3175,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3161])).

tff(c_3181,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_3175])).

tff(c_3182,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_3181])).

tff(c_72,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_137,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_1932,plain,(
    ! [A_179,B_180,C_181] :
      ( k7_subset_1(A_179,B_180,C_181) = k4_xboole_0(B_180,C_181)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(A_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1945,plain,(
    ! [C_182] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_182) = k4_xboole_0('#skF_2',C_182) ),
    inference(resolution,[status(thm)],[c_60,c_1932])).

tff(c_1957,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_1945])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_163,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_183,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(B_81,A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_163])).

tff(c_24,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    ! [B_81,A_80] : k2_xboole_0(B_81,A_80) = k2_xboole_0(A_80,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_24])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_546,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_tarski(A_100,C_101)
      | ~ r1_tarski(B_102,C_101)
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_753,plain,(
    ! [A_116,A_117,B_118] :
      ( r1_tarski(A_116,A_117)
      | ~ r1_tarski(A_116,k4_xboole_0(A_117,B_118)) ) ),
    inference(resolution,[status(thm)],[c_8,c_546])).

tff(c_792,plain,(
    ! [A_117,B_118,B_8] : r1_tarski(k4_xboole_0(k4_xboole_0(A_117,B_118),B_8),A_117) ),
    inference(resolution,[status(thm)],[c_8,c_753])).

tff(c_1432,plain,(
    ! [A_153,B_154,C_155] :
      ( r1_tarski(A_153,k2_xboole_0(B_154,C_155))
      | ~ r1_tarski(k4_xboole_0(A_153,B_154),C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1630,plain,(
    ! [A_164,B_165,B_166] : r1_tarski(k4_xboole_0(A_164,B_165),k2_xboole_0(B_166,A_164)) ),
    inference(resolution,[status(thm)],[c_792,c_1432])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k2_xboole_0(B_18,C_19))
      | ~ r1_tarski(k4_xboole_0(A_17,B_18),C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1962,plain,(
    ! [A_183,B_184,B_185] : r1_tarski(A_183,k2_xboole_0(B_184,k2_xboole_0(B_185,A_183))) ),
    inference(resolution,[status(thm)],[c_1630,c_18])).

tff(c_2000,plain,(
    ! [A_183,B_185,A_80] : r1_tarski(A_183,k2_xboole_0(k2_xboole_0(B_185,A_183),A_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_1962])).

tff(c_793,plain,(
    ! [A_119,B_120,C_121] :
      ( r1_tarski(k4_xboole_0(A_119,B_120),C_121)
      | ~ r1_tarski(A_119,k2_xboole_0(B_120,C_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8309,plain,(
    ! [A_351,B_352,B_353] :
      ( k4_xboole_0(A_351,B_352) = k1_xboole_0
      | ~ r1_tarski(A_351,k2_xboole_0(B_352,k4_xboole_0(B_353,k4_xboole_0(A_351,B_352)))) ) ),
    inference(resolution,[status(thm)],[c_793,c_10])).

tff(c_9237,plain,(
    ! [A_364,B_365] : k4_xboole_0(A_364,k2_xboole_0(B_365,A_364)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2000,c_8309])).

tff(c_9317,plain,(
    ! [A_364,B_365] : k3_xboole_0(A_364,k2_xboole_0(B_365,A_364)) = k4_xboole_0(A_364,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9237,c_20])).

tff(c_9389,plain,(
    ! [A_364,B_365] : k3_xboole_0(A_364,k2_xboole_0(B_365,A_364)) = A_364 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_9317])).

tff(c_2853,plain,(
    ! [A_230,C_231] :
      ( r1_tarski(A_230,C_231)
      | ~ r1_tarski(A_230,k2_xboole_0(k1_xboole_0,C_231)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_793])).

tff(c_3236,plain,(
    ! [C_237,B_238] : r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,C_237),B_238),C_237) ),
    inference(resolution,[status(thm)],[c_8,c_2853])).

tff(c_3485,plain,(
    ! [C_246,B_247] : r1_tarski(k2_xboole_0(k1_xboole_0,C_246),k2_xboole_0(B_247,C_246)) ),
    inference(resolution,[status(thm)],[c_3236,c_18])).

tff(c_3535,plain,(
    ! [A_80,B_81] : r1_tarski(k2_xboole_0(k1_xboole_0,A_80),k2_xboole_0(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_3485])).

tff(c_8523,plain,(
    ! [A_355] : k4_xboole_0(k2_xboole_0(k1_xboole_0,A_355),A_355) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3535,c_8309])).

tff(c_8584,plain,(
    ! [A_355] : k4_xboole_0(k2_xboole_0(k1_xboole_0,A_355),k1_xboole_0) = k3_xboole_0(k2_xboole_0(k1_xboole_0,A_355),A_355) ),
    inference(superposition,[status(thm),theory(equality)],[c_8523,c_20])).

tff(c_30303,plain,(
    ! [A_583] : k3_xboole_0(k2_xboole_0(k1_xboole_0,A_583),A_583) = k2_xboole_0(k1_xboole_0,A_583) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8584])).

tff(c_138,plain,(
    ! [A_70,B_71] : k1_setfam_1(k2_tarski(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_240,plain,(
    ! [B_84,A_85] : k1_setfam_1(k2_tarski(B_84,A_85)) = k3_xboole_0(A_85,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_40,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_246,plain,(
    ! [B_84,A_85] : k3_xboole_0(B_84,A_85) = k3_xboole_0(A_85,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_40])).

tff(c_30528,plain,(
    ! [A_583] : k3_xboole_0(A_583,k2_xboole_0(k1_xboole_0,A_583)) = k2_xboole_0(k1_xboole_0,A_583) ),
    inference(superposition,[status(thm),theory(equality)],[c_30303,c_246])).

tff(c_30632,plain,(
    ! [A_583] : k2_xboole_0(k1_xboole_0,A_583) = A_583 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9389,c_30528])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_425,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_460,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_425])).

tff(c_468,plain,(
    ! [A_97] : k4_xboole_0(A_97,A_97) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_460])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_659,plain,(
    ! [A_111] : k2_xboole_0(A_111,k1_xboole_0) = k2_xboole_0(A_111,A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_12])).

tff(c_668,plain,(
    ! [A_111] : k2_xboole_0(k1_xboole_0,A_111) = k2_xboole_0(A_111,A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_659,c_189])).

tff(c_30677,plain,(
    ! [A_111] : k2_xboole_0(A_111,A_111) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30632,c_668])).

tff(c_479,plain,(
    ! [A_97] : k2_xboole_0(A_97,k1_xboole_0) = k2_xboole_0(A_97,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_12])).

tff(c_31149,plain,(
    ! [A_97] : k2_xboole_0(A_97,k1_xboole_0) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30677,c_479])).

tff(c_1670,plain,(
    ! [A_80,B_165,B_81] : r1_tarski(k4_xboole_0(A_80,B_165),k2_xboole_0(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_1630])).

tff(c_8650,plain,(
    ! [A_356,B_357] : k4_xboole_0(k4_xboole_0(A_356,B_357),A_356) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1670,c_8309])).

tff(c_8709,plain,(
    ! [A_356,B_357] : k2_xboole_0(A_356,k4_xboole_0(A_356,B_357)) = k2_xboole_0(A_356,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8650,c_12])).

tff(c_35830,plain,(
    ! [A_642,B_643] : k2_xboole_0(A_642,k4_xboole_0(A_642,B_643)) = A_642 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31149,c_8709])).

tff(c_36175,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1957,c_35830])).

tff(c_2401,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1957,c_8])).

tff(c_158,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_162,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_158])).

tff(c_556,plain,(
    ! [A_100] :
      ( r1_tarski(A_100,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_100,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_162,c_546])).

tff(c_44,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,k1_zfmisc_1(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2787,plain,(
    ! [A_224,B_225,C_226] :
      ( k4_subset_1(A_224,B_225,C_226) = k2_xboole_0(B_225,C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(A_224))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(A_224)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_13081,plain,(
    ! [B_397,B_398,A_399] :
      ( k4_subset_1(B_397,B_398,A_399) = k2_xboole_0(B_398,A_399)
      | ~ m1_subset_1(B_398,k1_zfmisc_1(B_397))
      | ~ r1_tarski(A_399,B_397) ) ),
    inference(resolution,[status(thm)],[c_44,c_2787])).

tff(c_13235,plain,(
    ! [A_401] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_401) = k2_xboole_0('#skF_2',A_401)
      | ~ r1_tarski(A_401,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_60,c_13081])).

tff(c_15685,plain,(
    ! [A_429] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_429) = k2_xboole_0('#skF_2',A_429)
      | ~ r1_tarski(A_429,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_556,c_13235])).

tff(c_3804,plain,(
    ! [A_254,B_255] :
      ( k4_subset_1(u1_struct_0(A_254),B_255,k2_tops_1(A_254,B_255)) = k2_pre_topc(A_254,B_255)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3814,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3804])).

tff(c_3820,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3814])).

tff(c_15697,plain,
    ( k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15685,c_3820])).

tff(c_15735,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2401,c_15697])).

tff(c_37001,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36175,c_15735])).

tff(c_37003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3182,c_37001])).

tff(c_37004,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_37301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37004,c_137])).

tff(c_37302,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_37420,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37302,c_66])).

tff(c_39884,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39760,c_37420])).

tff(c_75603,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41416,c_39884])).

tff(c_40516,plain,(
    ! [A_817,B_818] :
      ( k2_pre_topc(A_817,B_818) = B_818
      | ~ v4_pre_topc(B_818,A_817)
      | ~ m1_subset_1(B_818,k1_zfmisc_1(u1_struct_0(A_817)))
      | ~ l1_pre_topc(A_817) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40530,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_40516])).

tff(c_40536,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_37302,c_40530])).

tff(c_41497,plain,(
    ! [A_860,B_861] :
      ( k4_subset_1(u1_struct_0(A_860),B_861,k2_tops_1(A_860,B_861)) = k2_pre_topc(A_860,B_861)
      | ~ m1_subset_1(B_861,k1_zfmisc_1(u1_struct_0(A_860)))
      | ~ l1_pre_topc(A_860) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_41507,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_41497])).

tff(c_41513,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40536,c_41507])).

tff(c_50,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k2_tops_1(A_48,B_49),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40804,plain,(
    ! [A_830,B_831,C_832] :
      ( k4_subset_1(A_830,B_831,C_832) = k2_xboole_0(B_831,C_832)
      | ~ m1_subset_1(C_832,k1_zfmisc_1(A_830))
      | ~ m1_subset_1(B_831,k1_zfmisc_1(A_830)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68915,plain,(
    ! [A_1202,B_1203,B_1204] :
      ( k4_subset_1(u1_struct_0(A_1202),B_1203,k2_tops_1(A_1202,B_1204)) = k2_xboole_0(B_1203,k2_tops_1(A_1202,B_1204))
      | ~ m1_subset_1(B_1203,k1_zfmisc_1(u1_struct_0(A_1202)))
      | ~ m1_subset_1(B_1204,k1_zfmisc_1(u1_struct_0(A_1202)))
      | ~ l1_pre_topc(A_1202) ) ),
    inference(resolution,[status(thm)],[c_50,c_40804])).

tff(c_68931,plain,(
    ! [B_1204] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_1204)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_1204))
      | ~ m1_subset_1(B_1204,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_68915])).

tff(c_98821,plain,(
    ! [B_1410] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_1410)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_1410))
      | ~ m1_subset_1(B_1410,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_68931])).

tff(c_98844,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_98821])).

tff(c_98853,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41513,c_98844])).

tff(c_37457,plain,(
    ! [A_676,B_677] : k4_xboole_0(A_676,k4_xboole_0(A_676,B_677)) = k3_xboole_0(A_676,B_677) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_37478,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_37457])).

tff(c_37482,plain,(
    ! [A_678] : k4_xboole_0(A_678,A_678) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_37478])).

tff(c_37487,plain,(
    ! [A_678] : k4_xboole_0(A_678,k1_xboole_0) = k3_xboole_0(A_678,A_678) ),
    inference(superposition,[status(thm),theory(equality)],[c_37482,c_20])).

tff(c_37505,plain,(
    ! [A_678] : k3_xboole_0(A_678,A_678) = A_678 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_37487])).

tff(c_37329,plain,(
    ! [A_667,B_668] : k3_tarski(k2_tarski(A_667,B_668)) = k2_xboole_0(A_667,B_668) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37757,plain,(
    ! [B_694,A_695] : k3_tarski(k2_tarski(B_694,A_695)) = k2_xboole_0(A_695,B_694) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_37329])).

tff(c_37763,plain,(
    ! [B_694,A_695] : k2_xboole_0(B_694,A_695) = k2_xboole_0(A_695,B_694) ),
    inference(superposition,[status(thm),theory(equality)],[c_37757,c_24])).

tff(c_37827,plain,(
    ! [A_698,C_699,B_700] :
      ( r1_tarski(A_698,C_699)
      | ~ r1_tarski(B_700,C_699)
      | ~ r1_tarski(A_698,B_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_37912,plain,(
    ! [A_705,A_706,B_707] :
      ( r1_tarski(A_705,A_706)
      | ~ r1_tarski(A_705,k4_xboole_0(A_706,B_707)) ) ),
    inference(resolution,[status(thm)],[c_8,c_37827])).

tff(c_37951,plain,(
    ! [A_706,B_707,B_8] : r1_tarski(k4_xboole_0(k4_xboole_0(A_706,B_707),B_8),A_706) ),
    inference(resolution,[status(thm)],[c_8,c_37912])).

tff(c_38781,plain,(
    ! [A_750,B_751,C_752] :
      ( r1_tarski(A_750,k2_xboole_0(B_751,C_752))
      | ~ r1_tarski(k4_xboole_0(A_750,B_751),C_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_39503,plain,(
    ! [A_777,B_778,B_779] : r1_tarski(k4_xboole_0(A_777,B_778),k2_xboole_0(B_779,A_777)) ),
    inference(resolution,[status(thm)],[c_37951,c_38781])).

tff(c_40451,plain,(
    ! [A_814,B_815,B_816] : r1_tarski(A_814,k2_xboole_0(B_815,k2_xboole_0(B_816,A_814))) ),
    inference(resolution,[status(thm)],[c_39503,c_18])).

tff(c_40490,plain,(
    ! [A_814,B_816,B_694] : r1_tarski(A_814,k2_xboole_0(k2_xboole_0(B_816,A_814),B_694)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37763,c_40451])).

tff(c_38316,plain,(
    ! [A_730,B_731,C_732] :
      ( r1_tarski(k4_xboole_0(A_730,B_731),C_732)
      | ~ r1_tarski(A_730,k2_xboole_0(B_731,C_732)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48354,plain,(
    ! [A_982,B_983,B_984] :
      ( k4_xboole_0(A_982,B_983) = k1_xboole_0
      | ~ r1_tarski(A_982,k2_xboole_0(B_983,k4_xboole_0(B_984,k4_xboole_0(A_982,B_983)))) ) ),
    inference(resolution,[status(thm)],[c_38316,c_10])).

tff(c_49153,plain,(
    ! [A_989,B_990] : k4_xboole_0(A_989,k2_xboole_0(B_990,A_989)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40490,c_48354])).

tff(c_49247,plain,(
    ! [A_989,B_990] : k3_xboole_0(A_989,k2_xboole_0(B_990,A_989)) = k4_xboole_0(A_989,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_49153,c_20])).

tff(c_49325,plain,(
    ! [A_989,B_990] : k3_xboole_0(A_989,k2_xboole_0(B_990,A_989)) = A_989 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_49247])).

tff(c_37314,plain,(
    ! [A_665,B_666] : k1_setfam_1(k2_tarski(A_665,B_666)) = k3_xboole_0(A_665,B_666) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_37349,plain,(
    ! [B_671,A_672] : k1_setfam_1(k2_tarski(B_671,A_672)) = k3_xboole_0(A_672,B_671) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_37314])).

tff(c_37355,plain,(
    ! [B_671,A_672] : k3_xboole_0(B_671,A_672) = k3_xboole_0(A_672,B_671) ),
    inference(superposition,[status(thm),theory(equality)],[c_37349,c_40])).

tff(c_40323,plain,(
    ! [B_809,B_810,A_811] : r1_tarski(k4_xboole_0(B_809,B_810),k2_xboole_0(B_809,A_811)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37763,c_39503])).

tff(c_40370,plain,(
    ! [A_20,B_21,A_811] : r1_tarski(k3_xboole_0(A_20,B_21),k2_xboole_0(A_20,A_811)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_40323])).

tff(c_49491,plain,(
    ! [A_992,B_993] : k4_xboole_0(k3_xboole_0(A_992,B_993),A_992) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40370,c_48354])).

tff(c_49665,plain,(
    ! [A_996,B_997] : k4_xboole_0(k3_xboole_0(A_996,B_997),B_997) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37355,c_49491])).

tff(c_49738,plain,(
    ! [A_996,B_997] : k4_xboole_0(k3_xboole_0(A_996,B_997),k1_xboole_0) = k3_xboole_0(k3_xboole_0(A_996,B_997),B_997) ),
    inference(superposition,[status(thm),theory(equality)],[c_49665,c_20])).

tff(c_71389,plain,(
    ! [A_1226,B_1227] : k3_xboole_0(k3_xboole_0(A_1226,B_1227),B_1227) = k3_xboole_0(A_1226,B_1227) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_49738])).

tff(c_74092,plain,(
    ! [A_1261,B_1262] : k3_xboole_0(k3_xboole_0(A_1261,B_1262),A_1261) = k3_xboole_0(B_1262,A_1261) ),
    inference(superposition,[status(thm),theory(equality)],[c_37355,c_71389])).

tff(c_74441,plain,(
    ! [B_990,A_989] : k3_xboole_0(k2_xboole_0(B_990,A_989),A_989) = k3_xboole_0(A_989,A_989) ),
    inference(superposition,[status(thm),theory(equality)],[c_49325,c_74092])).

tff(c_74556,plain,(
    ! [B_990,A_989] : k3_xboole_0(k2_xboole_0(B_990,A_989),A_989) = A_989 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37505,c_74441])).

tff(c_98884,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_98853,c_74556])).

tff(c_99003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75603,c_98884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:28:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.67/13.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.67/13.12  
% 21.67/13.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.67/13.12  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 21.67/13.12  
% 21.67/13.12  %Foreground sorts:
% 21.67/13.12  
% 21.67/13.12  
% 21.67/13.12  %Background operators:
% 21.67/13.12  
% 21.67/13.12  
% 21.67/13.12  %Foreground operators:
% 21.67/13.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.67/13.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.67/13.12  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 21.67/13.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.67/13.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.67/13.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 21.67/13.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.67/13.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.67/13.12  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 21.67/13.12  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 21.67/13.12  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 21.67/13.12  tff('#skF_2', type, '#skF_2': $i).
% 21.67/13.12  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 21.67/13.12  tff('#skF_1', type, '#skF_1': $i).
% 21.67/13.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.67/13.12  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 21.67/13.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.67/13.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 21.67/13.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.67/13.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 21.67/13.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.67/13.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.67/13.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.67/13.12  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 21.67/13.12  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 21.67/13.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.67/13.12  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.67/13.12  
% 21.67/13.15  tff(f_155, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 21.67/13.15  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 21.67/13.15  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 21.67/13.15  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 21.67/13.15  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 21.67/13.15  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 21.67/13.15  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 21.67/13.15  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 21.67/13.15  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 21.67/13.15  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 21.67/13.15  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 21.67/13.15  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 21.67/13.15  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 21.67/13.15  tff(f_89, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 21.67/13.15  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 21.67/13.15  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 21.67/13.15  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 21.67/13.15  tff(f_79, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 21.67/13.15  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 21.67/13.15  tff(f_114, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 21.67/13.15  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 21.67/13.15  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 21.67/13.15  tff(c_39751, plain, (![A_786, B_787, C_788]: (k7_subset_1(A_786, B_787, C_788)=k4_xboole_0(B_787, C_788) | ~m1_subset_1(B_787, k1_zfmisc_1(A_786)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.67/13.15  tff(c_39760, plain, (![C_788]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_788)=k4_xboole_0('#skF_2', C_788))), inference(resolution, [status(thm)], [c_60, c_39751])).
% 21.67/13.15  tff(c_41360, plain, (![A_856, B_857]: (k7_subset_1(u1_struct_0(A_856), B_857, k2_tops_1(A_856, B_857))=k1_tops_1(A_856, B_857) | ~m1_subset_1(B_857, k1_zfmisc_1(u1_struct_0(A_856))) | ~l1_pre_topc(A_856))), inference(cnfTransformation, [status(thm)], [f_143])).
% 21.67/13.15  tff(c_41370, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_41360])).
% 21.67/13.15  tff(c_41376, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_39760, c_41370])).
% 21.67/13.15  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.67/13.15  tff(c_41416, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_41376, c_20])).
% 21.67/13.15  tff(c_66, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 21.67/13.15  tff(c_239, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 21.67/13.15  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 21.67/13.15  tff(c_3161, plain, (![B_234, A_235]: (v4_pre_topc(B_234, A_235) | k2_pre_topc(A_235, B_234)!=B_234 | ~v2_pre_topc(A_235) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_235))) | ~l1_pre_topc(A_235))), inference(cnfTransformation, [status(thm)], [f_108])).
% 21.67/13.15  tff(c_3175, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_3161])).
% 21.67/13.15  tff(c_3181, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_3175])).
% 21.67/13.15  tff(c_3182, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_239, c_3181])).
% 21.67/13.15  tff(c_72, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 21.67/13.15  tff(c_137, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_72])).
% 21.67/13.15  tff(c_1932, plain, (![A_179, B_180, C_181]: (k7_subset_1(A_179, B_180, C_181)=k4_xboole_0(B_180, C_181) | ~m1_subset_1(B_180, k1_zfmisc_1(A_179)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.67/13.15  tff(c_1945, plain, (![C_182]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_182)=k4_xboole_0('#skF_2', C_182))), inference(resolution, [status(thm)], [c_60, c_1932])).
% 21.67/13.15  tff(c_1957, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_137, c_1945])).
% 21.67/13.15  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.67/13.15  tff(c_22, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 21.67/13.15  tff(c_163, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.67/13.15  tff(c_183, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(B_81, A_80))), inference(superposition, [status(thm), theory('equality')], [c_22, c_163])).
% 21.67/13.15  tff(c_24, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.67/13.15  tff(c_189, plain, (![B_81, A_80]: (k2_xboole_0(B_81, A_80)=k2_xboole_0(A_80, B_81))), inference(superposition, [status(thm), theory('equality')], [c_183, c_24])).
% 21.67/13.15  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.67/13.15  tff(c_546, plain, (![A_100, C_101, B_102]: (r1_tarski(A_100, C_101) | ~r1_tarski(B_102, C_101) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.67/13.15  tff(c_753, plain, (![A_116, A_117, B_118]: (r1_tarski(A_116, A_117) | ~r1_tarski(A_116, k4_xboole_0(A_117, B_118)))), inference(resolution, [status(thm)], [c_8, c_546])).
% 21.67/13.15  tff(c_792, plain, (![A_117, B_118, B_8]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_117, B_118), B_8), A_117))), inference(resolution, [status(thm)], [c_8, c_753])).
% 21.67/13.15  tff(c_1432, plain, (![A_153, B_154, C_155]: (r1_tarski(A_153, k2_xboole_0(B_154, C_155)) | ~r1_tarski(k4_xboole_0(A_153, B_154), C_155))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.67/13.15  tff(c_1630, plain, (![A_164, B_165, B_166]: (r1_tarski(k4_xboole_0(A_164, B_165), k2_xboole_0(B_166, A_164)))), inference(resolution, [status(thm)], [c_792, c_1432])).
% 21.67/13.15  tff(c_18, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k2_xboole_0(B_18, C_19)) | ~r1_tarski(k4_xboole_0(A_17, B_18), C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.67/13.15  tff(c_1962, plain, (![A_183, B_184, B_185]: (r1_tarski(A_183, k2_xboole_0(B_184, k2_xboole_0(B_185, A_183))))), inference(resolution, [status(thm)], [c_1630, c_18])).
% 21.67/13.15  tff(c_2000, plain, (![A_183, B_185, A_80]: (r1_tarski(A_183, k2_xboole_0(k2_xboole_0(B_185, A_183), A_80)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_1962])).
% 21.67/13.15  tff(c_793, plain, (![A_119, B_120, C_121]: (r1_tarski(k4_xboole_0(A_119, B_120), C_121) | ~r1_tarski(A_119, k2_xboole_0(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.67/13.15  tff(c_10, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k4_xboole_0(B_10, A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.67/13.15  tff(c_8309, plain, (![A_351, B_352, B_353]: (k4_xboole_0(A_351, B_352)=k1_xboole_0 | ~r1_tarski(A_351, k2_xboole_0(B_352, k4_xboole_0(B_353, k4_xboole_0(A_351, B_352)))))), inference(resolution, [status(thm)], [c_793, c_10])).
% 21.67/13.15  tff(c_9237, plain, (![A_364, B_365]: (k4_xboole_0(A_364, k2_xboole_0(B_365, A_364))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2000, c_8309])).
% 21.67/13.15  tff(c_9317, plain, (![A_364, B_365]: (k3_xboole_0(A_364, k2_xboole_0(B_365, A_364))=k4_xboole_0(A_364, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9237, c_20])).
% 21.67/13.15  tff(c_9389, plain, (![A_364, B_365]: (k3_xboole_0(A_364, k2_xboole_0(B_365, A_364))=A_364)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_9317])).
% 21.67/13.15  tff(c_2853, plain, (![A_230, C_231]: (r1_tarski(A_230, C_231) | ~r1_tarski(A_230, k2_xboole_0(k1_xboole_0, C_231)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_793])).
% 21.67/13.15  tff(c_3236, plain, (![C_237, B_238]: (r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0, C_237), B_238), C_237))), inference(resolution, [status(thm)], [c_8, c_2853])).
% 21.67/13.15  tff(c_3485, plain, (![C_246, B_247]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_246), k2_xboole_0(B_247, C_246)))), inference(resolution, [status(thm)], [c_3236, c_18])).
% 21.67/13.15  tff(c_3535, plain, (![A_80, B_81]: (r1_tarski(k2_xboole_0(k1_xboole_0, A_80), k2_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_3485])).
% 21.67/13.15  tff(c_8523, plain, (![A_355]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, A_355), A_355)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3535, c_8309])).
% 21.67/13.15  tff(c_8584, plain, (![A_355]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, A_355), k1_xboole_0)=k3_xboole_0(k2_xboole_0(k1_xboole_0, A_355), A_355))), inference(superposition, [status(thm), theory('equality')], [c_8523, c_20])).
% 21.67/13.15  tff(c_30303, plain, (![A_583]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, A_583), A_583)=k2_xboole_0(k1_xboole_0, A_583))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_8584])).
% 21.67/13.15  tff(c_138, plain, (![A_70, B_71]: (k1_setfam_1(k2_tarski(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.67/13.15  tff(c_240, plain, (![B_84, A_85]: (k1_setfam_1(k2_tarski(B_84, A_85))=k3_xboole_0(A_85, B_84))), inference(superposition, [status(thm), theory('equality')], [c_22, c_138])).
% 21.67/13.15  tff(c_40, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.67/13.15  tff(c_246, plain, (![B_84, A_85]: (k3_xboole_0(B_84, A_85)=k3_xboole_0(A_85, B_84))), inference(superposition, [status(thm), theory('equality')], [c_240, c_40])).
% 21.67/13.15  tff(c_30528, plain, (![A_583]: (k3_xboole_0(A_583, k2_xboole_0(k1_xboole_0, A_583))=k2_xboole_0(k1_xboole_0, A_583))), inference(superposition, [status(thm), theory('equality')], [c_30303, c_246])).
% 21.67/13.15  tff(c_30632, plain, (![A_583]: (k2_xboole_0(k1_xboole_0, A_583)=A_583)), inference(demodulation, [status(thm), theory('equality')], [c_9389, c_30528])).
% 21.67/13.15  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.67/13.15  tff(c_425, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k3_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.67/13.15  tff(c_460, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_425])).
% 21.67/13.15  tff(c_468, plain, (![A_97]: (k4_xboole_0(A_97, A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_460])).
% 21.67/13.15  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.67/13.15  tff(c_659, plain, (![A_111]: (k2_xboole_0(A_111, k1_xboole_0)=k2_xboole_0(A_111, A_111))), inference(superposition, [status(thm), theory('equality')], [c_468, c_12])).
% 21.67/13.15  tff(c_668, plain, (![A_111]: (k2_xboole_0(k1_xboole_0, A_111)=k2_xboole_0(A_111, A_111))), inference(superposition, [status(thm), theory('equality')], [c_659, c_189])).
% 21.67/13.15  tff(c_30677, plain, (![A_111]: (k2_xboole_0(A_111, A_111)=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_30632, c_668])).
% 21.67/13.15  tff(c_479, plain, (![A_97]: (k2_xboole_0(A_97, k1_xboole_0)=k2_xboole_0(A_97, A_97))), inference(superposition, [status(thm), theory('equality')], [c_468, c_12])).
% 21.67/13.15  tff(c_31149, plain, (![A_97]: (k2_xboole_0(A_97, k1_xboole_0)=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_30677, c_479])).
% 21.67/13.15  tff(c_1670, plain, (![A_80, B_165, B_81]: (r1_tarski(k4_xboole_0(A_80, B_165), k2_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_1630])).
% 21.67/13.15  tff(c_8650, plain, (![A_356, B_357]: (k4_xboole_0(k4_xboole_0(A_356, B_357), A_356)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1670, c_8309])).
% 21.67/13.15  tff(c_8709, plain, (![A_356, B_357]: (k2_xboole_0(A_356, k4_xboole_0(A_356, B_357))=k2_xboole_0(A_356, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8650, c_12])).
% 21.67/13.15  tff(c_35830, plain, (![A_642, B_643]: (k2_xboole_0(A_642, k4_xboole_0(A_642, B_643))=A_642)), inference(demodulation, [status(thm), theory('equality')], [c_31149, c_8709])).
% 21.67/13.15  tff(c_36175, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1957, c_35830])).
% 21.67/13.15  tff(c_2401, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1957, c_8])).
% 21.67/13.15  tff(c_158, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | ~m1_subset_1(A_74, k1_zfmisc_1(B_75)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 21.67/13.15  tff(c_162, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_158])).
% 21.67/13.15  tff(c_556, plain, (![A_100]: (r1_tarski(A_100, u1_struct_0('#skF_1')) | ~r1_tarski(A_100, '#skF_2'))), inference(resolution, [status(thm)], [c_162, c_546])).
% 21.67/13.15  tff(c_44, plain, (![A_43, B_44]: (m1_subset_1(A_43, k1_zfmisc_1(B_44)) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_93])).
% 21.67/13.15  tff(c_2787, plain, (![A_224, B_225, C_226]: (k4_subset_1(A_224, B_225, C_226)=k2_xboole_0(B_225, C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(A_224)) | ~m1_subset_1(B_225, k1_zfmisc_1(A_224)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 21.67/13.15  tff(c_13081, plain, (![B_397, B_398, A_399]: (k4_subset_1(B_397, B_398, A_399)=k2_xboole_0(B_398, A_399) | ~m1_subset_1(B_398, k1_zfmisc_1(B_397)) | ~r1_tarski(A_399, B_397))), inference(resolution, [status(thm)], [c_44, c_2787])).
% 21.67/13.15  tff(c_13235, plain, (![A_401]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_401)=k2_xboole_0('#skF_2', A_401) | ~r1_tarski(A_401, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_60, c_13081])).
% 21.67/13.15  tff(c_15685, plain, (![A_429]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_429)=k2_xboole_0('#skF_2', A_429) | ~r1_tarski(A_429, '#skF_2'))), inference(resolution, [status(thm)], [c_556, c_13235])).
% 21.67/13.15  tff(c_3804, plain, (![A_254, B_255]: (k4_subset_1(u1_struct_0(A_254), B_255, k2_tops_1(A_254, B_255))=k2_pre_topc(A_254, B_255) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_136])).
% 21.67/13.15  tff(c_3814, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_3804])).
% 21.67/13.15  tff(c_3820, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3814])).
% 21.67/13.15  tff(c_15697, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15685, c_3820])).
% 21.67/13.15  tff(c_15735, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2401, c_15697])).
% 21.67/13.15  tff(c_37001, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36175, c_15735])).
% 21.67/13.15  tff(c_37003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3182, c_37001])).
% 21.67/13.15  tff(c_37004, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 21.67/13.15  tff(c_37301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37004, c_137])).
% 21.67/13.15  tff(c_37302, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 21.67/13.15  tff(c_37420, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37302, c_66])).
% 21.67/13.15  tff(c_39884, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_39760, c_37420])).
% 21.67/13.15  tff(c_75603, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_41416, c_39884])).
% 21.67/13.15  tff(c_40516, plain, (![A_817, B_818]: (k2_pre_topc(A_817, B_818)=B_818 | ~v4_pre_topc(B_818, A_817) | ~m1_subset_1(B_818, k1_zfmisc_1(u1_struct_0(A_817))) | ~l1_pre_topc(A_817))), inference(cnfTransformation, [status(thm)], [f_108])).
% 21.67/13.15  tff(c_40530, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_40516])).
% 21.67/13.15  tff(c_40536, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_37302, c_40530])).
% 21.67/13.15  tff(c_41497, plain, (![A_860, B_861]: (k4_subset_1(u1_struct_0(A_860), B_861, k2_tops_1(A_860, B_861))=k2_pre_topc(A_860, B_861) | ~m1_subset_1(B_861, k1_zfmisc_1(u1_struct_0(A_860))) | ~l1_pre_topc(A_860))), inference(cnfTransformation, [status(thm)], [f_136])).
% 21.67/13.15  tff(c_41507, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_41497])).
% 21.67/13.15  tff(c_41513, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40536, c_41507])).
% 21.67/13.15  tff(c_50, plain, (![A_48, B_49]: (m1_subset_1(k2_tops_1(A_48, B_49), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_114])).
% 21.67/13.15  tff(c_40804, plain, (![A_830, B_831, C_832]: (k4_subset_1(A_830, B_831, C_832)=k2_xboole_0(B_831, C_832) | ~m1_subset_1(C_832, k1_zfmisc_1(A_830)) | ~m1_subset_1(B_831, k1_zfmisc_1(A_830)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 21.67/13.15  tff(c_68915, plain, (![A_1202, B_1203, B_1204]: (k4_subset_1(u1_struct_0(A_1202), B_1203, k2_tops_1(A_1202, B_1204))=k2_xboole_0(B_1203, k2_tops_1(A_1202, B_1204)) | ~m1_subset_1(B_1203, k1_zfmisc_1(u1_struct_0(A_1202))) | ~m1_subset_1(B_1204, k1_zfmisc_1(u1_struct_0(A_1202))) | ~l1_pre_topc(A_1202))), inference(resolution, [status(thm)], [c_50, c_40804])).
% 21.67/13.15  tff(c_68931, plain, (![B_1204]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_1204))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_1204)) | ~m1_subset_1(B_1204, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_68915])).
% 21.67/13.15  tff(c_98821, plain, (![B_1410]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_1410))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_1410)) | ~m1_subset_1(B_1410, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_68931])).
% 21.67/13.15  tff(c_98844, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_98821])).
% 21.67/13.15  tff(c_98853, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_41513, c_98844])).
% 21.67/13.15  tff(c_37457, plain, (![A_676, B_677]: (k4_xboole_0(A_676, k4_xboole_0(A_676, B_677))=k3_xboole_0(A_676, B_677))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.67/13.15  tff(c_37478, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_37457])).
% 21.67/13.15  tff(c_37482, plain, (![A_678]: (k4_xboole_0(A_678, A_678)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_37478])).
% 21.67/13.15  tff(c_37487, plain, (![A_678]: (k4_xboole_0(A_678, k1_xboole_0)=k3_xboole_0(A_678, A_678))), inference(superposition, [status(thm), theory('equality')], [c_37482, c_20])).
% 21.67/13.15  tff(c_37505, plain, (![A_678]: (k3_xboole_0(A_678, A_678)=A_678)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_37487])).
% 21.67/13.15  tff(c_37329, plain, (![A_667, B_668]: (k3_tarski(k2_tarski(A_667, B_668))=k2_xboole_0(A_667, B_668))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.67/13.15  tff(c_37757, plain, (![B_694, A_695]: (k3_tarski(k2_tarski(B_694, A_695))=k2_xboole_0(A_695, B_694))), inference(superposition, [status(thm), theory('equality')], [c_22, c_37329])).
% 21.67/13.15  tff(c_37763, plain, (![B_694, A_695]: (k2_xboole_0(B_694, A_695)=k2_xboole_0(A_695, B_694))), inference(superposition, [status(thm), theory('equality')], [c_37757, c_24])).
% 21.67/13.15  tff(c_37827, plain, (![A_698, C_699, B_700]: (r1_tarski(A_698, C_699) | ~r1_tarski(B_700, C_699) | ~r1_tarski(A_698, B_700))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.67/13.15  tff(c_37912, plain, (![A_705, A_706, B_707]: (r1_tarski(A_705, A_706) | ~r1_tarski(A_705, k4_xboole_0(A_706, B_707)))), inference(resolution, [status(thm)], [c_8, c_37827])).
% 21.67/13.15  tff(c_37951, plain, (![A_706, B_707, B_8]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_706, B_707), B_8), A_706))), inference(resolution, [status(thm)], [c_8, c_37912])).
% 21.67/13.15  tff(c_38781, plain, (![A_750, B_751, C_752]: (r1_tarski(A_750, k2_xboole_0(B_751, C_752)) | ~r1_tarski(k4_xboole_0(A_750, B_751), C_752))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.67/13.15  tff(c_39503, plain, (![A_777, B_778, B_779]: (r1_tarski(k4_xboole_0(A_777, B_778), k2_xboole_0(B_779, A_777)))), inference(resolution, [status(thm)], [c_37951, c_38781])).
% 21.67/13.15  tff(c_40451, plain, (![A_814, B_815, B_816]: (r1_tarski(A_814, k2_xboole_0(B_815, k2_xboole_0(B_816, A_814))))), inference(resolution, [status(thm)], [c_39503, c_18])).
% 21.67/13.15  tff(c_40490, plain, (![A_814, B_816, B_694]: (r1_tarski(A_814, k2_xboole_0(k2_xboole_0(B_816, A_814), B_694)))), inference(superposition, [status(thm), theory('equality')], [c_37763, c_40451])).
% 21.67/13.15  tff(c_38316, plain, (![A_730, B_731, C_732]: (r1_tarski(k4_xboole_0(A_730, B_731), C_732) | ~r1_tarski(A_730, k2_xboole_0(B_731, C_732)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.67/13.15  tff(c_48354, plain, (![A_982, B_983, B_984]: (k4_xboole_0(A_982, B_983)=k1_xboole_0 | ~r1_tarski(A_982, k2_xboole_0(B_983, k4_xboole_0(B_984, k4_xboole_0(A_982, B_983)))))), inference(resolution, [status(thm)], [c_38316, c_10])).
% 21.67/13.15  tff(c_49153, plain, (![A_989, B_990]: (k4_xboole_0(A_989, k2_xboole_0(B_990, A_989))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40490, c_48354])).
% 21.67/13.15  tff(c_49247, plain, (![A_989, B_990]: (k3_xboole_0(A_989, k2_xboole_0(B_990, A_989))=k4_xboole_0(A_989, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_49153, c_20])).
% 21.67/13.15  tff(c_49325, plain, (![A_989, B_990]: (k3_xboole_0(A_989, k2_xboole_0(B_990, A_989))=A_989)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_49247])).
% 21.67/13.15  tff(c_37314, plain, (![A_665, B_666]: (k1_setfam_1(k2_tarski(A_665, B_666))=k3_xboole_0(A_665, B_666))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.67/13.15  tff(c_37349, plain, (![B_671, A_672]: (k1_setfam_1(k2_tarski(B_671, A_672))=k3_xboole_0(A_672, B_671))), inference(superposition, [status(thm), theory('equality')], [c_22, c_37314])).
% 21.67/13.15  tff(c_37355, plain, (![B_671, A_672]: (k3_xboole_0(B_671, A_672)=k3_xboole_0(A_672, B_671))), inference(superposition, [status(thm), theory('equality')], [c_37349, c_40])).
% 21.67/13.15  tff(c_40323, plain, (![B_809, B_810, A_811]: (r1_tarski(k4_xboole_0(B_809, B_810), k2_xboole_0(B_809, A_811)))), inference(superposition, [status(thm), theory('equality')], [c_37763, c_39503])).
% 21.67/13.15  tff(c_40370, plain, (![A_20, B_21, A_811]: (r1_tarski(k3_xboole_0(A_20, B_21), k2_xboole_0(A_20, A_811)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_40323])).
% 21.67/13.15  tff(c_49491, plain, (![A_992, B_993]: (k4_xboole_0(k3_xboole_0(A_992, B_993), A_992)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40370, c_48354])).
% 21.67/13.15  tff(c_49665, plain, (![A_996, B_997]: (k4_xboole_0(k3_xboole_0(A_996, B_997), B_997)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_37355, c_49491])).
% 21.67/13.15  tff(c_49738, plain, (![A_996, B_997]: (k4_xboole_0(k3_xboole_0(A_996, B_997), k1_xboole_0)=k3_xboole_0(k3_xboole_0(A_996, B_997), B_997))), inference(superposition, [status(thm), theory('equality')], [c_49665, c_20])).
% 21.67/13.15  tff(c_71389, plain, (![A_1226, B_1227]: (k3_xboole_0(k3_xboole_0(A_1226, B_1227), B_1227)=k3_xboole_0(A_1226, B_1227))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_49738])).
% 21.67/13.15  tff(c_74092, plain, (![A_1261, B_1262]: (k3_xboole_0(k3_xboole_0(A_1261, B_1262), A_1261)=k3_xboole_0(B_1262, A_1261))), inference(superposition, [status(thm), theory('equality')], [c_37355, c_71389])).
% 21.67/13.15  tff(c_74441, plain, (![B_990, A_989]: (k3_xboole_0(k2_xboole_0(B_990, A_989), A_989)=k3_xboole_0(A_989, A_989))), inference(superposition, [status(thm), theory('equality')], [c_49325, c_74092])).
% 21.67/13.15  tff(c_74556, plain, (![B_990, A_989]: (k3_xboole_0(k2_xboole_0(B_990, A_989), A_989)=A_989)), inference(demodulation, [status(thm), theory('equality')], [c_37505, c_74441])).
% 21.67/13.15  tff(c_98884, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_98853, c_74556])).
% 21.67/13.15  tff(c_99003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75603, c_98884])).
% 21.67/13.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.67/13.15  
% 21.67/13.15  Inference rules
% 21.67/13.15  ----------------------
% 21.67/13.15  #Ref     : 0
% 21.67/13.15  #Sup     : 23658
% 21.67/13.15  #Fact    : 0
% 21.67/13.15  #Define  : 0
% 21.67/13.15  #Split   : 12
% 21.67/13.15  #Chain   : 0
% 21.67/13.15  #Close   : 0
% 21.67/13.15  
% 21.67/13.15  Ordering : KBO
% 21.67/13.15  
% 21.67/13.15  Simplification rules
% 21.67/13.15  ----------------------
% 21.67/13.15  #Subsume      : 1292
% 21.67/13.15  #Demod        : 22998
% 21.67/13.15  #Tautology    : 15750
% 21.67/13.15  #SimpNegUnit  : 8
% 21.67/13.15  #BackRed      : 126
% 21.67/13.15  
% 21.67/13.15  #Partial instantiations: 0
% 21.67/13.15  #Strategies tried      : 1
% 21.67/13.15  
% 21.67/13.15  Timing (in seconds)
% 21.67/13.15  ----------------------
% 21.67/13.15  Preprocessing        : 0.49
% 21.67/13.15  Parsing              : 0.23
% 21.67/13.15  CNF conversion       : 0.04
% 21.67/13.15  Main loop            : 11.81
% 21.67/13.15  Inferencing          : 1.69
% 21.67/13.15  Reduction            : 6.93
% 21.67/13.15  Demodulation         : 6.15
% 21.67/13.15  BG Simplification    : 0.18
% 21.67/13.15  Subsumption          : 2.48
% 21.67/13.15  Abstraction          : 0.29
% 21.67/13.15  MUC search           : 0.00
% 21.67/13.15  Cooper               : 0.00
% 21.67/13.15  Total                : 12.36
% 21.67/13.15  Index Insertion      : 0.00
% 21.67/13.15  Index Deletion       : 0.00
% 21.67/13.15  Index Matching       : 0.00
% 21.67/13.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

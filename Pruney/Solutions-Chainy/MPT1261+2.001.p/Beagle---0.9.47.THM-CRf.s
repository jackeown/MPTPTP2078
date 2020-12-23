%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:11 EST 2020

% Result     : Theorem 20.35s
% Output     : CNFRefutation 20.44s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 348 expanded)
%              Number of leaves         :   52 ( 136 expanded)
%              Depth                    :   16
%              Number of atoms          :  219 ( 550 expanded)
%              Number of equality atoms :  104 ( 240 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_167,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_155,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_107,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_31840,plain,(
    ! [A_661,B_662,C_663] :
      ( k7_subset_1(A_661,B_662,C_663) = k4_xboole_0(B_662,C_663)
      | ~ m1_subset_1(B_662,k1_zfmisc_1(A_661)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_31849,plain,(
    ! [C_663] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_663) = k4_xboole_0('#skF_3',C_663) ),
    inference(resolution,[status(thm)],[c_70,c_31840])).

tff(c_82,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_178,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_76,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_284,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_285,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | ~ m1_subset_1(A_94,k1_zfmisc_1(B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_293,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_285])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_6003,plain,(
    ! [A_293,B_294] :
      ( k4_subset_1(u1_struct_0(A_293),B_294,k2_tops_1(A_293,B_294)) = k2_pre_topc(A_293,B_294)
      | ~ m1_subset_1(B_294,k1_zfmisc_1(u1_struct_0(A_293)))
      | ~ l1_pre_topc(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6013,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6003])).

tff(c_6019,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6013])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3082,plain,(
    ! [A_238,B_239,C_240] :
      ( k7_subset_1(A_238,B_239,C_240) = k4_xboole_0(B_239,C_240)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(A_238)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3154,plain,(
    ! [C_244] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_244) = k4_xboole_0('#skF_3',C_244) ),
    inference(resolution,[status(thm)],[c_70,c_3082])).

tff(c_3166,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_3154])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4533,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3166,c_20])).

tff(c_2104,plain,(
    ! [A_193,B_194,C_195] :
      ( r1_tarski(k4_xboole_0(A_193,B_194),C_195)
      | ~ r1_tarski(A_193,k2_xboole_0(B_194,C_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_131,plain,(
    ! [B_84,A_85] : k2_xboole_0(B_84,A_85) = k2_xboole_0(A_85,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_147,plain,(
    ! [A_85] : k2_xboole_0(k1_xboole_0,A_85) = A_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_14])).

tff(c_533,plain,(
    ! [A_108,B_109] : k2_xboole_0(A_108,k4_xboole_0(B_109,A_108)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_540,plain,(
    ! [B_109] : k4_xboole_0(B_109,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_147])).

tff(c_558,plain,(
    ! [B_109] : k4_xboole_0(B_109,k1_xboole_0) = B_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_540])).

tff(c_179,plain,(
    ! [A_86] : k2_xboole_0(k1_xboole_0,A_86) = A_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_14])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_192,plain,(
    ! [B_17] : k3_xboole_0(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_18])).

tff(c_332,plain,(
    ! [A_100,B_101] : k4_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_347,plain,(
    ! [B_17] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_332])).

tff(c_609,plain,(
    ! [B_114] : k4_xboole_0(k1_xboole_0,B_114) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_347])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k4_xboole_0(B_21,A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_625,plain,(
    ! [B_114] :
      ( k1_xboole_0 = B_114
      | ~ r1_tarski(B_114,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_22])).

tff(c_2122,plain,(
    ! [A_193,B_194] :
      ( k4_xboole_0(A_193,B_194) = k1_xboole_0
      | ~ r1_tarski(A_193,k2_xboole_0(B_194,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_2104,c_625])).

tff(c_2146,plain,(
    ! [A_193,B_194] :
      ( k4_xboole_0(A_193,B_194) = k1_xboole_0
      | ~ r1_tarski(A_193,B_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2122])).

tff(c_4550,plain,(
    k4_xboole_0(k2_tops_1('#skF_2','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4533,c_2146])).

tff(c_24,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4612,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4550,c_24])).

tff(c_4636,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4612])).

tff(c_1386,plain,(
    ! [A_163,B_164,C_165] :
      ( r1_tarski(A_163,k2_xboole_0(B_164,C_165))
      | ~ r1_tarski(k4_xboole_0(A_163,B_164),C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1431,plain,(
    ! [A_166,B_167] : r1_tarski(A_166,k2_xboole_0(B_167,A_166)) ),
    inference(resolution,[status(thm)],[c_20,c_1386])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(A_13,C_15)
      | ~ r1_tarski(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1481,plain,(
    ! [A_13,B_167,A_166] :
      ( r1_tarski(A_13,k2_xboole_0(B_167,A_166))
      | ~ r1_tarski(A_13,A_166) ) ),
    inference(resolution,[status(thm)],[c_1431,c_16])).

tff(c_30,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_19953,plain,(
    ! [A_443,B_444,C_445] :
      ( r1_tarski(k4_xboole_0(A_443,B_444),C_445)
      | ~ r1_tarski(A_443,k2_xboole_0(k3_xboole_0(A_443,B_444),C_445)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2104])).

tff(c_20209,plain,(
    ! [A_446,B_447,A_448] :
      ( r1_tarski(k4_xboole_0(A_446,B_447),A_448)
      | ~ r1_tarski(A_446,A_448) ) ),
    inference(resolution,[status(thm)],[c_1481,c_19953])).

tff(c_20306,plain,(
    ! [A_448] :
      ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),A_448)
      | ~ r1_tarski('#skF_3',A_448) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3166,c_20209])).

tff(c_56,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(A_58,k1_zfmisc_1(B_59))
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4640,plain,(
    ! [A_273,B_274,C_275] :
      ( k4_subset_1(A_273,B_274,C_275) = k2_xboole_0(B_274,C_275)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(A_273))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(A_273)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28418,plain,(
    ! [B_520,B_521,A_522] :
      ( k4_subset_1(B_520,B_521,A_522) = k2_xboole_0(B_521,A_522)
      | ~ m1_subset_1(B_521,k1_zfmisc_1(B_520))
      | ~ r1_tarski(A_522,B_520) ) ),
    inference(resolution,[status(thm)],[c_56,c_4640])).

tff(c_28437,plain,(
    ! [A_523] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_523) = k2_xboole_0('#skF_3',A_523)
      | ~ r1_tarski(A_523,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_70,c_28418])).

tff(c_28458,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_20306,c_28437])).

tff(c_28611,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_6019,c_4636,c_28458])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_3506,plain,(
    ! [A_258,B_259] :
      ( v4_pre_topc(k2_pre_topc(A_258,B_259),A_258)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3514,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_3506])).

tff(c_3519,plain,(
    v4_pre_topc(k2_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3514])).

tff(c_28668,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28611,c_3519])).

tff(c_28670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_28668])).

tff(c_28671,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_28970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_28671])).

tff(c_28971,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_29092,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28971,c_76])).

tff(c_32057,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_29092])).

tff(c_33609,plain,(
    ! [A_720,B_721] :
      ( r1_tarski(k2_tops_1(A_720,B_721),B_721)
      | ~ v4_pre_topc(B_721,A_720)
      | ~ m1_subset_1(B_721,k1_zfmisc_1(u1_struct_0(A_720)))
      | ~ l1_pre_topc(A_720) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_33619,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_33609])).

tff(c_33625,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_28971,c_33619])).

tff(c_34156,plain,(
    ! [A_737,B_738] :
      ( k7_subset_1(u1_struct_0(A_737),B_738,k2_tops_1(A_737,B_738)) = k1_tops_1(A_737,B_738)
      | ~ m1_subset_1(B_738,k1_zfmisc_1(u1_struct_0(A_737)))
      | ~ l1_pre_topc(A_737) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_34166,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_34156])).

tff(c_34172,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_31849,c_34166])).

tff(c_29971,plain,(
    ! [A_612,B_613] :
      ( k4_xboole_0(A_612,B_613) = k3_subset_1(A_612,B_613)
      | ~ m1_subset_1(B_613,k1_zfmisc_1(A_612)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34782,plain,(
    ! [B_746,A_747] :
      ( k4_xboole_0(B_746,A_747) = k3_subset_1(B_746,A_747)
      | ~ r1_tarski(A_747,B_746) ) ),
    inference(resolution,[status(thm)],[c_56,c_29971])).

tff(c_34824,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k3_subset_1('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_33625,c_34782])).

tff(c_34941,plain,(
    k3_subset_1('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34172,c_34824])).

tff(c_30786,plain,(
    ! [A_636,B_637] :
      ( k3_subset_1(A_636,k3_subset_1(A_636,B_637)) = B_637
      | ~ m1_subset_1(B_637,k1_zfmisc_1(A_636)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30791,plain,(
    ! [B_59,A_58] :
      ( k3_subset_1(B_59,k3_subset_1(B_59,A_58)) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_56,c_30786])).

tff(c_38782,plain,
    ( k3_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34941,c_30791])).

tff(c_38790,plain,(
    k3_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33625,c_38782])).

tff(c_52,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,(
    ! [B_36,A_35] : k2_tarski(B_36,A_35) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29076,plain,(
    ! [A_546,B_547] : k1_setfam_1(k2_tarski(A_546,B_547)) = k3_xboole_0(A_546,B_547) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_29104,plain,(
    ! [B_554,A_555] : k1_setfam_1(k2_tarski(B_554,A_555)) = k3_xboole_0(A_555,B_554) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_29076])).

tff(c_29116,plain,(
    ! [B_57,A_56] : k3_xboole_0(B_57,A_56) = k3_xboole_0(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_29104])).

tff(c_34229,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34172,c_20])).

tff(c_29803,plain,(
    ! [A_605,B_606,C_607] :
      ( r1_tarski(k4_xboole_0(A_605,B_606),C_607)
      | ~ r1_tarski(A_605,k2_xboole_0(B_606,C_607)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_29127,plain,(
    ! [A_556,B_557] : k2_xboole_0(A_556,k4_xboole_0(B_557,A_556)) = k2_xboole_0(A_556,B_557) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29134,plain,(
    ! [B_557] : k4_xboole_0(B_557,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_557) ),
    inference(superposition,[status(thm),theory(equality)],[c_29127,c_147])).

tff(c_29143,plain,(
    ! [B_557] : k4_xboole_0(B_557,k1_xboole_0) = B_557 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_29134])).

tff(c_29168,plain,(
    ! [B_560,A_561] : k3_xboole_0(B_560,A_561) = k3_xboole_0(A_561,B_560) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_29104])).

tff(c_28973,plain,(
    ! [A_542] : k2_xboole_0(k1_xboole_0,A_542) = A_542 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_14])).

tff(c_28986,plain,(
    ! [B_17] : k3_xboole_0(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28973,c_18])).

tff(c_29184,plain,(
    ! [B_560] : k3_xboole_0(B_560,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_29168,c_28986])).

tff(c_29308,plain,(
    ! [A_567,B_568] : k5_xboole_0(A_567,k3_xboole_0(A_567,B_568)) = k4_xboole_0(A_567,B_568) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29317,plain,(
    ! [B_560] : k5_xboole_0(B_560,k1_xboole_0) = k4_xboole_0(B_560,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_29184,c_29308])).

tff(c_29329,plain,(
    ! [B_560] : k5_xboole_0(B_560,k1_xboole_0) = B_560 ),
    inference(demodulation,[status(thm),theory(equality)],[c_29143,c_29317])).

tff(c_29326,plain,(
    ! [B_17] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_28986,c_29308])).

tff(c_29340,plain,(
    ! [B_570] : k4_xboole_0(k1_xboole_0,B_570) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_29329,c_29326])).

tff(c_29352,plain,(
    ! [B_570] :
      ( k1_xboole_0 = B_570
      | ~ r1_tarski(B_570,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29340,c_22])).

tff(c_29815,plain,(
    ! [A_605,B_606] :
      ( k4_xboole_0(A_605,B_606) = k1_xboole_0
      | ~ r1_tarski(A_605,k2_xboole_0(B_606,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_29803,c_29352])).

tff(c_29836,plain,(
    ! [A_605,B_606] :
      ( k4_xboole_0(A_605,B_606) = k1_xboole_0
      | ~ r1_tarski(A_605,B_606) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_29815])).

tff(c_34244,plain,(
    k4_xboole_0(k1_tops_1('#skF_2','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34229,c_29836])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_29389,plain,(
    ! [A_574,B_575] : k4_xboole_0(A_574,k3_xboole_0(A_574,B_575)) = k4_xboole_0(A_574,B_575) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_29399,plain,(
    ! [A_574,B_575] : k2_xboole_0(k3_xboole_0(A_574,B_575),k4_xboole_0(A_574,B_575)) = k2_xboole_0(k3_xboole_0(A_574,B_575),A_574) ),
    inference(superposition,[status(thm),theory(equality)],[c_29389,c_24])).

tff(c_29427,plain,(
    ! [A_574,B_575] : k2_xboole_0(k3_xboole_0(A_574,B_575),k4_xboole_0(A_574,B_575)) = A_574 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_29399])).

tff(c_31421,plain,(
    ! [A_652,B_653,C_654] : k2_xboole_0(k2_xboole_0(A_652,B_653),C_654) = k2_xboole_0(A_652,k2_xboole_0(B_653,C_654)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36819,plain,(
    ! [C_771,A_772,B_773] : k2_xboole_0(C_771,k2_xboole_0(A_772,B_773)) = k2_xboole_0(A_772,k2_xboole_0(B_773,C_771)) ),
    inference(superposition,[status(thm),theory(equality)],[c_31421,c_2])).

tff(c_40569,plain,(
    ! [A_802,C_803] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_802,C_803)) = k2_xboole_0(C_803,A_802) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_36819])).

tff(c_40777,plain,(
    ! [A_574,B_575] : k2_xboole_0(k4_xboole_0(A_574,B_575),k3_xboole_0(A_574,B_575)) = k2_xboole_0(k1_xboole_0,A_574) ),
    inference(superposition,[status(thm),theory(equality)],[c_29427,c_40569])).

tff(c_45140,plain,(
    ! [A_847,B_848] : k2_xboole_0(k4_xboole_0(A_847,B_848),k3_xboole_0(A_847,B_848)) = A_847 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_40777])).

tff(c_45281,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_tops_1('#skF_2','#skF_3'),'#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34244,c_45140])).

tff(c_45394,plain,(
    k3_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_29116,c_45281])).

tff(c_30101,plain,(
    ! [A_614,B_615,C_616] :
      ( r1_tarski(A_614,k2_xboole_0(B_615,C_616))
      | ~ r1_tarski(k4_xboole_0(A_614,B_615),C_616) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30161,plain,(
    ! [A_617,B_618] : r1_tarski(A_617,k2_xboole_0(B_618,A_617)) ),
    inference(resolution,[status(thm)],[c_20,c_30101])).

tff(c_30196,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_30161])).

tff(c_34890,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k3_subset_1(A_16,k3_xboole_0(A_16,B_17)) ),
    inference(resolution,[status(thm)],[c_30196,c_34782])).

tff(c_34965,plain,(
    ! [A_16,B_17] : k3_subset_1(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34890])).

tff(c_82777,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k3_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45394,c_34965])).

tff(c_82907,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38790,c_82777])).

tff(c_82909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32057,c_82907])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n021.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 16:31:49 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.35/11.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.44/11.81  
% 20.44/11.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.44/11.81  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 20.44/11.81  
% 20.44/11.81  %Foreground sorts:
% 20.44/11.81  
% 20.44/11.81  
% 20.44/11.81  %Background operators:
% 20.44/11.81  
% 20.44/11.81  
% 20.44/11.81  %Foreground operators:
% 20.44/11.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.44/11.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.44/11.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.44/11.81  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 20.44/11.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.44/11.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.44/11.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.44/11.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.44/11.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.44/11.81  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 20.44/11.81  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 20.44/11.81  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 20.44/11.81  tff('#skF_2', type, '#skF_2': $i).
% 20.44/11.81  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 20.44/11.81  tff('#skF_3', type, '#skF_3': $i).
% 20.44/11.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.44/11.81  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 20.44/11.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.44/11.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.44/11.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 20.44/11.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.44/11.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.44/11.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.44/11.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.44/11.81  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 20.44/11.81  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 20.44/11.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.44/11.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.44/11.81  
% 20.44/11.83  tff(f_167, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 20.44/11.83  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 20.44/11.83  tff(f_111, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 20.44/11.83  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 20.44/11.83  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 20.44/11.84  tff(f_50, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 20.44/11.84  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 20.44/11.84  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 20.44/11.84  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 20.44/11.84  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 20.44/11.84  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 20.44/11.84  tff(f_54, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 20.44/11.84  tff(f_64, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 20.44/11.84  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 20.44/11.84  tff(f_97, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 20.44/11.84  tff(f_125, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 20.44/11.84  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 20.44/11.84  tff(f_155, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 20.44/11.84  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 20.44/11.84  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 20.44/11.84  tff(f_107, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 20.44/11.84  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 20.44/11.84  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 20.44/11.84  tff(f_68, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 20.44/11.84  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 20.44/11.84  tff(c_31840, plain, (![A_661, B_662, C_663]: (k7_subset_1(A_661, B_662, C_663)=k4_xboole_0(B_662, C_663) | ~m1_subset_1(B_662, k1_zfmisc_1(A_661)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 20.44/11.84  tff(c_31849, plain, (![C_663]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_663)=k4_xboole_0('#skF_3', C_663))), inference(resolution, [status(thm)], [c_70, c_31840])).
% 20.44/11.84  tff(c_82, plain, (v4_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 20.44/11.84  tff(c_178, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_82])).
% 20.44/11.84  tff(c_76, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 20.44/11.84  tff(c_284, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_76])).
% 20.44/11.84  tff(c_285, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | ~m1_subset_1(A_94, k1_zfmisc_1(B_95)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 20.44/11.84  tff(c_293, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_70, c_285])).
% 20.44/11.84  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 20.44/11.84  tff(c_6003, plain, (![A_293, B_294]: (k4_subset_1(u1_struct_0(A_293), B_294, k2_tops_1(A_293, B_294))=k2_pre_topc(A_293, B_294) | ~m1_subset_1(B_294, k1_zfmisc_1(u1_struct_0(A_293))) | ~l1_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_139])).
% 20.44/11.84  tff(c_6013, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_6003])).
% 20.44/11.84  tff(c_6019, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6013])).
% 20.44/11.84  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_40])).
% 20.44/11.84  tff(c_3082, plain, (![A_238, B_239, C_240]: (k7_subset_1(A_238, B_239, C_240)=k4_xboole_0(B_239, C_240) | ~m1_subset_1(B_239, k1_zfmisc_1(A_238)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 20.44/11.84  tff(c_3154, plain, (![C_244]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_244)=k4_xboole_0('#skF_3', C_244))), inference(resolution, [status(thm)], [c_70, c_3082])).
% 20.44/11.84  tff(c_3166, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_3154])).
% 20.44/11.84  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.44/11.84  tff(c_4533, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3166, c_20])).
% 20.44/11.84  tff(c_2104, plain, (![A_193, B_194, C_195]: (r1_tarski(k4_xboole_0(A_193, B_194), C_195) | ~r1_tarski(A_193, k2_xboole_0(B_194, C_195)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.44/11.84  tff(c_131, plain, (![B_84, A_85]: (k2_xboole_0(B_84, A_85)=k2_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.44/11.84  tff(c_147, plain, (![A_85]: (k2_xboole_0(k1_xboole_0, A_85)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_131, c_14])).
% 20.44/11.84  tff(c_533, plain, (![A_108, B_109]: (k2_xboole_0(A_108, k4_xboole_0(B_109, A_108))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_56])).
% 20.44/11.84  tff(c_540, plain, (![B_109]: (k4_xboole_0(B_109, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_109))), inference(superposition, [status(thm), theory('equality')], [c_533, c_147])).
% 20.44/11.84  tff(c_558, plain, (![B_109]: (k4_xboole_0(B_109, k1_xboole_0)=B_109)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_540])).
% 20.44/11.84  tff(c_179, plain, (![A_86]: (k2_xboole_0(k1_xboole_0, A_86)=A_86)), inference(superposition, [status(thm), theory('equality')], [c_131, c_14])).
% 20.44/11.84  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k3_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_48])).
% 20.44/11.84  tff(c_192, plain, (![B_17]: (k3_xboole_0(k1_xboole_0, B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_179, c_18])).
% 20.44/11.84  tff(c_332, plain, (![A_100, B_101]: (k4_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.44/11.84  tff(c_347, plain, (![B_17]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_17))), inference(superposition, [status(thm), theory('equality')], [c_192, c_332])).
% 20.44/11.84  tff(c_609, plain, (![B_114]: (k4_xboole_0(k1_xboole_0, B_114)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_558, c_347])).
% 20.44/11.84  tff(c_22, plain, (![A_20, B_21]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k4_xboole_0(B_21, A_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 20.44/11.84  tff(c_625, plain, (![B_114]: (k1_xboole_0=B_114 | ~r1_tarski(B_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_609, c_22])).
% 20.44/11.84  tff(c_2122, plain, (![A_193, B_194]: (k4_xboole_0(A_193, B_194)=k1_xboole_0 | ~r1_tarski(A_193, k2_xboole_0(B_194, k1_xboole_0)))), inference(resolution, [status(thm)], [c_2104, c_625])).
% 20.44/11.84  tff(c_2146, plain, (![A_193, B_194]: (k4_xboole_0(A_193, B_194)=k1_xboole_0 | ~r1_tarski(A_193, B_194))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2122])).
% 20.44/11.84  tff(c_4550, plain, (k4_xboole_0(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_4533, c_2146])).
% 20.44/11.84  tff(c_24, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 20.44/11.84  tff(c_4612, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4550, c_24])).
% 20.44/11.84  tff(c_4636, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4612])).
% 20.44/11.84  tff(c_1386, plain, (![A_163, B_164, C_165]: (r1_tarski(A_163, k2_xboole_0(B_164, C_165)) | ~r1_tarski(k4_xboole_0(A_163, B_164), C_165))), inference(cnfTransformation, [status(thm)], [f_64])).
% 20.44/11.84  tff(c_1431, plain, (![A_166, B_167]: (r1_tarski(A_166, k2_xboole_0(B_167, A_166)))), inference(resolution, [status(thm)], [c_20, c_1386])).
% 20.44/11.84  tff(c_16, plain, (![A_13, C_15, B_14]: (r1_tarski(A_13, C_15) | ~r1_tarski(B_14, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 20.44/11.84  tff(c_1481, plain, (![A_13, B_167, A_166]: (r1_tarski(A_13, k2_xboole_0(B_167, A_166)) | ~r1_tarski(A_13, A_166))), inference(resolution, [status(thm)], [c_1431, c_16])).
% 20.44/11.84  tff(c_30, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.44/11.84  tff(c_19953, plain, (![A_443, B_444, C_445]: (r1_tarski(k4_xboole_0(A_443, B_444), C_445) | ~r1_tarski(A_443, k2_xboole_0(k3_xboole_0(A_443, B_444), C_445)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2104])).
% 20.44/11.84  tff(c_20209, plain, (![A_446, B_447, A_448]: (r1_tarski(k4_xboole_0(A_446, B_447), A_448) | ~r1_tarski(A_446, A_448))), inference(resolution, [status(thm)], [c_1481, c_19953])).
% 20.44/11.84  tff(c_20306, plain, (![A_448]: (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), A_448) | ~r1_tarski('#skF_3', A_448))), inference(superposition, [status(thm), theory('equality')], [c_3166, c_20209])).
% 20.44/11.84  tff(c_56, plain, (![A_58, B_59]: (m1_subset_1(A_58, k1_zfmisc_1(B_59)) | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_111])).
% 20.44/11.84  tff(c_4640, plain, (![A_273, B_274, C_275]: (k4_subset_1(A_273, B_274, C_275)=k2_xboole_0(B_274, C_275) | ~m1_subset_1(C_275, k1_zfmisc_1(A_273)) | ~m1_subset_1(B_274, k1_zfmisc_1(A_273)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 20.44/11.84  tff(c_28418, plain, (![B_520, B_521, A_522]: (k4_subset_1(B_520, B_521, A_522)=k2_xboole_0(B_521, A_522) | ~m1_subset_1(B_521, k1_zfmisc_1(B_520)) | ~r1_tarski(A_522, B_520))), inference(resolution, [status(thm)], [c_56, c_4640])).
% 20.44/11.84  tff(c_28437, plain, (![A_523]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_523)=k2_xboole_0('#skF_3', A_523) | ~r1_tarski(A_523, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_70, c_28418])).
% 20.44/11.84  tff(c_28458, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20306, c_28437])).
% 20.44/11.84  tff(c_28611, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_293, c_6019, c_4636, c_28458])).
% 20.44/11.84  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 20.44/11.84  tff(c_3506, plain, (![A_258, B_259]: (v4_pre_topc(k2_pre_topc(A_258, B_259), A_258) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_125])).
% 20.44/11.84  tff(c_3514, plain, (v4_pre_topc(k2_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_3506])).
% 20.44/11.84  tff(c_3519, plain, (v4_pre_topc(k2_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3514])).
% 20.44/11.84  tff(c_28668, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28611, c_3519])).
% 20.44/11.84  tff(c_28670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_28668])).
% 20.44/11.84  tff(c_28671, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_76])).
% 20.44/11.84  tff(c_28970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_28671])).
% 20.44/11.84  tff(c_28971, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_82])).
% 20.44/11.84  tff(c_29092, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28971, c_76])).
% 20.44/11.84  tff(c_32057, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_29092])).
% 20.44/11.84  tff(c_33609, plain, (![A_720, B_721]: (r1_tarski(k2_tops_1(A_720, B_721), B_721) | ~v4_pre_topc(B_721, A_720) | ~m1_subset_1(B_721, k1_zfmisc_1(u1_struct_0(A_720))) | ~l1_pre_topc(A_720))), inference(cnfTransformation, [status(thm)], [f_148])).
% 20.44/11.84  tff(c_33619, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_33609])).
% 20.44/11.84  tff(c_33625, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_28971, c_33619])).
% 20.44/11.84  tff(c_34156, plain, (![A_737, B_738]: (k7_subset_1(u1_struct_0(A_737), B_738, k2_tops_1(A_737, B_738))=k1_tops_1(A_737, B_738) | ~m1_subset_1(B_738, k1_zfmisc_1(u1_struct_0(A_737))) | ~l1_pre_topc(A_737))), inference(cnfTransformation, [status(thm)], [f_155])).
% 20.44/11.84  tff(c_34166, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_34156])).
% 20.44/11.84  tff(c_34172, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_31849, c_34166])).
% 20.44/11.84  tff(c_29971, plain, (![A_612, B_613]: (k4_xboole_0(A_612, B_613)=k3_subset_1(A_612, B_613) | ~m1_subset_1(B_613, k1_zfmisc_1(A_612)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 20.44/11.84  tff(c_34782, plain, (![B_746, A_747]: (k4_xboole_0(B_746, A_747)=k3_subset_1(B_746, A_747) | ~r1_tarski(A_747, B_746))), inference(resolution, [status(thm)], [c_56, c_29971])).
% 20.44/11.84  tff(c_34824, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_33625, c_34782])).
% 20.44/11.84  tff(c_34941, plain, (k3_subset_1('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34172, c_34824])).
% 20.44/11.84  tff(c_30786, plain, (![A_636, B_637]: (k3_subset_1(A_636, k3_subset_1(A_636, B_637))=B_637 | ~m1_subset_1(B_637, k1_zfmisc_1(A_636)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.44/11.84  tff(c_30791, plain, (![B_59, A_58]: (k3_subset_1(B_59, k3_subset_1(B_59, A_58))=A_58 | ~r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_56, c_30786])).
% 20.44/11.84  tff(c_38782, plain, (k3_subset_1('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34941, c_30791])).
% 20.44/11.84  tff(c_38790, plain, (k3_subset_1('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33625, c_38782])).
% 20.44/11.84  tff(c_52, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_107])).
% 20.44/11.84  tff(c_34, plain, (![B_36, A_35]: (k2_tarski(B_36, A_35)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.44/11.84  tff(c_29076, plain, (![A_546, B_547]: (k1_setfam_1(k2_tarski(A_546, B_547))=k3_xboole_0(A_546, B_547))), inference(cnfTransformation, [status(thm)], [f_107])).
% 20.44/11.84  tff(c_29104, plain, (![B_554, A_555]: (k1_setfam_1(k2_tarski(B_554, A_555))=k3_xboole_0(A_555, B_554))), inference(superposition, [status(thm), theory('equality')], [c_34, c_29076])).
% 20.44/11.84  tff(c_29116, plain, (![B_57, A_56]: (k3_xboole_0(B_57, A_56)=k3_xboole_0(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_52, c_29104])).
% 20.44/11.84  tff(c_34229, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34172, c_20])).
% 20.44/11.84  tff(c_29803, plain, (![A_605, B_606, C_607]: (r1_tarski(k4_xboole_0(A_605, B_606), C_607) | ~r1_tarski(A_605, k2_xboole_0(B_606, C_607)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.44/11.84  tff(c_29127, plain, (![A_556, B_557]: (k2_xboole_0(A_556, k4_xboole_0(B_557, A_556))=k2_xboole_0(A_556, B_557))), inference(cnfTransformation, [status(thm)], [f_56])).
% 20.44/11.84  tff(c_29134, plain, (![B_557]: (k4_xboole_0(B_557, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_557))), inference(superposition, [status(thm), theory('equality')], [c_29127, c_147])).
% 20.44/11.84  tff(c_29143, plain, (![B_557]: (k4_xboole_0(B_557, k1_xboole_0)=B_557)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_29134])).
% 20.44/11.84  tff(c_29168, plain, (![B_560, A_561]: (k3_xboole_0(B_560, A_561)=k3_xboole_0(A_561, B_560))), inference(superposition, [status(thm), theory('equality')], [c_52, c_29104])).
% 20.44/11.84  tff(c_28973, plain, (![A_542]: (k2_xboole_0(k1_xboole_0, A_542)=A_542)), inference(superposition, [status(thm), theory('equality')], [c_131, c_14])).
% 20.44/11.84  tff(c_28986, plain, (![B_17]: (k3_xboole_0(k1_xboole_0, B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28973, c_18])).
% 20.44/11.84  tff(c_29184, plain, (![B_560]: (k3_xboole_0(B_560, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_29168, c_28986])).
% 20.44/11.84  tff(c_29308, plain, (![A_567, B_568]: (k5_xboole_0(A_567, k3_xboole_0(A_567, B_568))=k4_xboole_0(A_567, B_568))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.44/11.84  tff(c_29317, plain, (![B_560]: (k5_xboole_0(B_560, k1_xboole_0)=k4_xboole_0(B_560, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_29184, c_29308])).
% 20.44/11.84  tff(c_29329, plain, (![B_560]: (k5_xboole_0(B_560, k1_xboole_0)=B_560)), inference(demodulation, [status(thm), theory('equality')], [c_29143, c_29317])).
% 20.44/11.84  tff(c_29326, plain, (![B_17]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_17))), inference(superposition, [status(thm), theory('equality')], [c_28986, c_29308])).
% 20.44/11.84  tff(c_29340, plain, (![B_570]: (k4_xboole_0(k1_xboole_0, B_570)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_29329, c_29326])).
% 20.44/11.84  tff(c_29352, plain, (![B_570]: (k1_xboole_0=B_570 | ~r1_tarski(B_570, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_29340, c_22])).
% 20.44/11.84  tff(c_29815, plain, (![A_605, B_606]: (k4_xboole_0(A_605, B_606)=k1_xboole_0 | ~r1_tarski(A_605, k2_xboole_0(B_606, k1_xboole_0)))), inference(resolution, [status(thm)], [c_29803, c_29352])).
% 20.44/11.84  tff(c_29836, plain, (![A_605, B_606]: (k4_xboole_0(A_605, B_606)=k1_xboole_0 | ~r1_tarski(A_605, B_606))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_29815])).
% 20.44/11.84  tff(c_34244, plain, (k4_xboole_0(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34229, c_29836])).
% 20.44/11.84  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.44/11.84  tff(c_29389, plain, (![A_574, B_575]: (k4_xboole_0(A_574, k3_xboole_0(A_574, B_575))=k4_xboole_0(A_574, B_575))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.44/11.84  tff(c_29399, plain, (![A_574, B_575]: (k2_xboole_0(k3_xboole_0(A_574, B_575), k4_xboole_0(A_574, B_575))=k2_xboole_0(k3_xboole_0(A_574, B_575), A_574))), inference(superposition, [status(thm), theory('equality')], [c_29389, c_24])).
% 20.44/11.84  tff(c_29427, plain, (![A_574, B_575]: (k2_xboole_0(k3_xboole_0(A_574, B_575), k4_xboole_0(A_574, B_575))=A_574)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_29399])).
% 20.44/11.84  tff(c_31421, plain, (![A_652, B_653, C_654]: (k2_xboole_0(k2_xboole_0(A_652, B_653), C_654)=k2_xboole_0(A_652, k2_xboole_0(B_653, C_654)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 20.44/11.84  tff(c_36819, plain, (![C_771, A_772, B_773]: (k2_xboole_0(C_771, k2_xboole_0(A_772, B_773))=k2_xboole_0(A_772, k2_xboole_0(B_773, C_771)))), inference(superposition, [status(thm), theory('equality')], [c_31421, c_2])).
% 20.44/11.84  tff(c_40569, plain, (![A_802, C_803]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_802, C_803))=k2_xboole_0(C_803, A_802))), inference(superposition, [status(thm), theory('equality')], [c_147, c_36819])).
% 20.44/11.84  tff(c_40777, plain, (![A_574, B_575]: (k2_xboole_0(k4_xboole_0(A_574, B_575), k3_xboole_0(A_574, B_575))=k2_xboole_0(k1_xboole_0, A_574))), inference(superposition, [status(thm), theory('equality')], [c_29427, c_40569])).
% 20.44/11.84  tff(c_45140, plain, (![A_847, B_848]: (k2_xboole_0(k4_xboole_0(A_847, B_848), k3_xboole_0(A_847, B_848))=A_847)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_40777])).
% 20.44/11.84  tff(c_45281, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_tops_1('#skF_2', '#skF_3'), '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34244, c_45140])).
% 20.44/11.84  tff(c_45394, plain, (k3_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_29116, c_45281])).
% 20.44/11.84  tff(c_30101, plain, (![A_614, B_615, C_616]: (r1_tarski(A_614, k2_xboole_0(B_615, C_616)) | ~r1_tarski(k4_xboole_0(A_614, B_615), C_616))), inference(cnfTransformation, [status(thm)], [f_64])).
% 20.44/11.84  tff(c_30161, plain, (![A_617, B_618]: (r1_tarski(A_617, k2_xboole_0(B_618, A_617)))), inference(resolution, [status(thm)], [c_20, c_30101])).
% 20.44/11.84  tff(c_30196, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_30161])).
% 20.44/11.84  tff(c_34890, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k3_subset_1(A_16, k3_xboole_0(A_16, B_17)))), inference(resolution, [status(thm)], [c_30196, c_34782])).
% 20.44/11.84  tff(c_34965, plain, (![A_16, B_17]: (k3_subset_1(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34890])).
% 20.44/11.84  tff(c_82777, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_45394, c_34965])).
% 20.44/11.84  tff(c_82907, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38790, c_82777])).
% 20.44/11.84  tff(c_82909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32057, c_82907])).
% 20.44/11.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.44/11.84  
% 20.44/11.84  Inference rules
% 20.44/11.84  ----------------------
% 20.44/11.84  #Ref     : 0
% 20.44/11.84  #Sup     : 20352
% 20.44/11.84  #Fact    : 0
% 20.44/11.84  #Define  : 0
% 20.44/11.84  #Split   : 10
% 20.44/11.84  #Chain   : 0
% 20.44/11.84  #Close   : 0
% 20.44/11.84  
% 20.44/11.84  Ordering : KBO
% 20.44/11.84  
% 20.44/11.84  Simplification rules
% 20.44/11.84  ----------------------
% 20.44/11.84  #Subsume      : 959
% 20.44/11.84  #Demod        : 20079
% 20.44/11.84  #Tautology    : 13307
% 20.44/11.84  #SimpNegUnit  : 3
% 20.44/11.84  #BackRed      : 8
% 20.44/11.84  
% 20.44/11.84  #Partial instantiations: 0
% 20.44/11.84  #Strategies tried      : 1
% 20.44/11.84  
% 20.44/11.84  Timing (in seconds)
% 20.44/11.84  ----------------------
% 20.44/11.84  Preprocessing        : 0.38
% 20.44/11.84  Parsing              : 0.21
% 20.44/11.84  CNF conversion       : 0.03
% 20.44/11.84  Main loop            : 10.70
% 20.44/11.84  Inferencing          : 1.55
% 20.44/11.84  Reduction            : 6.41
% 20.44/11.84  Demodulation         : 5.73
% 20.44/11.84  BG Simplification    : 0.18
% 20.44/11.84  Subsumption          : 2.07
% 20.44/11.84  Abstraction          : 0.28
% 20.44/11.84  MUC search           : 0.00
% 20.44/11.84  Cooper               : 0.00
% 20.44/11.84  Total                : 11.15
% 20.44/11.84  Index Insertion      : 0.00
% 20.44/11.84  Index Deletion       : 0.00
% 20.44/11.84  Index Matching       : 0.00
% 20.44/11.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------

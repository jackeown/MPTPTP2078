%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:18 EST 2020

% Result     : Theorem 14.19s
% Output     : CNFRefutation 14.19s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 181 expanded)
%              Number of leaves         :   49 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  157 ( 307 expanded)
%              Number of equality atoms :   77 ( 119 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_33166,plain,(
    ! [A_848,B_849,C_850] :
      ( k7_subset_1(A_848,B_849,C_850) = k4_xboole_0(B_849,C_850)
      | ~ m1_subset_1(B_849,k1_zfmisc_1(A_848)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_33180,plain,(
    ! [C_850] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_850) = k4_xboole_0('#skF_4',C_850) ),
    inference(resolution,[status(thm)],[c_74,c_33166])).

tff(c_80,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_234,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_78,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4988,plain,(
    ! [B_232,A_233] :
      ( v4_pre_topc(B_232,A_233)
      | k2_pre_topc(A_233,B_232) != B_232
      | ~ v2_pre_topc(A_233)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5010,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_4988])).

tff(c_5022,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_5010])).

tff(c_5023,plain,(
    k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_5022])).

tff(c_2415,plain,(
    ! [A_177,B_178,C_179] :
      ( k7_subset_1(A_177,B_178,C_179) = k4_xboole_0(B_178,C_179)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2458,plain,(
    ! [C_184] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_184) = k4_xboole_0('#skF_4',C_184) ),
    inference(resolution,[status(thm)],[c_74,c_2415])).

tff(c_86,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_120,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_2464,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2458,c_120])).

tff(c_24,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_193,plain,(
    ! [A_80,B_81] : k1_setfam_1(k2_tarski(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_239,plain,(
    ! [B_84,A_85] : k1_setfam_1(k2_tarski(B_84,A_85)) = k3_xboole_0(A_85,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_193])).

tff(c_52,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_262,plain,(
    ! [B_86,A_87] : k3_xboole_0(B_86,A_87) = k3_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_52])).

tff(c_50,plain,(
    ! [A_37] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_180,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,B_79)
      | ~ m1_subset_1(A_78,k1_zfmisc_1(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_208,plain,(
    ! [A_82] : r1_tarski(k1_xboole_0,A_82) ),
    inference(resolution,[status(thm)],[c_50,c_180])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_212,plain,(
    ! [A_82] : k3_xboole_0(k1_xboole_0,A_82) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_208,c_26])).

tff(c_278,plain,(
    ! [B_86] : k3_xboole_0(B_86,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_212])).

tff(c_32,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_460,plain,(
    ! [A_96,B_97] : k4_xboole_0(A_96,k4_xboole_0(A_96,B_97)) = k3_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_489,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_460])).

tff(c_495,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_489])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_352,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_376,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_352])).

tff(c_496,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_376])).

tff(c_28,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_154,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_832,plain,(
    ! [A_124,B_125] : k3_xboole_0(k4_xboole_0(A_124,B_125),A_124) = k4_xboole_0(A_124,B_125) ),
    inference(resolution,[status(thm)],[c_28,c_154])).

tff(c_22,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_847,plain,(
    ! [A_124,B_125] : k5_xboole_0(k4_xboole_0(A_124,B_125),k4_xboole_0(A_124,B_125)) = k4_xboole_0(k4_xboole_0(A_124,B_125),A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_22])).

tff(c_900,plain,(
    ! [A_126,B_127] : k4_xboole_0(k4_xboole_0(A_126,B_127),A_126) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_847])).

tff(c_30,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_917,plain,(
    ! [A_126,B_127] : k2_xboole_0(A_126,k4_xboole_0(A_126,B_127)) = k2_xboole_0(A_126,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_30])).

tff(c_955,plain,(
    ! [A_126,B_127] : k2_xboole_0(A_126,k4_xboole_0(A_126,B_127)) = A_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_917])).

tff(c_2482,plain,(
    k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2464,c_955])).

tff(c_6011,plain,(
    ! [A_264,B_265] :
      ( k4_subset_1(u1_struct_0(A_264),B_265,k2_tops_1(A_264,B_265)) = k2_pre_topc(A_264,B_265)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6027,plain,
    ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_6011])).

tff(c_6038,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6027])).

tff(c_64,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k2_tops_1(A_48,B_49),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3185,plain,(
    ! [A_200,B_201,C_202] :
      ( k4_subset_1(A_200,B_201,C_202) = k2_xboole_0(B_201,C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(A_200))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(A_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30502,plain,(
    ! [A_718,B_719,B_720] :
      ( k4_subset_1(u1_struct_0(A_718),B_719,k2_tops_1(A_718,B_720)) = k2_xboole_0(B_719,k2_tops_1(A_718,B_720))
      | ~ m1_subset_1(B_719,k1_zfmisc_1(u1_struct_0(A_718)))
      | ~ m1_subset_1(B_720,k1_zfmisc_1(u1_struct_0(A_718)))
      | ~ l1_pre_topc(A_718) ) ),
    inference(resolution,[status(thm)],[c_64,c_3185])).

tff(c_30559,plain,(
    ! [B_720] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3',B_720)) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3',B_720))
      | ~ m1_subset_1(B_720,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_74,c_30502])).

tff(c_30590,plain,(
    ! [B_721] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3',B_721)) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3',B_721))
      | ~ m1_subset_1(B_721,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_30559])).

tff(c_30669,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_30590])).

tff(c_30716,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2482,c_6038,c_30669])).

tff(c_30718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5023,c_30716])).

tff(c_30719,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_30951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30719,c_120])).

tff(c_30952,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_31053,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30952,c_80])).

tff(c_33209,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33180,c_31053])).

tff(c_31058,plain,(
    ! [A_751,B_752] : k1_setfam_1(k2_tarski(A_751,B_752)) = k3_xboole_0(A_751,B_752) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_31289,plain,(
    ! [A_768,B_769] : k1_setfam_1(k2_tarski(A_768,B_769)) = k3_xboole_0(B_769,A_768) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_31058])).

tff(c_31295,plain,(
    ! [B_769,A_768] : k3_xboole_0(B_769,A_768) = k3_xboole_0(A_768,B_769) ),
    inference(superposition,[status(thm),theory(equality)],[c_31289,c_52])).

tff(c_33907,plain,(
    ! [A_870,B_871] :
      ( r1_tarski(k2_tops_1(A_870,B_871),B_871)
      | ~ v4_pre_topc(B_871,A_870)
      | ~ m1_subset_1(B_871,k1_zfmisc_1(u1_struct_0(A_870)))
      | ~ l1_pre_topc(A_870) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_33920,plain,
    ( r1_tarski(k2_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_33907])).

tff(c_33930,plain,(
    r1_tarski(k2_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_30952,c_33920])).

tff(c_33935,plain,(
    k3_xboole_0(k2_tops_1('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_33930,c_26])).

tff(c_34006,plain,(
    k3_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_31295,c_33935])).

tff(c_36420,plain,(
    ! [A_917,B_918] :
      ( k7_subset_1(u1_struct_0(A_917),B_918,k2_tops_1(A_917,B_918)) = k1_tops_1(A_917,B_918)
      | ~ m1_subset_1(B_918,k1_zfmisc_1(u1_struct_0(A_917)))
      | ~ l1_pre_topc(A_917) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_36436,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_36420])).

tff(c_36448,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_33180,c_36436])).

tff(c_34,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36493,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36448,c_34])).

tff(c_36511,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34006,c_36493])).

tff(c_36513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33209,c_36511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:16:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.19/6.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.19/6.18  
% 14.19/6.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.19/6.18  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 14.19/6.18  
% 14.19/6.18  %Foreground sorts:
% 14.19/6.18  
% 14.19/6.18  
% 14.19/6.18  %Background operators:
% 14.19/6.18  
% 14.19/6.18  
% 14.19/6.18  %Foreground operators:
% 14.19/6.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.19/6.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.19/6.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.19/6.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.19/6.18  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 14.19/6.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.19/6.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.19/6.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.19/6.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.19/6.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.19/6.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.19/6.18  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.19/6.18  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.19/6.18  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.19/6.18  tff('#skF_3', type, '#skF_3': $i).
% 14.19/6.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.19/6.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.19/6.18  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.19/6.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.19/6.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.19/6.18  tff('#skF_4', type, '#skF_4': $i).
% 14.19/6.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.19/6.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.19/6.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.19/6.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.19/6.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.19/6.18  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.19/6.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.19/6.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.19/6.18  
% 14.19/6.20  tff(f_156, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 14.19/6.20  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.19/6.20  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 14.19/6.20  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 14.19/6.20  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.19/6.20  tff(f_83, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.19/6.20  tff(f_81, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 14.19/6.20  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.19/6.20  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.19/6.20  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.19/6.20  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.19/6.20  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 14.19/6.20  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.19/6.20  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.19/6.20  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.19/6.20  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 14.19/6.20  tff(f_114, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 14.19/6.20  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.19/6.20  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 14.19/6.20  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 14.19/6.20  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 14.19/6.20  tff(c_33166, plain, (![A_848, B_849, C_850]: (k7_subset_1(A_848, B_849, C_850)=k4_xboole_0(B_849, C_850) | ~m1_subset_1(B_849, k1_zfmisc_1(A_848)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.19/6.20  tff(c_33180, plain, (![C_850]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_850)=k4_xboole_0('#skF_4', C_850))), inference(resolution, [status(thm)], [c_74, c_33166])).
% 14.19/6.20  tff(c_80, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 14.19/6.20  tff(c_234, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 14.19/6.20  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 14.19/6.20  tff(c_78, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 14.19/6.20  tff(c_4988, plain, (![B_232, A_233]: (v4_pre_topc(B_232, A_233) | k2_pre_topc(A_233, B_232)!=B_232 | ~v2_pre_topc(A_233) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.19/6.20  tff(c_5010, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4' | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_74, c_4988])).
% 14.19/6.20  tff(c_5022, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_5010])).
% 14.19/6.20  tff(c_5023, plain, (k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_234, c_5022])).
% 14.19/6.20  tff(c_2415, plain, (![A_177, B_178, C_179]: (k7_subset_1(A_177, B_178, C_179)=k4_xboole_0(B_178, C_179) | ~m1_subset_1(B_178, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.19/6.20  tff(c_2458, plain, (![C_184]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_184)=k4_xboole_0('#skF_4', C_184))), inference(resolution, [status(thm)], [c_74, c_2415])).
% 14.19/6.20  tff(c_86, plain, (v4_pre_topc('#skF_4', '#skF_3') | k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 14.19/6.20  tff(c_120, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 14.19/6.20  tff(c_2464, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2458, c_120])).
% 14.19/6.20  tff(c_24, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.19/6.20  tff(c_36, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.19/6.20  tff(c_193, plain, (![A_80, B_81]: (k1_setfam_1(k2_tarski(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.19/6.20  tff(c_239, plain, (![B_84, A_85]: (k1_setfam_1(k2_tarski(B_84, A_85))=k3_xboole_0(A_85, B_84))), inference(superposition, [status(thm), theory('equality')], [c_36, c_193])).
% 14.19/6.20  tff(c_52, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.19/6.20  tff(c_262, plain, (![B_86, A_87]: (k3_xboole_0(B_86, A_87)=k3_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_239, c_52])).
% 14.19/6.20  tff(c_50, plain, (![A_37]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.19/6.20  tff(c_180, plain, (![A_78, B_79]: (r1_tarski(A_78, B_79) | ~m1_subset_1(A_78, k1_zfmisc_1(B_79)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.19/6.20  tff(c_208, plain, (![A_82]: (r1_tarski(k1_xboole_0, A_82))), inference(resolution, [status(thm)], [c_50, c_180])).
% 14.19/6.20  tff(c_26, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.19/6.20  tff(c_212, plain, (![A_82]: (k3_xboole_0(k1_xboole_0, A_82)=k1_xboole_0)), inference(resolution, [status(thm)], [c_208, c_26])).
% 14.19/6.20  tff(c_278, plain, (![B_86]: (k3_xboole_0(B_86, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_262, c_212])).
% 14.19/6.20  tff(c_32, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.19/6.20  tff(c_460, plain, (![A_96, B_97]: (k4_xboole_0(A_96, k4_xboole_0(A_96, B_97))=k3_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.19/6.20  tff(c_489, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_460])).
% 14.19/6.20  tff(c_495, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_278, c_489])).
% 14.19/6.20  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.19/6.20  tff(c_352, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.19/6.20  tff(c_376, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_352])).
% 14.19/6.20  tff(c_496, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_495, c_376])).
% 14.19/6.20  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.19/6.20  tff(c_154, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.19/6.20  tff(c_832, plain, (![A_124, B_125]: (k3_xboole_0(k4_xboole_0(A_124, B_125), A_124)=k4_xboole_0(A_124, B_125))), inference(resolution, [status(thm)], [c_28, c_154])).
% 14.19/6.20  tff(c_22, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.19/6.20  tff(c_847, plain, (![A_124, B_125]: (k5_xboole_0(k4_xboole_0(A_124, B_125), k4_xboole_0(A_124, B_125))=k4_xboole_0(k4_xboole_0(A_124, B_125), A_124))), inference(superposition, [status(thm), theory('equality')], [c_832, c_22])).
% 14.19/6.20  tff(c_900, plain, (![A_126, B_127]: (k4_xboole_0(k4_xboole_0(A_126, B_127), A_126)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_496, c_847])).
% 14.19/6.20  tff(c_30, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.19/6.20  tff(c_917, plain, (![A_126, B_127]: (k2_xboole_0(A_126, k4_xboole_0(A_126, B_127))=k2_xboole_0(A_126, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_900, c_30])).
% 14.19/6.20  tff(c_955, plain, (![A_126, B_127]: (k2_xboole_0(A_126, k4_xboole_0(A_126, B_127))=A_126)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_917])).
% 14.19/6.20  tff(c_2482, plain, (k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2464, c_955])).
% 14.19/6.20  tff(c_6011, plain, (![A_264, B_265]: (k4_subset_1(u1_struct_0(A_264), B_265, k2_tops_1(A_264, B_265))=k2_pre_topc(A_264, B_265) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.19/6.20  tff(c_6027, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_74, c_6011])).
% 14.19/6.20  tff(c_6038, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6027])).
% 14.19/6.20  tff(c_64, plain, (![A_48, B_49]: (m1_subset_1(k2_tops_1(A_48, B_49), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.19/6.20  tff(c_3185, plain, (![A_200, B_201, C_202]: (k4_subset_1(A_200, B_201, C_202)=k2_xboole_0(B_201, C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(A_200)) | ~m1_subset_1(B_201, k1_zfmisc_1(A_200)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.19/6.20  tff(c_30502, plain, (![A_718, B_719, B_720]: (k4_subset_1(u1_struct_0(A_718), B_719, k2_tops_1(A_718, B_720))=k2_xboole_0(B_719, k2_tops_1(A_718, B_720)) | ~m1_subset_1(B_719, k1_zfmisc_1(u1_struct_0(A_718))) | ~m1_subset_1(B_720, k1_zfmisc_1(u1_struct_0(A_718))) | ~l1_pre_topc(A_718))), inference(resolution, [status(thm)], [c_64, c_3185])).
% 14.19/6.20  tff(c_30559, plain, (![B_720]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', B_720))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', B_720)) | ~m1_subset_1(B_720, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_74, c_30502])).
% 14.19/6.20  tff(c_30590, plain, (![B_721]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', B_721))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', B_721)) | ~m1_subset_1(B_721, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_30559])).
% 14.19/6.20  tff(c_30669, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_30590])).
% 14.19/6.20  tff(c_30716, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2482, c_6038, c_30669])).
% 14.19/6.20  tff(c_30718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5023, c_30716])).
% 14.19/6.20  tff(c_30719, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_80])).
% 14.19/6.20  tff(c_30951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30719, c_120])).
% 14.19/6.20  tff(c_30952, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 14.19/6.20  tff(c_31053, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30952, c_80])).
% 14.19/6.20  tff(c_33209, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33180, c_31053])).
% 14.19/6.20  tff(c_31058, plain, (![A_751, B_752]: (k1_setfam_1(k2_tarski(A_751, B_752))=k3_xboole_0(A_751, B_752))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.19/6.20  tff(c_31289, plain, (![A_768, B_769]: (k1_setfam_1(k2_tarski(A_768, B_769))=k3_xboole_0(B_769, A_768))), inference(superposition, [status(thm), theory('equality')], [c_36, c_31058])).
% 14.19/6.20  tff(c_31295, plain, (![B_769, A_768]: (k3_xboole_0(B_769, A_768)=k3_xboole_0(A_768, B_769))), inference(superposition, [status(thm), theory('equality')], [c_31289, c_52])).
% 14.19/6.20  tff(c_33907, plain, (![A_870, B_871]: (r1_tarski(k2_tops_1(A_870, B_871), B_871) | ~v4_pre_topc(B_871, A_870) | ~m1_subset_1(B_871, k1_zfmisc_1(u1_struct_0(A_870))) | ~l1_pre_topc(A_870))), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.19/6.20  tff(c_33920, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_74, c_33907])).
% 14.19/6.20  tff(c_33930, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_30952, c_33920])).
% 14.19/6.20  tff(c_33935, plain, (k3_xboole_0(k2_tops_1('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_33930, c_26])).
% 14.19/6.20  tff(c_34006, plain, (k3_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_31295, c_33935])).
% 14.19/6.20  tff(c_36420, plain, (![A_917, B_918]: (k7_subset_1(u1_struct_0(A_917), B_918, k2_tops_1(A_917, B_918))=k1_tops_1(A_917, B_918) | ~m1_subset_1(B_918, k1_zfmisc_1(u1_struct_0(A_917))) | ~l1_pre_topc(A_917))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.19/6.20  tff(c_36436, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_74, c_36420])).
% 14.19/6.20  tff(c_36448, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_33180, c_36436])).
% 14.19/6.20  tff(c_34, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.19/6.20  tff(c_36493, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36448, c_34])).
% 14.19/6.20  tff(c_36511, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34006, c_36493])).
% 14.19/6.20  tff(c_36513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33209, c_36511])).
% 14.19/6.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.19/6.20  
% 14.19/6.20  Inference rules
% 14.19/6.20  ----------------------
% 14.19/6.20  #Ref     : 0
% 14.19/6.20  #Sup     : 8835
% 14.19/6.20  #Fact    : 0
% 14.19/6.20  #Define  : 0
% 14.19/6.20  #Split   : 8
% 14.19/6.20  #Chain   : 0
% 14.19/6.20  #Close   : 0
% 14.19/6.20  
% 14.19/6.20  Ordering : KBO
% 14.19/6.20  
% 14.19/6.20  Simplification rules
% 14.19/6.20  ----------------------
% 14.19/6.20  #Subsume      : 866
% 14.19/6.20  #Demod        : 9894
% 14.19/6.20  #Tautology    : 5078
% 14.19/6.20  #SimpNegUnit  : 62
% 14.19/6.20  #BackRed      : 83
% 14.19/6.20  
% 14.19/6.20  #Partial instantiations: 0
% 14.19/6.20  #Strategies tried      : 1
% 14.19/6.20  
% 14.19/6.20  Timing (in seconds)
% 14.19/6.20  ----------------------
% 14.19/6.20  Preprocessing        : 0.36
% 14.19/6.20  Parsing              : 0.19
% 14.19/6.20  CNF conversion       : 0.03
% 14.19/6.20  Main loop            : 5.06
% 14.19/6.20  Inferencing          : 1.06
% 14.19/6.20  Reduction            : 2.58
% 14.19/6.20  Demodulation         : 2.19
% 14.19/6.20  BG Simplification    : 0.11
% 14.19/6.20  Subsumption          : 1.00
% 14.19/6.20  Abstraction          : 0.21
% 14.19/6.20  MUC search           : 0.00
% 14.19/6.20  Cooper               : 0.00
% 14.19/6.20  Total                : 5.46
% 14.19/6.20  Index Insertion      : 0.00
% 14.19/6.20  Index Deletion       : 0.00
% 14.19/6.20  Index Matching       : 0.00
% 14.19/6.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

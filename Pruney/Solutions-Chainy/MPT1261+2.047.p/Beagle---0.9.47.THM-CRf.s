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

% Result     : Theorem 10.89s
% Output     : CNFRefutation 10.89s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 212 expanded)
%              Number of leaves         :   49 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 389 expanded)
%              Number of equality atoms :   82 ( 136 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(f_148,negated_conjecture,(
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

tff(f_100,axiom,(
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

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_81,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_106,axiom,(
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

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_22821,plain,(
    ! [A_596,B_597,C_598] :
      ( k7_subset_1(A_596,B_597,C_598) = k4_xboole_0(B_597,C_598)
      | ~ m1_subset_1(B_597,k1_zfmisc_1(A_596)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22830,plain,(
    ! [C_598] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_598) = k4_xboole_0('#skF_4',C_598) ),
    inference(resolution,[status(thm)],[c_70,c_22821])).

tff(c_82,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_116,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_76,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_237,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4220,plain,(
    ! [B_199,A_200] :
      ( v4_pre_topc(B_199,A_200)
      | k2_pre_topc(A_200,B_199) != B_199
      | ~ v2_pre_topc(A_200)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4234,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_4220])).

tff(c_4240,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_4234])).

tff(c_4241,plain,(
    k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_4240])).

tff(c_4978,plain,(
    ! [A_222,B_223] :
      ( k4_subset_1(u1_struct_0(A_222),B_223,k2_tops_1(A_222,B_223)) = k2_pre_topc(A_222,B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4994,plain,
    ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_4978])).

tff(c_5002,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4994])).

tff(c_1457,plain,(
    ! [A_137,B_138,C_139] :
      ( k7_subset_1(A_137,B_138,C_139) = k4_xboole_0(B_138,C_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1467,plain,(
    ! [C_140] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_140) = k4_xboole_0('#skF_4',C_140) ),
    inference(resolution,[status(thm)],[c_70,c_1457])).

tff(c_1473,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1467,c_116])).

tff(c_24,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_190,plain,(
    ! [A_72,B_73] : k1_setfam_1(k2_tarski(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_214,plain,(
    ! [B_76,A_77] : k1_setfam_1(k2_tarski(B_76,A_77)) = k3_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_190])).

tff(c_50,plain,(
    ! [A_36,B_37] : k1_setfam_1(k2_tarski(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_238,plain,(
    ! [B_78,A_79] : k3_xboole_0(B_78,A_79) = k3_xboole_0(A_79,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_50])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_150,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_163,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_254,plain,(
    ! [B_78] : k3_xboole_0(B_78,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_163])).

tff(c_34,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_395,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k4_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_422,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_395])).

tff(c_425,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_422])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_358,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_382,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_358])).

tff(c_561,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_382])).

tff(c_30,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_697,plain,(
    ! [A_108,B_109] : k3_xboole_0(k4_xboole_0(A_108,B_109),A_108) = k4_xboole_0(A_108,B_109) ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_22,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_709,plain,(
    ! [A_108,B_109] : k5_xboole_0(k4_xboole_0(A_108,B_109),k4_xboole_0(A_108,B_109)) = k4_xboole_0(k4_xboole_0(A_108,B_109),A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_22])).

tff(c_766,plain,(
    ! [A_110,B_111] : k4_xboole_0(k4_xboole_0(A_110,B_111),A_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_709])).

tff(c_32,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_783,plain,(
    ! [A_110,B_111] : k2_xboole_0(A_110,k4_xboole_0(A_110,B_111)) = k2_xboole_0(A_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_32])).

tff(c_825,plain,(
    ! [A_110,B_111] : k2_xboole_0(A_110,k4_xboole_0(A_110,B_111)) = A_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_783])).

tff(c_1485,plain,(
    k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1473,c_825])).

tff(c_60,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k2_tops_1(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2857,plain,(
    ! [A_171,B_172,C_173] :
      ( k4_subset_1(A_171,B_172,C_173) = k2_xboole_0(B_172,C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_171))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(A_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20569,plain,(
    ! [A_492,B_493,B_494] :
      ( k4_subset_1(u1_struct_0(A_492),B_493,k2_tops_1(A_492,B_494)) = k2_xboole_0(B_493,k2_tops_1(A_492,B_494))
      | ~ m1_subset_1(B_493,k1_zfmisc_1(u1_struct_0(A_492)))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(u1_struct_0(A_492)))
      | ~ l1_pre_topc(A_492) ) ),
    inference(resolution,[status(thm)],[c_60,c_2857])).

tff(c_20587,plain,(
    ! [B_494] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3',B_494)) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3',B_494))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_70,c_20569])).

tff(c_20600,plain,(
    ! [B_495] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3',B_495)) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3',B_495))
      | ~ m1_subset_1(B_495,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20587])).

tff(c_20627,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_20600])).

tff(c_20640,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5002,c_1485,c_20627])).

tff(c_20642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4241,c_20640])).

tff(c_20643,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_20913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_20643])).

tff(c_20914,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_21014,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20914,c_76])).

tff(c_22831,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22830,c_21014])).

tff(c_20981,plain,(
    ! [A_524,B_525] : k1_setfam_1(k2_tarski(A_524,B_525)) = k3_xboole_0(A_524,B_525) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_21015,plain,(
    ! [B_528,A_529] : k1_setfam_1(k2_tarski(B_528,A_529)) = k3_xboole_0(A_529,B_528) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_20981])).

tff(c_21021,plain,(
    ! [B_528,A_529] : k3_xboole_0(B_528,A_529) = k3_xboole_0(A_529,B_528) ),
    inference(superposition,[status(thm),theory(equality)],[c_21015,c_50])).

tff(c_23807,plain,(
    ! [A_624,B_625] :
      ( r1_tarski(k2_tops_1(A_624,B_625),B_625)
      | ~ v4_pre_topc(B_625,A_624)
      | ~ m1_subset_1(B_625,k1_zfmisc_1(u1_struct_0(A_624)))
      | ~ l1_pre_topc(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_23817,plain,
    ( r1_tarski(k2_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_23807])).

tff(c_23823,plain,(
    r1_tarski(k2_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20914,c_23817])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_23827,plain,(
    k3_xboole_0(k2_tops_1('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_23823,c_26])).

tff(c_23907,plain,(
    k3_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21021,c_23827])).

tff(c_54,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_21873,plain,(
    ! [A_574,B_575] :
      ( k4_xboole_0(A_574,B_575) = k3_subset_1(A_574,B_575)
      | ~ m1_subset_1(B_575,k1_zfmisc_1(A_574)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_25033,plain,(
    ! [B_654,A_655] :
      ( k4_xboole_0(B_654,A_655) = k3_subset_1(B_654,A_655)
      | ~ r1_tarski(A_655,B_654) ) ),
    inference(resolution,[status(thm)],[c_54,c_21873])).

tff(c_25061,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k3_subset_1('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_23823,c_25033])).

tff(c_25744,plain,(
    ! [A_674,B_675] :
      ( k7_subset_1(u1_struct_0(A_674),B_675,k2_tops_1(A_674,B_675)) = k1_tops_1(A_674,B_675)
      | ~ m1_subset_1(B_675,k1_zfmisc_1(u1_struct_0(A_674)))
      | ~ l1_pre_topc(A_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_25760,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_25744])).

tff(c_25770,plain,(
    k3_subset_1('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_25061,c_22830,c_25760])).

tff(c_25781,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25770,c_25061])).

tff(c_36,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_25833,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25781,c_36])).

tff(c_25846,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23907,c_25833])).

tff(c_25848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22831,c_25846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.89/4.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.89/4.60  
% 10.89/4.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.89/4.60  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 10.89/4.60  
% 10.89/4.60  %Foreground sorts:
% 10.89/4.60  
% 10.89/4.60  
% 10.89/4.60  %Background operators:
% 10.89/4.60  
% 10.89/4.60  
% 10.89/4.60  %Foreground operators:
% 10.89/4.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.89/4.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.89/4.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.89/4.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.89/4.60  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.89/4.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.89/4.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.89/4.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.89/4.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.89/4.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.89/4.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.89/4.60  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.89/4.60  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.89/4.60  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.89/4.60  tff('#skF_3', type, '#skF_3': $i).
% 10.89/4.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.89/4.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.89/4.60  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.89/4.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.89/4.60  tff('#skF_4', type, '#skF_4': $i).
% 10.89/4.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.89/4.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.89/4.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.89/4.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.89/4.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.89/4.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.89/4.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.89/4.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.89/4.60  
% 10.89/4.62  tff(f_148, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 10.89/4.62  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.89/4.62  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 10.89/4.62  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.89/4.62  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.89/4.62  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.89/4.62  tff(f_81, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.89/4.62  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.89/4.62  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.89/4.62  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.89/4.62  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.89/4.62  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 10.89/4.62  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.89/4.62  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.89/4.62  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.89/4.62  tff(f_106, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 10.89/4.62  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.89/4.62  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 10.89/4.62  tff(f_85, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.89/4.62  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.89/4.62  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 10.89/4.62  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.89/4.62  tff(c_22821, plain, (![A_596, B_597, C_598]: (k7_subset_1(A_596, B_597, C_598)=k4_xboole_0(B_597, C_598) | ~m1_subset_1(B_597, k1_zfmisc_1(A_596)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.89/4.62  tff(c_22830, plain, (![C_598]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_598)=k4_xboole_0('#skF_4', C_598))), inference(resolution, [status(thm)], [c_70, c_22821])).
% 10.89/4.62  tff(c_82, plain, (v4_pre_topc('#skF_4', '#skF_3') | k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.89/4.62  tff(c_116, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 10.89/4.62  tff(c_76, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.89/4.62  tff(c_237, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_76])).
% 10.89/4.62  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.89/4.62  tff(c_74, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.89/4.62  tff(c_4220, plain, (![B_199, A_200]: (v4_pre_topc(B_199, A_200) | k2_pre_topc(A_200, B_199)!=B_199 | ~v2_pre_topc(A_200) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.89/4.62  tff(c_4234, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4' | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_4220])).
% 10.89/4.62  tff(c_4240, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_4234])).
% 10.89/4.62  tff(c_4241, plain, (k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_237, c_4240])).
% 10.89/4.62  tff(c_4978, plain, (![A_222, B_223]: (k4_subset_1(u1_struct_0(A_222), B_223, k2_tops_1(A_222, B_223))=k2_pre_topc(A_222, B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.89/4.62  tff(c_4994, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_4978])).
% 10.89/4.62  tff(c_5002, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4994])).
% 10.89/4.62  tff(c_1457, plain, (![A_137, B_138, C_139]: (k7_subset_1(A_137, B_138, C_139)=k4_xboole_0(B_138, C_139) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.89/4.62  tff(c_1467, plain, (![C_140]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_140)=k4_xboole_0('#skF_4', C_140))), inference(resolution, [status(thm)], [c_70, c_1457])).
% 10.89/4.62  tff(c_1473, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1467, c_116])).
% 10.89/4.62  tff(c_24, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.89/4.62  tff(c_38, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.89/4.62  tff(c_190, plain, (![A_72, B_73]: (k1_setfam_1(k2_tarski(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.89/4.62  tff(c_214, plain, (![B_76, A_77]: (k1_setfam_1(k2_tarski(B_76, A_77))=k3_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_38, c_190])).
% 10.89/4.62  tff(c_50, plain, (![A_36, B_37]: (k1_setfam_1(k2_tarski(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.89/4.62  tff(c_238, plain, (![B_78, A_79]: (k3_xboole_0(B_78, A_79)=k3_xboole_0(A_79, B_78))), inference(superposition, [status(thm), theory('equality')], [c_214, c_50])).
% 10.89/4.62  tff(c_28, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.89/4.62  tff(c_150, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.89/4.62  tff(c_163, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_150])).
% 10.89/4.62  tff(c_254, plain, (![B_78]: (k3_xboole_0(B_78, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_238, c_163])).
% 10.89/4.62  tff(c_34, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.89/4.62  tff(c_395, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k4_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.89/4.62  tff(c_422, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_395])).
% 10.89/4.62  tff(c_425, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_254, c_422])).
% 10.89/4.62  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.89/4.62  tff(c_358, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.89/4.62  tff(c_382, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_358])).
% 10.89/4.62  tff(c_561, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_425, c_382])).
% 10.89/4.62  tff(c_30, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.89/4.62  tff(c_697, plain, (![A_108, B_109]: (k3_xboole_0(k4_xboole_0(A_108, B_109), A_108)=k4_xboole_0(A_108, B_109))), inference(resolution, [status(thm)], [c_30, c_150])).
% 10.89/4.62  tff(c_22, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.89/4.62  tff(c_709, plain, (![A_108, B_109]: (k5_xboole_0(k4_xboole_0(A_108, B_109), k4_xboole_0(A_108, B_109))=k4_xboole_0(k4_xboole_0(A_108, B_109), A_108))), inference(superposition, [status(thm), theory('equality')], [c_697, c_22])).
% 10.89/4.62  tff(c_766, plain, (![A_110, B_111]: (k4_xboole_0(k4_xboole_0(A_110, B_111), A_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_561, c_709])).
% 10.89/4.62  tff(c_32, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.89/4.62  tff(c_783, plain, (![A_110, B_111]: (k2_xboole_0(A_110, k4_xboole_0(A_110, B_111))=k2_xboole_0(A_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_766, c_32])).
% 10.89/4.62  tff(c_825, plain, (![A_110, B_111]: (k2_xboole_0(A_110, k4_xboole_0(A_110, B_111))=A_110)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_783])).
% 10.89/4.62  tff(c_1485, plain, (k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1473, c_825])).
% 10.89/4.62  tff(c_60, plain, (![A_43, B_44]: (m1_subset_1(k2_tops_1(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.89/4.62  tff(c_2857, plain, (![A_171, B_172, C_173]: (k4_subset_1(A_171, B_172, C_173)=k2_xboole_0(B_172, C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(A_171)) | ~m1_subset_1(B_172, k1_zfmisc_1(A_171)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.89/4.62  tff(c_20569, plain, (![A_492, B_493, B_494]: (k4_subset_1(u1_struct_0(A_492), B_493, k2_tops_1(A_492, B_494))=k2_xboole_0(B_493, k2_tops_1(A_492, B_494)) | ~m1_subset_1(B_493, k1_zfmisc_1(u1_struct_0(A_492))) | ~m1_subset_1(B_494, k1_zfmisc_1(u1_struct_0(A_492))) | ~l1_pre_topc(A_492))), inference(resolution, [status(thm)], [c_60, c_2857])).
% 10.89/4.62  tff(c_20587, plain, (![B_494]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', B_494))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', B_494)) | ~m1_subset_1(B_494, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_20569])).
% 10.89/4.62  tff(c_20600, plain, (![B_495]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', B_495))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', B_495)) | ~m1_subset_1(B_495, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_20587])).
% 10.89/4.62  tff(c_20627, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_20600])).
% 10.89/4.62  tff(c_20640, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5002, c_1485, c_20627])).
% 10.89/4.62  tff(c_20642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4241, c_20640])).
% 10.89/4.62  tff(c_20643, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_76])).
% 10.89/4.62  tff(c_20913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_20643])).
% 10.89/4.62  tff(c_20914, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_82])).
% 10.89/4.62  tff(c_21014, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20914, c_76])).
% 10.89/4.62  tff(c_22831, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22830, c_21014])).
% 10.89/4.62  tff(c_20981, plain, (![A_524, B_525]: (k1_setfam_1(k2_tarski(A_524, B_525))=k3_xboole_0(A_524, B_525))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.89/4.62  tff(c_21015, plain, (![B_528, A_529]: (k1_setfam_1(k2_tarski(B_528, A_529))=k3_xboole_0(A_529, B_528))), inference(superposition, [status(thm), theory('equality')], [c_38, c_20981])).
% 10.89/4.62  tff(c_21021, plain, (![B_528, A_529]: (k3_xboole_0(B_528, A_529)=k3_xboole_0(A_529, B_528))), inference(superposition, [status(thm), theory('equality')], [c_21015, c_50])).
% 10.89/4.62  tff(c_23807, plain, (![A_624, B_625]: (r1_tarski(k2_tops_1(A_624, B_625), B_625) | ~v4_pre_topc(B_625, A_624) | ~m1_subset_1(B_625, k1_zfmisc_1(u1_struct_0(A_624))) | ~l1_pre_topc(A_624))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.89/4.62  tff(c_23817, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_23807])).
% 10.89/4.62  tff(c_23823, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_20914, c_23817])).
% 10.89/4.62  tff(c_26, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.89/4.62  tff(c_23827, plain, (k3_xboole_0(k2_tops_1('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_23823, c_26])).
% 10.89/4.62  tff(c_23907, plain, (k3_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21021, c_23827])).
% 10.89/4.62  tff(c_54, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.89/4.62  tff(c_21873, plain, (![A_574, B_575]: (k4_xboole_0(A_574, B_575)=k3_subset_1(A_574, B_575) | ~m1_subset_1(B_575, k1_zfmisc_1(A_574)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.89/4.62  tff(c_25033, plain, (![B_654, A_655]: (k4_xboole_0(B_654, A_655)=k3_subset_1(B_654, A_655) | ~r1_tarski(A_655, B_654))), inference(resolution, [status(thm)], [c_54, c_21873])).
% 10.89/4.62  tff(c_25061, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_23823, c_25033])).
% 10.89/4.62  tff(c_25744, plain, (![A_674, B_675]: (k7_subset_1(u1_struct_0(A_674), B_675, k2_tops_1(A_674, B_675))=k1_tops_1(A_674, B_675) | ~m1_subset_1(B_675, k1_zfmisc_1(u1_struct_0(A_674))) | ~l1_pre_topc(A_674))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.89/4.62  tff(c_25760, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_25744])).
% 10.89/4.62  tff(c_25770, plain, (k3_subset_1('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_25061, c_22830, c_25760])).
% 10.89/4.62  tff(c_25781, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25770, c_25061])).
% 10.89/4.62  tff(c_36, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.89/4.62  tff(c_25833, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_25781, c_36])).
% 10.89/4.62  tff(c_25846, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23907, c_25833])).
% 10.89/4.62  tff(c_25848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22831, c_25846])).
% 10.89/4.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.89/4.62  
% 10.89/4.62  Inference rules
% 10.89/4.62  ----------------------
% 10.89/4.62  #Ref     : 0
% 10.89/4.62  #Sup     : 6360
% 10.89/4.62  #Fact    : 0
% 10.89/4.62  #Define  : 0
% 10.89/4.62  #Split   : 3
% 10.89/4.62  #Chain   : 0
% 10.89/4.62  #Close   : 0
% 10.89/4.62  
% 10.89/4.62  Ordering : KBO
% 10.89/4.62  
% 10.89/4.62  Simplification rules
% 10.89/4.62  ----------------------
% 10.89/4.62  #Subsume      : 584
% 10.89/4.62  #Demod        : 8228
% 10.89/4.62  #Tautology    : 4160
% 10.89/4.62  #SimpNegUnit  : 6
% 10.89/4.62  #BackRed      : 8
% 10.89/4.62  
% 10.89/4.62  #Partial instantiations: 0
% 10.89/4.62  #Strategies tried      : 1
% 10.89/4.62  
% 10.89/4.62  Timing (in seconds)
% 10.89/4.62  ----------------------
% 10.89/4.62  Preprocessing        : 0.36
% 10.89/4.62  Parsing              : 0.20
% 10.89/4.62  CNF conversion       : 0.03
% 10.89/4.62  Main loop            : 3.47
% 10.89/4.62  Inferencing          : 0.78
% 10.89/4.62  Reduction            : 1.83
% 10.89/4.62  Demodulation         : 1.58
% 10.89/4.62  BG Simplification    : 0.08
% 10.89/4.62  Subsumption          : 0.61
% 10.89/4.62  Abstraction          : 0.15
% 10.89/4.62  MUC search           : 0.00
% 10.89/4.62  Cooper               : 0.00
% 11.08/4.62  Total                : 3.87
% 11.08/4.62  Index Insertion      : 0.00
% 11.08/4.62  Index Deletion       : 0.00
% 11.08/4.62  Index Matching       : 0.00
% 11.08/4.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------

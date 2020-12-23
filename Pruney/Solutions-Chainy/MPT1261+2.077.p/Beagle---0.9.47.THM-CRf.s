%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:22 EST 2020

% Result     : Theorem 5.49s
% Output     : CNFRefutation 5.49s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 179 expanded)
%              Number of leaves         :   43 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 308 expanded)
%              Number of equality atoms :   81 ( 125 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5485,plain,(
    ! [A_211,B_212,C_213] :
      ( k7_subset_1(A_211,B_212,C_213) = k4_xboole_0(B_212,C_213)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(A_211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5488,plain,(
    ! [C_213] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_213) = k4_xboole_0('#skF_2',C_213) ),
    inference(resolution,[status(thm)],[c_40,c_5485])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_275,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1684,plain,(
    ! [B_121,A_122] :
      ( v4_pre_topc(B_121,A_122)
      | k2_pre_topc(A_122,B_121) != B_121
      | ~ v2_pre_topc(A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1690,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1684])).

tff(c_1694,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1690])).

tff(c_1695,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_1694])).

tff(c_2159,plain,(
    ! [A_133,B_134] :
      ( k4_subset_1(u1_struct_0(A_133),B_134,k2_tops_1(A_133,B_134)) = k2_pre_topc(A_133,B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2163,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2159])).

tff(c_2167,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2163])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_118,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_447,plain,(
    ! [A_72,B_73,C_74] :
      ( k7_subset_1(A_72,B_73,C_74) = k4_xboole_0(B_73,C_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_497,plain,(
    ! [C_79] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_79) = k4_xboole_0('#skF_2',C_79) ),
    inference(resolution,[status(thm)],[c_40,c_447])).

tff(c_509,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_497])).

tff(c_294,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_129,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    ! [A_55,B_56] : k2_xboole_0(k4_xboole_0(A_55,B_56),A_55) = A_55 ),
    inference(resolution,[status(thm)],[c_12,c_129])).

tff(c_164,plain,(
    ! [B_56] : k4_xboole_0(k1_xboole_0,B_56) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_8])).

tff(c_352,plain,(
    ! [B_70] : k3_xboole_0(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_164])).

tff(c_20,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_203,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_219,plain,(
    ! [B_60,A_61] : k1_setfam_1(k2_tarski(B_60,A_61)) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_203])).

tff(c_26,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_225,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,A_61) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_26])).

tff(c_360,plain,(
    ! [B_70] : k3_xboole_0(B_70,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_225])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_329,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_294])).

tff(c_581,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_329])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_334,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_349,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_334])).

tff(c_623,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_349])).

tff(c_119,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_774,plain,(
    ! [A_93,B_94] : k3_xboole_0(k4_xboole_0(A_93,B_94),A_93) = k4_xboole_0(A_93,B_94) ),
    inference(resolution,[status(thm)],[c_12,c_119])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_796,plain,(
    ! [A_93,B_94] : k5_xboole_0(k4_xboole_0(A_93,B_94),k4_xboole_0(A_93,B_94)) = k4_xboole_0(k4_xboole_0(A_93,B_94),A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_4])).

tff(c_847,plain,(
    ! [A_95,B_96] : k4_xboole_0(k4_xboole_0(A_95,B_96),A_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_796])).

tff(c_879,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_847])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1044,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_14])).

tff(c_1057,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1044])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_tops_1(A_30,B_31),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1452,plain,(
    ! [A_113,B_114,C_115] :
      ( k4_subset_1(A_113,B_114,C_115) = k2_xboole_0(B_114,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(A_113))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4633,plain,(
    ! [A_174,B_175,B_176] :
      ( k4_subset_1(u1_struct_0(A_174),B_175,k2_tops_1(A_174,B_176)) = k2_xboole_0(B_175,k2_tops_1(A_174,B_176))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(resolution,[status(thm)],[c_32,c_1452])).

tff(c_4637,plain,(
    ! [B_176] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_176)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_176))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_4633])).

tff(c_4959,plain,(
    ! [B_179] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_179)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_179))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4637])).

tff(c_4966,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_4959])).

tff(c_4971,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_1057,c_4966])).

tff(c_4973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1695,c_4971])).

tff(c_4974,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4974,c_118])).

tff(c_5144,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5166,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5144,c_46])).

tff(c_5620,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5488,c_5166])).

tff(c_5233,plain,(
    ! [A_196,B_197] : k1_setfam_1(k2_tarski(A_196,B_197)) = k3_xboole_0(A_196,B_197) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5269,plain,(
    ! [B_201,A_202] : k1_setfam_1(k2_tarski(B_201,A_202)) = k3_xboole_0(A_202,B_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5233])).

tff(c_5275,plain,(
    ! [B_201,A_202] : k3_xboole_0(B_201,A_202) = k3_xboole_0(A_202,B_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_5269,c_26])).

tff(c_6022,plain,(
    ! [A_240,B_241] :
      ( r1_tarski(k2_tops_1(A_240,B_241),B_241)
      | ~ v4_pre_topc(B_241,A_240)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6026,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_6022])).

tff(c_6030,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5144,c_6026])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6038,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6030,c_10])).

tff(c_6145,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5275,c_6038])).

tff(c_7091,plain,(
    ! [A_269,B_270] :
      ( k7_subset_1(u1_struct_0(A_269),B_270,k2_tops_1(A_269,B_270)) = k1_tops_1(A_269,B_270)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7095,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_7091])).

tff(c_7099,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5488,c_7095])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7121,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7099,c_18])).

tff(c_7134,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6145,c_7121])).

tff(c_7136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5620,c_7134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.49/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.14  
% 5.49/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.14  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.49/2.14  
% 5.49/2.14  %Foreground sorts:
% 5.49/2.14  
% 5.49/2.14  
% 5.49/2.14  %Background operators:
% 5.49/2.14  
% 5.49/2.14  
% 5.49/2.14  %Foreground operators:
% 5.49/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.49/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.49/2.14  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.49/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.49/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.49/2.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.49/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.49/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.49/2.14  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.49/2.14  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.49/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.49/2.14  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.49/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.49/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.49/2.14  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.49/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.49/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.49/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.49/2.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.49/2.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.49/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.49/2.14  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.49/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.49/2.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.49/2.14  
% 5.49/2.16  tff(f_117, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.49/2.16  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.49/2.16  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.49/2.16  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.49/2.16  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.49/2.16  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.49/2.16  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.49/2.16  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.49/2.16  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.49/2.16  tff(f_61, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.49/2.16  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.49/2.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.49/2.16  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.49/2.16  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.49/2.16  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.49/2.16  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.49/2.16  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.49/2.16  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.49/2.16  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.49/2.16  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.49/2.16  tff(c_5485, plain, (![A_211, B_212, C_213]: (k7_subset_1(A_211, B_212, C_213)=k4_xboole_0(B_212, C_213) | ~m1_subset_1(B_212, k1_zfmisc_1(A_211)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.49/2.16  tff(c_5488, plain, (![C_213]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_213)=k4_xboole_0('#skF_2', C_213))), inference(resolution, [status(thm)], [c_40, c_5485])).
% 5.49/2.16  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.49/2.16  tff(c_275, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 5.49/2.16  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.49/2.16  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.49/2.16  tff(c_1684, plain, (![B_121, A_122]: (v4_pre_topc(B_121, A_122) | k2_pre_topc(A_122, B_121)!=B_121 | ~v2_pre_topc(A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.49/2.16  tff(c_1690, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1684])).
% 5.49/2.16  tff(c_1694, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1690])).
% 5.49/2.16  tff(c_1695, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_275, c_1694])).
% 5.49/2.16  tff(c_2159, plain, (![A_133, B_134]: (k4_subset_1(u1_struct_0(A_133), B_134, k2_tops_1(A_133, B_134))=k2_pre_topc(A_133, B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.49/2.16  tff(c_2163, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2159])).
% 5.49/2.16  tff(c_2167, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2163])).
% 5.49/2.16  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.49/2.16  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.49/2.16  tff(c_118, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 5.49/2.16  tff(c_447, plain, (![A_72, B_73, C_74]: (k7_subset_1(A_72, B_73, C_74)=k4_xboole_0(B_73, C_74) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.49/2.16  tff(c_497, plain, (![C_79]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_79)=k4_xboole_0('#skF_2', C_79))), inference(resolution, [status(thm)], [c_40, c_447])).
% 5.49/2.16  tff(c_509, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_497])).
% 5.49/2.16  tff(c_294, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.49/2.16  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.49/2.16  tff(c_129, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.49/2.16  tff(c_157, plain, (![A_55, B_56]: (k2_xboole_0(k4_xboole_0(A_55, B_56), A_55)=A_55)), inference(resolution, [status(thm)], [c_12, c_129])).
% 5.49/2.16  tff(c_164, plain, (![B_56]: (k4_xboole_0(k1_xboole_0, B_56)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_8])).
% 5.49/2.16  tff(c_352, plain, (![B_70]: (k3_xboole_0(k1_xboole_0, B_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_294, c_164])).
% 5.49/2.16  tff(c_20, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.49/2.16  tff(c_203, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.49/2.16  tff(c_219, plain, (![B_60, A_61]: (k1_setfam_1(k2_tarski(B_60, A_61))=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_20, c_203])).
% 5.49/2.16  tff(c_26, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.49/2.16  tff(c_225, plain, (![B_60, A_61]: (k3_xboole_0(B_60, A_61)=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_219, c_26])).
% 5.49/2.16  tff(c_360, plain, (![B_70]: (k3_xboole_0(B_70, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_352, c_225])).
% 5.49/2.16  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.49/2.16  tff(c_329, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_294])).
% 5.49/2.16  tff(c_581, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_360, c_329])).
% 5.49/2.16  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.49/2.16  tff(c_334, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.49/2.16  tff(c_349, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_334])).
% 5.49/2.16  tff(c_623, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_581, c_349])).
% 5.49/2.16  tff(c_119, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.49/2.16  tff(c_774, plain, (![A_93, B_94]: (k3_xboole_0(k4_xboole_0(A_93, B_94), A_93)=k4_xboole_0(A_93, B_94))), inference(resolution, [status(thm)], [c_12, c_119])).
% 5.49/2.16  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.49/2.16  tff(c_796, plain, (![A_93, B_94]: (k5_xboole_0(k4_xboole_0(A_93, B_94), k4_xboole_0(A_93, B_94))=k4_xboole_0(k4_xboole_0(A_93, B_94), A_93))), inference(superposition, [status(thm), theory('equality')], [c_774, c_4])).
% 5.49/2.16  tff(c_847, plain, (![A_95, B_96]: (k4_xboole_0(k4_xboole_0(A_95, B_96), A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_623, c_796])).
% 5.49/2.16  tff(c_879, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_509, c_847])).
% 5.49/2.16  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.49/2.16  tff(c_1044, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_879, c_14])).
% 5.49/2.16  tff(c_1057, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1044])).
% 5.49/2.16  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(k2_tops_1(A_30, B_31), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.49/2.16  tff(c_1452, plain, (![A_113, B_114, C_115]: (k4_subset_1(A_113, B_114, C_115)=k2_xboole_0(B_114, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(A_113)) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.49/2.16  tff(c_4633, plain, (![A_174, B_175, B_176]: (k4_subset_1(u1_struct_0(A_174), B_175, k2_tops_1(A_174, B_176))=k2_xboole_0(B_175, k2_tops_1(A_174, B_176)) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(resolution, [status(thm)], [c_32, c_1452])).
% 5.49/2.16  tff(c_4637, plain, (![B_176]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_176))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_176)) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_4633])).
% 5.49/2.16  tff(c_4959, plain, (![B_179]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_179))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_179)) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4637])).
% 5.49/2.16  tff(c_4966, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_4959])).
% 5.49/2.16  tff(c_4971, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_1057, c_4966])).
% 5.49/2.16  tff(c_4973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1695, c_4971])).
% 5.49/2.16  tff(c_4974, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.49/2.16  tff(c_5143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4974, c_118])).
% 5.49/2.16  tff(c_5144, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 5.49/2.16  tff(c_5166, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5144, c_46])).
% 5.49/2.16  tff(c_5620, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5488, c_5166])).
% 5.49/2.16  tff(c_5233, plain, (![A_196, B_197]: (k1_setfam_1(k2_tarski(A_196, B_197))=k3_xboole_0(A_196, B_197))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.49/2.16  tff(c_5269, plain, (![B_201, A_202]: (k1_setfam_1(k2_tarski(B_201, A_202))=k3_xboole_0(A_202, B_201))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5233])).
% 5.49/2.16  tff(c_5275, plain, (![B_201, A_202]: (k3_xboole_0(B_201, A_202)=k3_xboole_0(A_202, B_201))), inference(superposition, [status(thm), theory('equality')], [c_5269, c_26])).
% 5.49/2.16  tff(c_6022, plain, (![A_240, B_241]: (r1_tarski(k2_tops_1(A_240, B_241), B_241) | ~v4_pre_topc(B_241, A_240) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.49/2.16  tff(c_6026, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_6022])).
% 5.49/2.16  tff(c_6030, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5144, c_6026])).
% 5.49/2.16  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.49/2.16  tff(c_6038, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6030, c_10])).
% 5.49/2.16  tff(c_6145, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5275, c_6038])).
% 5.49/2.16  tff(c_7091, plain, (![A_269, B_270]: (k7_subset_1(u1_struct_0(A_269), B_270, k2_tops_1(A_269, B_270))=k1_tops_1(A_269, B_270) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.49/2.16  tff(c_7095, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_7091])).
% 5.49/2.16  tff(c_7099, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5488, c_7095])).
% 5.49/2.16  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.49/2.16  tff(c_7121, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7099, c_18])).
% 5.49/2.16  tff(c_7134, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6145, c_7121])).
% 5.49/2.16  tff(c_7136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5620, c_7134])).
% 5.49/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.16  
% 5.49/2.16  Inference rules
% 5.49/2.16  ----------------------
% 5.49/2.16  #Ref     : 0
% 5.49/2.16  #Sup     : 1743
% 5.49/2.16  #Fact    : 0
% 5.49/2.16  #Define  : 0
% 5.49/2.16  #Split   : 3
% 5.49/2.16  #Chain   : 0
% 5.49/2.16  #Close   : 0
% 5.49/2.16  
% 5.49/2.16  Ordering : KBO
% 5.49/2.16  
% 5.49/2.16  Simplification rules
% 5.49/2.16  ----------------------
% 5.49/2.16  #Subsume      : 46
% 5.49/2.16  #Demod        : 2013
% 5.49/2.16  #Tautology    : 1438
% 5.49/2.16  #SimpNegUnit  : 4
% 5.49/2.16  #BackRed      : 4
% 5.49/2.16  
% 5.49/2.16  #Partial instantiations: 0
% 5.49/2.16  #Strategies tried      : 1
% 5.49/2.16  
% 5.49/2.16  Timing (in seconds)
% 5.49/2.16  ----------------------
% 5.49/2.16  Preprocessing        : 0.39
% 5.49/2.16  Parsing              : 0.20
% 5.49/2.16  CNF conversion       : 0.02
% 5.49/2.16  Main loop            : 0.97
% 5.49/2.16  Inferencing          : 0.30
% 5.69/2.16  Reduction            : 0.46
% 5.69/2.16  Demodulation         : 0.38
% 5.69/2.16  BG Simplification    : 0.03
% 5.69/2.16  Subsumption          : 0.13
% 5.69/2.16  Abstraction          : 0.05
% 5.69/2.16  MUC search           : 0.00
% 5.69/2.16  Cooper               : 0.00
% 5.69/2.16  Total                : 1.41
% 5.69/2.16  Index Insertion      : 0.00
% 5.69/2.16  Index Deletion       : 0.00
% 5.69/2.16  Index Matching       : 0.00
% 5.69/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

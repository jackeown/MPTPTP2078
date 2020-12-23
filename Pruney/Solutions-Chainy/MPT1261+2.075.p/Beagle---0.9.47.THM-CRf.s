%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:22 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 385 expanded)
%              Number of leaves         :   40 ( 147 expanded)
%              Depth                    :   17
%              Number of atoms          :  144 ( 502 expanded)
%              Number of equality atoms :   83 ( 341 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_68,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6588,plain,(
    ! [A_203,B_204,C_205] :
      ( k7_subset_1(A_203,B_204,C_205) = k4_xboole_0(B_204,C_205)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(A_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6591,plain,(
    ! [C_205] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_205) = k4_xboole_0('#skF_2',C_205) ),
    inference(resolution,[status(thm)],[c_34,c_6588])).

tff(c_40,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_135,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1494,plain,(
    ! [B_106,A_107] :
      ( v4_pre_topc(B_106,A_107)
      | k2_pre_topc(A_107,B_106) != B_106
      | ~ v2_pre_topc(A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1500,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1494])).

tff(c_1504,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_1500])).

tff(c_1505,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_1504])).

tff(c_403,plain,(
    ! [A_65,B_66,C_67] :
      ( k7_subset_1(A_65,B_66,C_67) = k4_xboole_0(B_66,C_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_641,plain,(
    ! [C_76] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_76) = k4_xboole_0('#skF_2',C_76) ),
    inference(resolution,[status(thm)],[c_34,c_403])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_255,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_46])).

tff(c_647,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_255])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_324,plain,(
    ! [A_60,B_61] : k2_xboole_0(k3_xboole_0(A_60,B_61),k4_xboole_0(A_60,B_61)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_370,plain,(
    ! [A_62,B_63] : k4_xboole_0(k3_xboole_0(A_62,B_63),A_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_6])).

tff(c_392,plain,(
    ! [A_64] : k4_xboole_0(A_64,A_64) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_370])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_397,plain,(
    ! [A_64] : k2_xboole_0(k3_xboole_0(A_64,A_64),k1_xboole_0) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_8])).

tff(c_425,plain,(
    ! [A_69] : k2_xboole_0(A_69,k1_xboole_0) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_397])).

tff(c_14,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_136,plain,(
    ! [B_47,A_48] : k3_tarski(k2_tarski(B_47,A_48)) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_16,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_142,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_16])).

tff(c_434,plain,(
    ! [A_69] : k2_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_142])).

tff(c_120,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_261,plain,(
    ! [B_56,A_57] : k1_setfam_1(k2_tarski(B_56,A_57)) = k3_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_120])).

tff(c_22,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_267,plain,(
    ! [B_56,A_57] : k3_xboole_0(B_56,A_57) = k3_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_22])).

tff(c_159,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_16])).

tff(c_174,plain,(
    ! [A_50,B_49] : k4_xboole_0(A_50,k2_xboole_0(B_49,A_50)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_6])).

tff(c_836,plain,(
    ! [A_83,B_84] : k4_xboole_0(k4_xboole_0(A_83,B_84),A_83) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_174])).

tff(c_851,plain,(
    ! [A_83,B_84] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_83,B_84),A_83),k1_xboole_0) = k4_xboole_0(A_83,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_8])).

tff(c_2085,plain,(
    ! [A_120,B_121] : k3_xboole_0(A_120,k4_xboole_0(A_120,B_121)) = k4_xboole_0(A_120,B_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_142,c_267,c_851])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_431,plain,(
    ! [A_69] : k4_xboole_0(k1_xboole_0,A_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_174])).

tff(c_535,plain,(
    ! [A_72,B_73,C_74] : k2_xboole_0(k4_xboole_0(A_72,B_73),k3_xboole_0(A_72,C_74)) = k4_xboole_0(A_72,k4_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_556,plain,(
    ! [A_69,C_74] : k4_xboole_0(k1_xboole_0,k4_xboole_0(A_69,C_74)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_535])).

tff(c_594,plain,(
    ! [C_75] : k3_xboole_0(k1_xboole_0,C_75) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_431,c_556])).

tff(c_656,plain,(
    ! [C_77] : k3_xboole_0(C_77,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_267])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_679,plain,(
    ! [C_77] : k5_xboole_0(C_77,k1_xboole_0) = k4_xboole_0(C_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_4])).

tff(c_707,plain,(
    ! [C_77] : k4_xboole_0(C_77,k1_xboole_0) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_679])).

tff(c_717,plain,(
    ! [C_78] : k4_xboole_0(C_78,k1_xboole_0) = C_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_679])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k4_xboole_0(A_9,B_10),k3_xboole_0(A_9,C_11)) = k4_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_723,plain,(
    ! [C_78,C_11] : k4_xboole_0(C_78,k4_xboole_0(k1_xboole_0,C_11)) = k2_xboole_0(C_78,k3_xboole_0(C_78,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_10])).

tff(c_755,plain,(
    ! [C_78,C_11] : k2_xboole_0(C_78,k3_xboole_0(C_78,C_11)) = C_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_707,c_431,c_723])).

tff(c_2198,plain,(
    ! [A_122,B_123] : k2_xboole_0(A_122,k4_xboole_0(A_122,B_123)) = A_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_755])).

tff(c_2232,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_2198])).

tff(c_1706,plain,(
    ! [A_112,B_113] :
      ( k4_subset_1(u1_struct_0(A_112),B_113,k2_tops_1(A_112,B_113)) = k2_pre_topc(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1710,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1706])).

tff(c_1714,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1710])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_tops_1(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1325,plain,(
    ! [A_98,B_99,C_100] :
      ( k4_subset_1(A_98,B_99,C_100) = k2_xboole_0(B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5663,plain,(
    ! [A_172,B_173,B_174] :
      ( k4_subset_1(u1_struct_0(A_172),B_173,k2_tops_1(A_172,B_174)) = k2_xboole_0(B_173,k2_tops_1(A_172,B_174))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(resolution,[status(thm)],[c_28,c_1325])).

tff(c_5667,plain,(
    ! [B_174] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_174)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_174))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_5663])).

tff(c_6180,plain,(
    ! [B_180] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_180)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_180))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5667])).

tff(c_6187,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_6180])).

tff(c_6192,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2232,c_1714,c_6187])).

tff(c_6194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1505,c_6192])).

tff(c_6195,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6595,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6591,c_6195])).

tff(c_6196,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6990,plain,(
    ! [A_220,B_221] :
      ( k2_pre_topc(A_220,B_221) = B_221
      | ~ v4_pre_topc(B_221,A_220)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6996,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_6990])).

tff(c_7000,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6196,c_6996])).

tff(c_7876,plain,(
    ! [A_252,B_253] :
      ( k7_subset_1(u1_struct_0(A_252),k2_pre_topc(A_252,B_253),k1_tops_1(A_252,B_253)) = k2_tops_1(A_252,B_253)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7885,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7000,c_7876])).

tff(c_7889,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_6591,c_7885])).

tff(c_7891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6595,c_7889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.06  
% 5.17/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.06  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.17/2.06  
% 5.17/2.06  %Foreground sorts:
% 5.17/2.06  
% 5.17/2.06  
% 5.17/2.06  %Background operators:
% 5.17/2.06  
% 5.17/2.06  
% 5.17/2.06  %Foreground operators:
% 5.17/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.17/2.06  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.17/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.17/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.17/2.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.17/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.17/2.06  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.17/2.06  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.17/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.17/2.06  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.17/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.17/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.17/2.06  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.17/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.17/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.17/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.17/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.17/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.17/2.06  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.17/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.17/2.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.17/2.06  
% 5.55/2.08  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.55/2.08  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.55/2.08  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.55/2.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.55/2.08  tff(f_33, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.55/2.08  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.55/2.08  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.55/2.08  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.55/2.08  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.55/2.08  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.55/2.08  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 5.55/2.08  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.55/2.08  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.55/2.08  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.55/2.08  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.55/2.08  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.55/2.08  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.55/2.08  tff(c_6588, plain, (![A_203, B_204, C_205]: (k7_subset_1(A_203, B_204, C_205)=k4_xboole_0(B_204, C_205) | ~m1_subset_1(B_204, k1_zfmisc_1(A_203)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.55/2.08  tff(c_6591, plain, (![C_205]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_205)=k4_xboole_0('#skF_2', C_205))), inference(resolution, [status(thm)], [c_34, c_6588])).
% 5.55/2.08  tff(c_40, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.55/2.08  tff(c_135, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 5.55/2.08  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.55/2.08  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.55/2.08  tff(c_1494, plain, (![B_106, A_107]: (v4_pre_topc(B_106, A_107) | k2_pre_topc(A_107, B_106)!=B_106 | ~v2_pre_topc(A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.55/2.08  tff(c_1500, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1494])).
% 5.55/2.08  tff(c_1504, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_1500])).
% 5.55/2.08  tff(c_1505, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_135, c_1504])).
% 5.55/2.08  tff(c_403, plain, (![A_65, B_66, C_67]: (k7_subset_1(A_65, B_66, C_67)=k4_xboole_0(B_66, C_67) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.55/2.08  tff(c_641, plain, (![C_76]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_76)=k4_xboole_0('#skF_2', C_76))), inference(resolution, [status(thm)], [c_34, c_403])).
% 5.55/2.08  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.55/2.08  tff(c_255, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_135, c_46])).
% 5.55/2.08  tff(c_647, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_641, c_255])).
% 5.55/2.08  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.55/2.08  tff(c_324, plain, (![A_60, B_61]: (k2_xboole_0(k3_xboole_0(A_60, B_61), k4_xboole_0(A_60, B_61))=A_60)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.55/2.08  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.55/2.08  tff(c_370, plain, (![A_62, B_63]: (k4_xboole_0(k3_xboole_0(A_62, B_63), A_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_324, c_6])).
% 5.55/2.08  tff(c_392, plain, (![A_64]: (k4_xboole_0(A_64, A_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_370])).
% 5.55/2.08  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.55/2.08  tff(c_397, plain, (![A_64]: (k2_xboole_0(k3_xboole_0(A_64, A_64), k1_xboole_0)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_392, c_8])).
% 5.55/2.08  tff(c_425, plain, (![A_69]: (k2_xboole_0(A_69, k1_xboole_0)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_397])).
% 5.55/2.08  tff(c_14, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.55/2.08  tff(c_105, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.55/2.08  tff(c_136, plain, (![B_47, A_48]: (k3_tarski(k2_tarski(B_47, A_48))=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_14, c_105])).
% 5.55/2.08  tff(c_16, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.55/2.08  tff(c_142, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_136, c_16])).
% 5.55/2.08  tff(c_434, plain, (![A_69]: (k2_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_425, c_142])).
% 5.55/2.08  tff(c_120, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.55/2.08  tff(c_261, plain, (![B_56, A_57]: (k1_setfam_1(k2_tarski(B_56, A_57))=k3_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_14, c_120])).
% 5.55/2.08  tff(c_22, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.55/2.08  tff(c_267, plain, (![B_56, A_57]: (k3_xboole_0(B_56, A_57)=k3_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_261, c_22])).
% 5.55/2.08  tff(c_159, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_136, c_16])).
% 5.55/2.08  tff(c_174, plain, (![A_50, B_49]: (k4_xboole_0(A_50, k2_xboole_0(B_49, A_50))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_6])).
% 5.55/2.08  tff(c_836, plain, (![A_83, B_84]: (k4_xboole_0(k4_xboole_0(A_83, B_84), A_83)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_324, c_174])).
% 5.55/2.08  tff(c_851, plain, (![A_83, B_84]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_83, B_84), A_83), k1_xboole_0)=k4_xboole_0(A_83, B_84))), inference(superposition, [status(thm), theory('equality')], [c_836, c_8])).
% 5.55/2.08  tff(c_2085, plain, (![A_120, B_121]: (k3_xboole_0(A_120, k4_xboole_0(A_120, B_121))=k4_xboole_0(A_120, B_121))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_142, c_267, c_851])).
% 5.55/2.08  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.55/2.08  tff(c_431, plain, (![A_69]: (k4_xboole_0(k1_xboole_0, A_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_425, c_174])).
% 5.55/2.08  tff(c_535, plain, (![A_72, B_73, C_74]: (k2_xboole_0(k4_xboole_0(A_72, B_73), k3_xboole_0(A_72, C_74))=k4_xboole_0(A_72, k4_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.55/2.08  tff(c_556, plain, (![A_69, C_74]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_69, C_74))=k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, C_74)))), inference(superposition, [status(thm), theory('equality')], [c_431, c_535])).
% 5.55/2.08  tff(c_594, plain, (![C_75]: (k3_xboole_0(k1_xboole_0, C_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_434, c_431, c_556])).
% 5.55/2.08  tff(c_656, plain, (![C_77]: (k3_xboole_0(C_77, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_594, c_267])).
% 5.55/2.08  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.55/2.08  tff(c_679, plain, (![C_77]: (k5_xboole_0(C_77, k1_xboole_0)=k4_xboole_0(C_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_656, c_4])).
% 5.55/2.08  tff(c_707, plain, (![C_77]: (k4_xboole_0(C_77, k1_xboole_0)=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_679])).
% 5.55/2.08  tff(c_717, plain, (![C_78]: (k4_xboole_0(C_78, k1_xboole_0)=C_78)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_679])).
% 5.55/2.08  tff(c_10, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k3_xboole_0(A_9, C_11))=k4_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.55/2.08  tff(c_723, plain, (![C_78, C_11]: (k4_xboole_0(C_78, k4_xboole_0(k1_xboole_0, C_11))=k2_xboole_0(C_78, k3_xboole_0(C_78, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_717, c_10])).
% 5.55/2.08  tff(c_755, plain, (![C_78, C_11]: (k2_xboole_0(C_78, k3_xboole_0(C_78, C_11))=C_78)), inference(demodulation, [status(thm), theory('equality')], [c_707, c_431, c_723])).
% 5.55/2.08  tff(c_2198, plain, (![A_122, B_123]: (k2_xboole_0(A_122, k4_xboole_0(A_122, B_123))=A_122)), inference(superposition, [status(thm), theory('equality')], [c_2085, c_755])).
% 5.55/2.08  tff(c_2232, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_647, c_2198])).
% 5.55/2.08  tff(c_1706, plain, (![A_112, B_113]: (k4_subset_1(u1_struct_0(A_112), B_113, k2_tops_1(A_112, B_113))=k2_pre_topc(A_112, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.55/2.08  tff(c_1710, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1706])).
% 5.55/2.08  tff(c_1714, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1710])).
% 5.55/2.08  tff(c_28, plain, (![A_28, B_29]: (m1_subset_1(k2_tops_1(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.55/2.08  tff(c_1325, plain, (![A_98, B_99, C_100]: (k4_subset_1(A_98, B_99, C_100)=k2_xboole_0(B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.55/2.08  tff(c_5663, plain, (![A_172, B_173, B_174]: (k4_subset_1(u1_struct_0(A_172), B_173, k2_tops_1(A_172, B_174))=k2_xboole_0(B_173, k2_tops_1(A_172, B_174)) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(resolution, [status(thm)], [c_28, c_1325])).
% 5.55/2.08  tff(c_5667, plain, (![B_174]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_174))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_174)) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_5663])).
% 5.55/2.08  tff(c_6180, plain, (![B_180]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_180))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_180)) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5667])).
% 5.55/2.08  tff(c_6187, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_6180])).
% 5.55/2.08  tff(c_6192, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2232, c_1714, c_6187])).
% 5.55/2.08  tff(c_6194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1505, c_6192])).
% 5.55/2.08  tff(c_6195, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 5.55/2.08  tff(c_6595, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6591, c_6195])).
% 5.55/2.08  tff(c_6196, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 5.55/2.08  tff(c_6990, plain, (![A_220, B_221]: (k2_pre_topc(A_220, B_221)=B_221 | ~v4_pre_topc(B_221, A_220) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.55/2.08  tff(c_6996, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_6990])).
% 5.55/2.08  tff(c_7000, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6196, c_6996])).
% 5.55/2.08  tff(c_7876, plain, (![A_252, B_253]: (k7_subset_1(u1_struct_0(A_252), k2_pre_topc(A_252, B_253), k1_tops_1(A_252, B_253))=k2_tops_1(A_252, B_253) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.55/2.08  tff(c_7885, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7000, c_7876])).
% 5.55/2.08  tff(c_7889, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_6591, c_7885])).
% 5.55/2.08  tff(c_7891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6595, c_7889])).
% 5.55/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.08  
% 5.55/2.08  Inference rules
% 5.55/2.08  ----------------------
% 5.55/2.08  #Ref     : 0
% 5.55/2.08  #Sup     : 1954
% 5.55/2.08  #Fact    : 0
% 5.55/2.08  #Define  : 0
% 5.55/2.08  #Split   : 2
% 5.55/2.08  #Chain   : 0
% 5.55/2.08  #Close   : 0
% 5.55/2.08  
% 5.55/2.08  Ordering : KBO
% 5.55/2.08  
% 5.55/2.08  Simplification rules
% 5.55/2.08  ----------------------
% 5.55/2.08  #Subsume      : 37
% 5.55/2.08  #Demod        : 2132
% 5.55/2.08  #Tautology    : 1524
% 5.55/2.08  #SimpNegUnit  : 4
% 5.55/2.08  #BackRed      : 6
% 5.55/2.08  
% 5.55/2.08  #Partial instantiations: 0
% 5.55/2.08  #Strategies tried      : 1
% 5.55/2.08  
% 5.55/2.08  Timing (in seconds)
% 5.55/2.08  ----------------------
% 5.55/2.09  Preprocessing        : 0.32
% 5.55/2.09  Parsing              : 0.18
% 5.64/2.09  CNF conversion       : 0.02
% 5.64/2.09  Main loop            : 1.00
% 5.64/2.09  Inferencing          : 0.29
% 5.64/2.09  Reduction            : 0.49
% 5.64/2.09  Demodulation         : 0.42
% 5.64/2.09  BG Simplification    : 0.03
% 5.64/2.09  Subsumption          : 0.12
% 5.64/2.09  Abstraction          : 0.05
% 5.64/2.09  MUC search           : 0.00
% 5.64/2.09  Cooper               : 0.00
% 5.64/2.09  Total                : 1.36
% 5.64/2.09  Index Insertion      : 0.00
% 5.64/2.09  Index Deletion       : 0.00
% 5.64/2.09  Index Matching       : 0.00
% 5.64/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

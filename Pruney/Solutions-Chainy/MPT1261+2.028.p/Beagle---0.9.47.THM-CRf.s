%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:15 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 196 expanded)
%              Number of leaves         :   47 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  156 ( 341 expanded)
%              Number of equality atoms :   79 ( 135 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_128,negated_conjecture,(
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

tff(f_88,axiom,(
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

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2498,plain,(
    ! [A_225,B_226,C_227] :
      ( k7_subset_1(A_225,B_226,C_227) = k4_xboole_0(B_226,C_227)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(A_225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2505,plain,(
    ! [C_227] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_227) = k4_xboole_0('#skF_2',C_227) ),
    inference(resolution,[status(thm)],[c_46,c_2498])).

tff(c_52,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_354,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1026,plain,(
    ! [B_127,A_128] :
      ( v4_pre_topc(B_127,A_128)
      | k2_pre_topc(A_128,B_127) != B_127
      | ~ v2_pre_topc(A_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1032,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1026])).

tff(c_1044,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_1032])).

tff(c_1045,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_1044])).

tff(c_1187,plain,(
    ! [A_132,B_133] :
      ( k4_subset_1(u1_struct_0(A_132),B_133,k2_tops_1(A_132,B_133)) = k2_pre_topc(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1191,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1187])).

tff(c_1201,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1191])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_403,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_409,plain,(
    ! [A_25] : k4_xboole_0(A_25,k1_xboole_0) = k3_subset_1(A_25,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_403])).

tff(c_415,plain,(
    ! [A_25] : k3_subset_1(A_25,k1_xboole_0) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_409])).

tff(c_359,plain,(
    ! [A_83,B_84] :
      ( k3_subset_1(A_83,k3_subset_1(A_83,B_84)) = B_84
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_367,plain,(
    ! [A_25] : k3_subset_1(A_25,k3_subset_1(A_25,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_359])).

tff(c_417,plain,(
    ! [A_25] : k3_subset_1(A_25,A_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_367])).

tff(c_16,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k2_subset_1(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_16] : m1_subset_1(A_16,k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_416,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_subset_1(A_16,A_16) ),
    inference(resolution,[status(thm)],[c_59,c_403])).

tff(c_451,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_416])).

tff(c_89,plain,(
    ! [A_50,B_51] : r1_tarski(k4_xboole_0(A_50,B_51),A_50) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_127,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_134,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_92,c_127])).

tff(c_183,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_192,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k4_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_183])).

tff(c_452,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_192])).

tff(c_490,plain,(
    ! [A_93,B_94,C_95] :
      ( k7_subset_1(A_93,B_94,C_95) = k4_xboole_0(B_94,C_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_572,plain,(
    ! [C_99] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_99) = k4_xboole_0('#skF_2',C_99) ),
    inference(resolution,[status(thm)],[c_46,c_490])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_243,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_578,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_243])).

tff(c_14,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_160,plain,(
    ! [B_60,A_61] : k1_setfam_1(k2_tarski(B_60,A_61)) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_145])).

tff(c_30,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_166,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,A_61) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_30])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [A_6,B_7] : k3_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k4_xboole_0(A_6,B_7) ),
    inference(resolution,[status(thm)],[c_8,c_127])).

tff(c_803,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_135])).

tff(c_813,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_166,c_803])).

tff(c_195,plain,(
    ! [B_64,A_65] : k3_xboole_0(B_64,A_65) = k3_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_30])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_213,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,k3_xboole_0(A_65,B_64)) = k4_xboole_0(B_64,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_2])).

tff(c_823,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_213])).

tff(c_829,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_823])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_861,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_10])).

tff(c_869,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_861])).

tff(c_38,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k2_tops_1(A_34,B_35),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_944,plain,(
    ! [A_118,B_119,C_120] :
      ( k4_subset_1(A_118,B_119,C_120) = k2_xboole_0(B_119,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1887,plain,(
    ! [A_183,B_184,B_185] :
      ( k4_subset_1(u1_struct_0(A_183),B_184,k2_tops_1(A_183,B_185)) = k2_xboole_0(B_184,k2_tops_1(A_183,B_185))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(resolution,[status(thm)],[c_38,c_944])).

tff(c_1891,plain,(
    ! [B_185] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_185)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_185))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_1887])).

tff(c_1904,plain,(
    ! [B_186] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_186)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_186))
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1891])).

tff(c_1911,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_1904])).

tff(c_1924,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1201,c_869,c_1911])).

tff(c_1926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1045,c_1924])).

tff(c_1927,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1927,c_243])).

tff(c_2122,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2139,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2122,c_52])).

tff(c_2551,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2505,c_2139])).

tff(c_2584,plain,(
    ! [A_231,B_232] :
      ( k2_pre_topc(A_231,B_232) = B_232
      | ~ v4_pre_topc(B_232,A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2587,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2584])).

tff(c_2598,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2122,c_2587])).

tff(c_3186,plain,(
    ! [A_282,B_283] :
      ( k7_subset_1(u1_struct_0(A_282),k2_pre_topc(A_282,B_283),k1_tops_1(A_282,B_283)) = k2_tops_1(A_282,B_283)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3195,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2598,c_3186])).

tff(c_3199,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2505,c_3195])).

tff(c_3201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2551,c_3199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:48:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.79  
% 4.57/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.79  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.57/1.79  
% 4.57/1.79  %Foreground sorts:
% 4.57/1.79  
% 4.57/1.79  
% 4.57/1.79  %Background operators:
% 4.57/1.79  
% 4.57/1.79  
% 4.57/1.79  %Foreground operators:
% 4.57/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.57/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.57/1.79  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.57/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.57/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.57/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.57/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.57/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.57/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.57/1.79  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.57/1.79  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.57/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.57/1.79  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.57/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.57/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.79  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.57/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.57/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.57/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.57/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.57/1.79  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.57/1.79  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.57/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.57/1.79  
% 4.70/1.81  tff(f_128, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.70/1.81  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.70/1.81  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.70/1.81  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.70/1.81  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.70/1.81  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.70/1.81  tff(f_65, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.70/1.81  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.70/1.81  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.70/1.81  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.70/1.81  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.70/1.81  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.70/1.81  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.70/1.81  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.70/1.81  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.70/1.81  tff(f_67, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.70/1.81  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.70/1.81  tff(f_94, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.70/1.81  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.70/1.81  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.70/1.81  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.70/1.81  tff(c_2498, plain, (![A_225, B_226, C_227]: (k7_subset_1(A_225, B_226, C_227)=k4_xboole_0(B_226, C_227) | ~m1_subset_1(B_226, k1_zfmisc_1(A_225)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.70/1.81  tff(c_2505, plain, (![C_227]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_227)=k4_xboole_0('#skF_2', C_227))), inference(resolution, [status(thm)], [c_46, c_2498])).
% 4.70/1.81  tff(c_52, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.70/1.81  tff(c_354, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 4.70/1.81  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.70/1.81  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.70/1.81  tff(c_1026, plain, (![B_127, A_128]: (v4_pre_topc(B_127, A_128) | k2_pre_topc(A_128, B_127)!=B_127 | ~v2_pre_topc(A_128) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.70/1.81  tff(c_1032, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1026])).
% 4.70/1.81  tff(c_1044, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_1032])).
% 4.70/1.81  tff(c_1045, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_354, c_1044])).
% 4.70/1.81  tff(c_1187, plain, (![A_132, B_133]: (k4_subset_1(u1_struct_0(A_132), B_133, k2_tops_1(A_132, B_133))=k2_pre_topc(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.70/1.81  tff(c_1191, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1187])).
% 4.70/1.81  tff(c_1201, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1191])).
% 4.70/1.81  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.70/1.81  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.70/1.81  tff(c_28, plain, (![A_25]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.70/1.81  tff(c_403, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.70/1.81  tff(c_409, plain, (![A_25]: (k4_xboole_0(A_25, k1_xboole_0)=k3_subset_1(A_25, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_403])).
% 4.70/1.81  tff(c_415, plain, (![A_25]: (k3_subset_1(A_25, k1_xboole_0)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_409])).
% 4.70/1.81  tff(c_359, plain, (![A_83, B_84]: (k3_subset_1(A_83, k3_subset_1(A_83, B_84))=B_84 | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.70/1.81  tff(c_367, plain, (![A_25]: (k3_subset_1(A_25, k3_subset_1(A_25, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_359])).
% 4.70/1.81  tff(c_417, plain, (![A_25]: (k3_subset_1(A_25, A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_415, c_367])).
% 4.70/1.81  tff(c_16, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.70/1.81  tff(c_20, plain, (![A_16]: (m1_subset_1(k2_subset_1(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.70/1.81  tff(c_59, plain, (![A_16]: (m1_subset_1(A_16, k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 4.70/1.81  tff(c_416, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_subset_1(A_16, A_16))), inference(resolution, [status(thm)], [c_59, c_403])).
% 4.70/1.81  tff(c_451, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_417, c_416])).
% 4.70/1.81  tff(c_89, plain, (![A_50, B_51]: (r1_tarski(k4_xboole_0(A_50, B_51), A_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.70/1.81  tff(c_92, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 4.70/1.81  tff(c_127, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.70/1.81  tff(c_134, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(resolution, [status(thm)], [c_92, c_127])).
% 4.70/1.81  tff(c_183, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.70/1.81  tff(c_192, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k4_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_134, c_183])).
% 4.70/1.81  tff(c_452, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_451, c_192])).
% 4.70/1.81  tff(c_490, plain, (![A_93, B_94, C_95]: (k7_subset_1(A_93, B_94, C_95)=k4_xboole_0(B_94, C_95) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.70/1.81  tff(c_572, plain, (![C_99]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_99)=k4_xboole_0('#skF_2', C_99))), inference(resolution, [status(thm)], [c_46, c_490])).
% 4.70/1.81  tff(c_58, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.70/1.81  tff(c_243, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 4.70/1.81  tff(c_578, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_572, c_243])).
% 4.70/1.81  tff(c_14, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.70/1.81  tff(c_145, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.70/1.81  tff(c_160, plain, (![B_60, A_61]: (k1_setfam_1(k2_tarski(B_60, A_61))=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_14, c_145])).
% 4.70/1.81  tff(c_30, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.70/1.81  tff(c_166, plain, (![B_60, A_61]: (k3_xboole_0(B_60, A_61)=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_160, c_30])).
% 4.70/1.81  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.70/1.81  tff(c_135, plain, (![A_6, B_7]: (k3_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k4_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_127])).
% 4.70/1.81  tff(c_803, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_578, c_135])).
% 4.70/1.81  tff(c_813, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_578, c_166, c_803])).
% 4.70/1.81  tff(c_195, plain, (![B_64, A_65]: (k3_xboole_0(B_64, A_65)=k3_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_160, c_30])).
% 4.70/1.81  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.70/1.81  tff(c_213, plain, (![B_64, A_65]: (k5_xboole_0(B_64, k3_xboole_0(A_65, B_64))=k4_xboole_0(B_64, A_65))), inference(superposition, [status(thm), theory('equality')], [c_195, c_2])).
% 4.70/1.81  tff(c_823, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_813, c_213])).
% 4.70/1.81  tff(c_829, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_452, c_823])).
% 4.70/1.81  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.70/1.81  tff(c_861, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_829, c_10])).
% 4.70/1.81  tff(c_869, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_861])).
% 4.70/1.81  tff(c_38, plain, (![A_34, B_35]: (m1_subset_1(k2_tops_1(A_34, B_35), k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.70/1.81  tff(c_944, plain, (![A_118, B_119, C_120]: (k4_subset_1(A_118, B_119, C_120)=k2_xboole_0(B_119, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(A_118)) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.70/1.81  tff(c_1887, plain, (![A_183, B_184, B_185]: (k4_subset_1(u1_struct_0(A_183), B_184, k2_tops_1(A_183, B_185))=k2_xboole_0(B_184, k2_tops_1(A_183, B_185)) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(resolution, [status(thm)], [c_38, c_944])).
% 4.70/1.81  tff(c_1891, plain, (![B_185]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_185))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_185)) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_1887])).
% 4.70/1.81  tff(c_1904, plain, (![B_186]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_186))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_186)) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1891])).
% 4.70/1.81  tff(c_1911, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_1904])).
% 4.70/1.81  tff(c_1924, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1201, c_869, c_1911])).
% 4.70/1.81  tff(c_1926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1045, c_1924])).
% 4.70/1.81  tff(c_1927, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 4.70/1.81  tff(c_2121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1927, c_243])).
% 4.70/1.81  tff(c_2122, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 4.70/1.81  tff(c_2139, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2122, c_52])).
% 4.70/1.81  tff(c_2551, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2505, c_2139])).
% 4.70/1.81  tff(c_2584, plain, (![A_231, B_232]: (k2_pre_topc(A_231, B_232)=B_232 | ~v4_pre_topc(B_232, A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.70/1.81  tff(c_2587, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_2584])).
% 4.70/1.81  tff(c_2598, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2122, c_2587])).
% 4.70/1.81  tff(c_3186, plain, (![A_282, B_283]: (k7_subset_1(u1_struct_0(A_282), k2_pre_topc(A_282, B_283), k1_tops_1(A_282, B_283))=k2_tops_1(A_282, B_283) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.70/1.81  tff(c_3195, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2598, c_3186])).
% 4.70/1.81  tff(c_3199, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2505, c_3195])).
% 4.70/1.81  tff(c_3201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2551, c_3199])).
% 4.70/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.81  
% 4.70/1.81  Inference rules
% 4.70/1.81  ----------------------
% 4.70/1.81  #Ref     : 0
% 4.70/1.81  #Sup     : 781
% 4.70/1.81  #Fact    : 0
% 4.70/1.81  #Define  : 0
% 4.70/1.81  #Split   : 3
% 4.70/1.81  #Chain   : 0
% 4.70/1.81  #Close   : 0
% 4.70/1.81  
% 4.70/1.81  Ordering : KBO
% 4.70/1.81  
% 4.70/1.81  Simplification rules
% 4.70/1.81  ----------------------
% 4.70/1.81  #Subsume      : 9
% 4.70/1.81  #Demod        : 376
% 4.70/1.81  #Tautology    : 559
% 4.70/1.81  #SimpNegUnit  : 4
% 4.70/1.81  #BackRed      : 9
% 4.70/1.81  
% 4.70/1.81  #Partial instantiations: 0
% 4.70/1.81  #Strategies tried      : 1
% 4.70/1.81  
% 4.70/1.81  Timing (in seconds)
% 4.70/1.81  ----------------------
% 4.70/1.82  Preprocessing        : 0.34
% 4.70/1.82  Parsing              : 0.19
% 4.70/1.82  CNF conversion       : 0.02
% 4.70/1.82  Main loop            : 0.72
% 4.70/1.82  Inferencing          : 0.26
% 4.70/1.82  Reduction            : 0.26
% 4.70/1.82  Demodulation         : 0.19
% 4.70/1.82  BG Simplification    : 0.03
% 4.70/1.82  Subsumption          : 0.12
% 4.70/1.82  Abstraction          : 0.04
% 4.70/1.82  MUC search           : 0.00
% 4.70/1.82  Cooper               : 0.00
% 4.70/1.82  Total                : 1.10
% 4.70/1.82  Index Insertion      : 0.00
% 4.70/1.82  Index Deletion       : 0.00
% 4.70/1.82  Index Matching       : 0.00
% 4.70/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

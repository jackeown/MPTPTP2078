%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:12 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 220 expanded)
%              Number of leaves         :   48 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 373 expanded)
%              Number of equality atoms :   83 ( 154 expanded)
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

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_94,axiom,(
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

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3318,plain,(
    ! [A_255,B_256,C_257] :
      ( k7_subset_1(A_255,B_256,C_257) = k4_xboole_0(B_256,C_257)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(A_255)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3325,plain,(
    ! [C_257] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_257) = k4_xboole_0('#skF_2',C_257) ),
    inference(resolution,[status(thm)],[c_52,c_3318])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_251,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_355,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1304,plain,(
    ! [B_136,A_137] :
      ( v4_pre_topc(B_136,A_137)
      | k2_pre_topc(A_137,B_136) != B_136
      | ~ v2_pre_topc(A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1310,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1304])).

tff(c_1322,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_1310])).

tff(c_1323,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_1322])).

tff(c_1381,plain,(
    ! [A_141,B_142] :
      ( k4_subset_1(u1_struct_0(A_141),B_142,k2_tops_1(A_141,B_142)) = k2_pre_topc(A_141,B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1385,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1381])).

tff(c_1395,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1385])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_28] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_532,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(A_95,B_96) = k3_subset_1(A_95,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_538,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = k3_subset_1(A_28,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_532])).

tff(c_544,plain,(
    ! [A_28] : k3_subset_1(A_28,k1_xboole_0) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_538])).

tff(c_437,plain,(
    ! [A_89,B_90] :
      ( k3_subset_1(A_89,k3_subset_1(A_89,B_90)) = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_445,plain,(
    ! [A_28] : k3_subset_1(A_28,k3_subset_1(A_28,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_437])).

tff(c_546,plain,(
    ! [A_28] : k3_subset_1(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_445])).

tff(c_22,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_19] : m1_subset_1(k2_subset_1(A_19),k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_65,plain,(
    ! [A_19] : m1_subset_1(A_19,k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_545,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_subset_1(A_19,A_19) ),
    inference(resolution,[status(thm)],[c_65,c_532])).

tff(c_582,plain,(
    ! [A_99] : k4_xboole_0(A_99,A_99) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_545])).

tff(c_18,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_593,plain,(
    ! [A_99] : k5_xboole_0(A_99,k1_xboole_0) = k2_xboole_0(A_99,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_18])).

tff(c_610,plain,(
    ! [A_99] : k5_xboole_0(A_99,k1_xboole_0) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_593])).

tff(c_580,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_545])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_150])).

tff(c_191,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_200,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_191])).

tff(c_581,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_200])).

tff(c_782,plain,(
    ! [A_105,B_106,C_107] :
      ( k7_subset_1(A_105,B_106,C_107) = k4_xboole_0(B_106,C_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_856,plain,(
    ! [C_109] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_109) = k4_xboole_0('#skF_2',C_109) ),
    inference(resolution,[status(thm)],[c_52,c_782])).

tff(c_862,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_251])).

tff(c_20,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_135,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_168,plain,(
    ! [B_63,A_64] : k1_setfam_1(k2_tarski(B_63,A_64)) = k3_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_135])).

tff(c_36,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_174,plain,(
    ! [B_63,A_64] : k3_xboole_0(B_63,A_64) = k3_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_36])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_157,plain,(
    ! [A_9,B_10] : k3_xboole_0(k4_xboole_0(A_9,B_10),A_9) = k4_xboole_0(A_9,B_10) ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_972,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_157])).

tff(c_982,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_174,c_972])).

tff(c_203,plain,(
    ! [B_67,A_68] : k3_xboole_0(B_67,A_68) = k3_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_36])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_221,plain,(
    ! [B_67,A_68] : k5_xboole_0(B_67,k3_xboole_0(A_68,B_67)) = k4_xboole_0(B_67,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_10])).

tff(c_1014,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_221])).

tff(c_1020,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_1014])).

tff(c_1035,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_18])).

tff(c_1043,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_1035])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k2_tops_1(A_37,B_38),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1182,plain,(
    ! [A_126,B_127,C_128] :
      ( k4_subset_1(A_126,B_127,C_128) = k2_xboole_0(B_127,C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(A_126))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2202,plain,(
    ! [A_197,B_198,B_199] :
      ( k4_subset_1(u1_struct_0(A_197),B_198,k2_tops_1(A_197,B_199)) = k2_xboole_0(B_198,k2_tops_1(A_197,B_199))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(resolution,[status(thm)],[c_44,c_1182])).

tff(c_2206,plain,(
    ! [B_199] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_199)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_199))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_2202])).

tff(c_2219,plain,(
    ! [B_200] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_200)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_200))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2206])).

tff(c_2226,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_2219])).

tff(c_2239,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_1043,c_2226])).

tff(c_2241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1323,c_2239])).

tff(c_2242,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_2242])).

tff(c_2709,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2725,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2709,c_58])).

tff(c_3338,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3325,c_2725])).

tff(c_3565,plain,(
    ! [A_278,B_279] :
      ( k2_pre_topc(A_278,B_279) = B_279
      | ~ v4_pre_topc(B_279,A_278)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3571,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_3565])).

tff(c_3583,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2709,c_3571])).

tff(c_3974,plain,(
    ! [A_306,B_307] :
      ( k7_subset_1(u1_struct_0(A_306),k2_pre_topc(A_306,B_307),k1_tops_1(A_306,B_307)) = k2_tops_1(A_306,B_307)
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3983,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3583,c_3974])).

tff(c_3987,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3325,c_3983])).

tff(c_3989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3338,c_3987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:12:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.90  
% 4.88/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.90  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.88/1.90  
% 4.88/1.90  %Foreground sorts:
% 4.88/1.90  
% 4.88/1.90  
% 4.88/1.90  %Background operators:
% 4.88/1.90  
% 4.88/1.90  
% 4.88/1.90  %Foreground operators:
% 4.88/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.88/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.88/1.90  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.88/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.88/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.88/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.88/1.90  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.88/1.90  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.88/1.90  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.88/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.88/1.90  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.88/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.88/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.88/1.90  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.88/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.88/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.88/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.88/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.88/1.90  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.88/1.90  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.88/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.88/1.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.88/1.90  
% 4.88/1.92  tff(f_134, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.88/1.92  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.88/1.92  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.88/1.92  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.88/1.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.88/1.92  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.88/1.92  tff(f_71, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.88/1.92  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.88/1.92  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.88/1.92  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.88/1.92  tff(f_55, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.88/1.92  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.88/1.92  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.88/1.92  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.88/1.92  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.88/1.92  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.88/1.92  tff(f_73, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.88/1.92  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.88/1.92  tff(f_100, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.88/1.92  tff(f_65, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.88/1.92  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.88/1.92  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.88/1.92  tff(c_3318, plain, (![A_255, B_256, C_257]: (k7_subset_1(A_255, B_256, C_257)=k4_xboole_0(B_256, C_257) | ~m1_subset_1(B_256, k1_zfmisc_1(A_255)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.88/1.92  tff(c_3325, plain, (![C_257]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_257)=k4_xboole_0('#skF_2', C_257))), inference(resolution, [status(thm)], [c_52, c_3318])).
% 4.88/1.92  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.88/1.92  tff(c_251, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 4.88/1.92  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.88/1.92  tff(c_355, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 4.88/1.92  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.88/1.92  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.88/1.92  tff(c_1304, plain, (![B_136, A_137]: (v4_pre_topc(B_136, A_137) | k2_pre_topc(A_137, B_136)!=B_136 | ~v2_pre_topc(A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.92  tff(c_1310, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1304])).
% 4.88/1.92  tff(c_1322, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_1310])).
% 4.88/1.92  tff(c_1323, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_355, c_1322])).
% 4.88/1.92  tff(c_1381, plain, (![A_141, B_142]: (k4_subset_1(u1_struct_0(A_141), B_142, k2_tops_1(A_141, B_142))=k2_pre_topc(A_141, B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.88/1.92  tff(c_1385, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1381])).
% 4.88/1.92  tff(c_1395, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1385])).
% 4.88/1.92  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.88/1.92  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/1.92  tff(c_34, plain, (![A_28]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.88/1.92  tff(c_532, plain, (![A_95, B_96]: (k4_xboole_0(A_95, B_96)=k3_subset_1(A_95, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.88/1.92  tff(c_538, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=k3_subset_1(A_28, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_532])).
% 4.88/1.92  tff(c_544, plain, (![A_28]: (k3_subset_1(A_28, k1_xboole_0)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_538])).
% 4.88/1.92  tff(c_437, plain, (![A_89, B_90]: (k3_subset_1(A_89, k3_subset_1(A_89, B_90))=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.88/1.92  tff(c_445, plain, (![A_28]: (k3_subset_1(A_28, k3_subset_1(A_28, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_437])).
% 4.88/1.92  tff(c_546, plain, (![A_28]: (k3_subset_1(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_544, c_445])).
% 4.88/1.92  tff(c_22, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.88/1.92  tff(c_26, plain, (![A_19]: (m1_subset_1(k2_subset_1(A_19), k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.88/1.92  tff(c_65, plain, (![A_19]: (m1_subset_1(A_19, k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 4.88/1.92  tff(c_545, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_subset_1(A_19, A_19))), inference(resolution, [status(thm)], [c_65, c_532])).
% 4.88/1.92  tff(c_582, plain, (![A_99]: (k4_xboole_0(A_99, A_99)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_546, c_545])).
% 4.88/1.92  tff(c_18, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.88/1.92  tff(c_593, plain, (![A_99]: (k5_xboole_0(A_99, k1_xboole_0)=k2_xboole_0(A_99, A_99))), inference(superposition, [status(thm), theory('equality')], [c_582, c_18])).
% 4.88/1.92  tff(c_610, plain, (![A_99]: (k5_xboole_0(A_99, k1_xboole_0)=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_593])).
% 4.88/1.92  tff(c_580, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_546, c_545])).
% 4.88/1.92  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.88/1.92  tff(c_150, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.88/1.92  tff(c_158, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_150])).
% 4.88/1.92  tff(c_191, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.88/1.92  tff(c_200, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_158, c_191])).
% 4.88/1.92  tff(c_581, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_580, c_200])).
% 4.88/1.92  tff(c_782, plain, (![A_105, B_106, C_107]: (k7_subset_1(A_105, B_106, C_107)=k4_xboole_0(B_106, C_107) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.88/1.92  tff(c_856, plain, (![C_109]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_109)=k4_xboole_0('#skF_2', C_109))), inference(resolution, [status(thm)], [c_52, c_782])).
% 4.88/1.92  tff(c_862, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_856, c_251])).
% 4.88/1.92  tff(c_20, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.88/1.92  tff(c_135, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/1.92  tff(c_168, plain, (![B_63, A_64]: (k1_setfam_1(k2_tarski(B_63, A_64))=k3_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_20, c_135])).
% 4.88/1.92  tff(c_36, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/1.92  tff(c_174, plain, (![B_63, A_64]: (k3_xboole_0(B_63, A_64)=k3_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_168, c_36])).
% 4.88/1.92  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.88/1.92  tff(c_157, plain, (![A_9, B_10]: (k3_xboole_0(k4_xboole_0(A_9, B_10), A_9)=k4_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_14, c_150])).
% 4.88/1.92  tff(c_972, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_862, c_157])).
% 4.88/1.92  tff(c_982, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_174, c_972])).
% 4.88/1.92  tff(c_203, plain, (![B_67, A_68]: (k3_xboole_0(B_67, A_68)=k3_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_168, c_36])).
% 4.88/1.92  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.88/1.92  tff(c_221, plain, (![B_67, A_68]: (k5_xboole_0(B_67, k3_xboole_0(A_68, B_67))=k4_xboole_0(B_67, A_68))), inference(superposition, [status(thm), theory('equality')], [c_203, c_10])).
% 4.88/1.92  tff(c_1014, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_982, c_221])).
% 4.88/1.92  tff(c_1020, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_581, c_1014])).
% 4.88/1.92  tff(c_1035, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1020, c_18])).
% 4.88/1.92  tff(c_1043, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_610, c_1035])).
% 4.88/1.92  tff(c_44, plain, (![A_37, B_38]: (m1_subset_1(k2_tops_1(A_37, B_38), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.88/1.92  tff(c_1182, plain, (![A_126, B_127, C_128]: (k4_subset_1(A_126, B_127, C_128)=k2_xboole_0(B_127, C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(A_126)) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.88/1.92  tff(c_2202, plain, (![A_197, B_198, B_199]: (k4_subset_1(u1_struct_0(A_197), B_198, k2_tops_1(A_197, B_199))=k2_xboole_0(B_198, k2_tops_1(A_197, B_199)) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(resolution, [status(thm)], [c_44, c_1182])).
% 4.88/1.92  tff(c_2206, plain, (![B_199]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_199))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_199)) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_2202])).
% 4.88/1.92  tff(c_2219, plain, (![B_200]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_200))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_200)) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2206])).
% 4.88/1.92  tff(c_2226, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_2219])).
% 4.88/1.92  tff(c_2239, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1395, c_1043, c_2226])).
% 4.88/1.92  tff(c_2241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1323, c_2239])).
% 4.88/1.92  tff(c_2242, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 4.88/1.92  tff(c_2708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_2242])).
% 4.88/1.92  tff(c_2709, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 4.88/1.92  tff(c_2725, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2709, c_58])).
% 4.88/1.92  tff(c_3338, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3325, c_2725])).
% 4.88/1.92  tff(c_3565, plain, (![A_278, B_279]: (k2_pre_topc(A_278, B_279)=B_279 | ~v4_pre_topc(B_279, A_278) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.92  tff(c_3571, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_3565])).
% 4.88/1.92  tff(c_3583, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2709, c_3571])).
% 4.88/1.92  tff(c_3974, plain, (![A_306, B_307]: (k7_subset_1(u1_struct_0(A_306), k2_pre_topc(A_306, B_307), k1_tops_1(A_306, B_307))=k2_tops_1(A_306, B_307) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_306))) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.88/1.92  tff(c_3983, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3583, c_3974])).
% 4.88/1.92  tff(c_3987, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3325, c_3983])).
% 4.88/1.92  tff(c_3989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3338, c_3987])).
% 4.88/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.92  
% 4.88/1.92  Inference rules
% 4.88/1.92  ----------------------
% 4.88/1.92  #Ref     : 0
% 4.88/1.92  #Sup     : 952
% 4.88/1.92  #Fact    : 0
% 4.88/1.92  #Define  : 0
% 4.88/1.92  #Split   : 7
% 4.88/1.92  #Chain   : 0
% 4.88/1.92  #Close   : 0
% 4.88/1.92  
% 4.88/1.92  Ordering : KBO
% 4.88/1.92  
% 4.88/1.92  Simplification rules
% 4.88/1.92  ----------------------
% 4.88/1.92  #Subsume      : 25
% 4.88/1.92  #Demod        : 563
% 4.88/1.92  #Tautology    : 681
% 4.88/1.92  #SimpNegUnit  : 3
% 4.88/1.92  #BackRed      : 19
% 4.88/1.92  
% 4.88/1.92  #Partial instantiations: 0
% 4.88/1.92  #Strategies tried      : 1
% 4.88/1.92  
% 4.88/1.92  Timing (in seconds)
% 4.88/1.92  ----------------------
% 4.88/1.92  Preprocessing        : 0.35
% 4.88/1.92  Parsing              : 0.19
% 4.88/1.92  CNF conversion       : 0.02
% 4.88/1.92  Main loop            : 0.80
% 4.88/1.92  Inferencing          : 0.29
% 4.88/1.92  Reduction            : 0.30
% 4.88/1.92  Demodulation         : 0.23
% 4.88/1.92  BG Simplification    : 0.03
% 4.88/1.92  Subsumption          : 0.13
% 4.88/1.92  Abstraction          : 0.04
% 4.88/1.92  MUC search           : 0.00
% 4.88/1.92  Cooper               : 0.00
% 4.88/1.92  Total                : 1.19
% 4.88/1.92  Index Insertion      : 0.00
% 4.88/1.92  Index Deletion       : 0.00
% 4.88/1.92  Index Matching       : 0.00
% 4.88/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------

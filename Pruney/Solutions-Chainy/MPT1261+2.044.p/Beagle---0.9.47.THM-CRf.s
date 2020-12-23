%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:18 EST 2020

% Result     : Theorem 9.46s
% Output     : CNFRefutation 9.58s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 190 expanded)
%              Number of leaves         :   44 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  146 ( 332 expanded)
%              Number of equality atoms :   67 ( 119 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff(f_120,negated_conjecture,(
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

tff(f_80,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_13174,plain,(
    ! [A_322,B_323,C_324] :
      ( k7_subset_1(A_322,B_323,C_324) = k4_xboole_0(B_323,C_324)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(A_322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13183,plain,(
    ! [C_324] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_324) = k4_xboole_0('#skF_2',C_324) ),
    inference(resolution,[status(thm)],[c_42,c_13174])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_90,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2306,plain,(
    ! [B_141,A_142] :
      ( v4_pre_topc(B_141,A_142)
      | k2_pre_topc(A_142,B_141) != B_141
      | ~ v2_pre_topc(A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2320,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2306])).

tff(c_2326,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_2320])).

tff(c_2327,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2326])).

tff(c_488,plain,(
    ! [A_87,B_88,C_89] :
      ( k7_subset_1(A_87,B_88,C_89) = k4_xboole_0(B_88,C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_551,plain,(
    ! [C_92] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_92) = k4_xboole_0('#skF_2',C_92) ),
    inference(resolution,[status(thm)],[c_42,c_488])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_232,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_54])).

tff(c_557,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_232])).

tff(c_22,plain,(
    ! [A_21,B_22] : k6_subset_1(A_21,B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_16,B_17] : m1_subset_1(k6_subset_1(A_16,B_17),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    ! [A_16,B_17] : m1_subset_1(k4_xboole_0(A_16,B_17),k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2124,plain,(
    ! [A_136,B_137,C_138] :
      ( k4_subset_1(A_136,B_137,C_138) = k2_xboole_0(B_137,C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(A_136))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7544,plain,(
    ! [A_231,B_232,B_233] :
      ( k4_subset_1(A_231,B_232,k3_subset_1(A_231,B_233)) = k2_xboole_0(B_232,k3_subset_1(A_231,B_233))
      | ~ m1_subset_1(B_232,k1_zfmisc_1(A_231))
      | ~ m1_subset_1(B_233,k1_zfmisc_1(A_231)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2124])).

tff(c_12000,plain,(
    ! [A_277,B_278,B_279] :
      ( k4_subset_1(A_277,k4_xboole_0(A_277,B_278),k3_subset_1(A_277,B_279)) = k2_xboole_0(k4_xboole_0(A_277,B_278),k3_subset_1(A_277,B_279))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(A_277)) ) ),
    inference(resolution,[status(thm)],[c_55,c_7544])).

tff(c_14,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( k4_subset_1(A_26,B_27,k3_subset_1(A_26,B_27)) = k2_subset_1(A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_610,plain,(
    ! [A_95,B_96] :
      ( k4_subset_1(A_95,B_96,k3_subset_1(A_95,B_96)) = A_95
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_621,plain,(
    ! [A_16,B_17] : k4_subset_1(A_16,k4_xboole_0(A_16,B_17),k3_subset_1(A_16,k4_xboole_0(A_16,B_17))) = A_16 ),
    inference(resolution,[status(thm)],[c_55,c_610])).

tff(c_12007,plain,(
    ! [A_277,B_278] :
      ( k2_xboole_0(k4_xboole_0(A_277,B_278),k3_subset_1(A_277,k4_xboole_0(A_277,B_278))) = A_277
      | ~ m1_subset_1(k4_xboole_0(A_277,B_278),k1_zfmisc_1(A_277)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12000,c_621])).

tff(c_12049,plain,(
    ! [A_277,B_278] : k2_xboole_0(k4_xboole_0(A_277,B_278),k3_subset_1(A_277,k4_xboole_0(A_277,B_278))) = A_277 ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_12007])).

tff(c_12062,plain,(
    ! [A_280,B_281] : k2_xboole_0(k4_xboole_0(A_280,B_281),k3_subset_1(A_280,k4_xboole_0(A_280,B_281))) = A_280 ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_12007])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(resolution,[status(thm)],[c_8,c_139])).

tff(c_10,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_389,plain,(
    ! [A_81,B_82] : k1_setfam_1(k2_tarski(A_81,B_82)) = k3_xboole_0(B_82,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_124])).

tff(c_28,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_412,plain,(
    ! [B_83,A_84] : k3_xboole_0(B_83,A_84) = k3_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_28])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_499,plain,(
    ! [A_90,B_91] : k2_xboole_0(A_90,k3_xboole_0(B_91,A_90)) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_4])).

tff(c_533,plain,(
    ! [A_7,B_8] : k2_xboole_0(k2_xboole_0(A_7,B_8),A_7) = k2_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_499])).

tff(c_12158,plain,(
    ! [A_280,B_281] : k2_xboole_0(k4_xboole_0(A_280,B_281),k3_subset_1(A_280,k4_xboole_0(A_280,B_281))) = k2_xboole_0(A_280,k4_xboole_0(A_280,B_281)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12062,c_533])).

tff(c_12356,plain,(
    ! [A_285,B_286] : k2_xboole_0(A_285,k4_xboole_0(A_285,B_286)) = A_285 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12049,c_12158])).

tff(c_12506,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_12356])).

tff(c_2597,plain,(
    ! [A_148,B_149] :
      ( k4_subset_1(u1_struct_0(A_148),B_149,k2_tops_1(A_148,B_149)) = k2_pre_topc(A_148,B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2607,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2597])).

tff(c_2613,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2607])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_tops_1(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9836,plain,(
    ! [A_254,B_255,B_256] :
      ( k4_subset_1(u1_struct_0(A_254),B_255,k2_tops_1(A_254,B_256)) = k2_xboole_0(B_255,k2_tops_1(A_254,B_256))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(resolution,[status(thm)],[c_34,c_2124])).

tff(c_9846,plain,(
    ! [B_256] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_256)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_256))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_9836])).

tff(c_9855,plain,(
    ! [B_257] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_257)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_257))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9846])).

tff(c_9870,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_9855])).

tff(c_9877,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2613,c_9870])).

tff(c_12781,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12506,c_9877])).

tff(c_12783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2327,c_12781])).

tff(c_12784,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_13255,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13183,c_12784])).

tff(c_12785,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_13623,plain,(
    ! [A_344,B_345] :
      ( k2_pre_topc(A_344,B_345) = B_345
      | ~ v4_pre_topc(B_345,A_344)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_13637,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_13623])).

tff(c_13643,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12785,c_13637])).

tff(c_15047,plain,(
    ! [A_381,B_382] :
      ( k7_subset_1(u1_struct_0(A_381),k2_pre_topc(A_381,B_382),k1_tops_1(A_381,B_382)) = k2_tops_1(A_381,B_382)
      | ~ m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ l1_pre_topc(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_15056,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13643,c_15047])).

tff(c_15060,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_13183,c_15056])).

tff(c_15062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13255,c_15060])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.46/3.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.46/3.28  
% 9.46/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/3.29  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 9.58/3.29  
% 9.58/3.29  %Foreground sorts:
% 9.58/3.29  
% 9.58/3.29  
% 9.58/3.29  %Background operators:
% 9.58/3.29  
% 9.58/3.29  
% 9.58/3.29  %Foreground operators:
% 9.58/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.58/3.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.58/3.29  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.58/3.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.58/3.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.58/3.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.58/3.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.58/3.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.58/3.29  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.58/3.29  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.58/3.29  tff('#skF_2', type, '#skF_2': $i).
% 9.58/3.29  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.58/3.29  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.58/3.29  tff('#skF_1', type, '#skF_1': $i).
% 9.58/3.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.58/3.29  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.58/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.58/3.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.58/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.58/3.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.58/3.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.58/3.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.58/3.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.58/3.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.58/3.29  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.58/3.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.58/3.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.58/3.29  
% 9.58/3.31  tff(f_120, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 9.58/3.31  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.58/3.31  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 9.58/3.31  tff(f_55, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.58/3.31  tff(f_47, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 9.58/3.31  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.58/3.31  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.58/3.31  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.58/3.31  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 9.58/3.31  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.58/3.31  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.58/3.31  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.58/3.31  tff(f_65, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.58/3.31  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 9.58/3.31  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 9.58/3.31  tff(f_86, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 9.58/3.31  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 9.58/3.31  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.58/3.31  tff(c_13174, plain, (![A_322, B_323, C_324]: (k7_subset_1(A_322, B_323, C_324)=k4_xboole_0(B_323, C_324) | ~m1_subset_1(B_323, k1_zfmisc_1(A_322)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.58/3.31  tff(c_13183, plain, (![C_324]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_324)=k4_xboole_0('#skF_2', C_324))), inference(resolution, [status(thm)], [c_42, c_13174])).
% 9.58/3.31  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.58/3.31  tff(c_90, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 9.58/3.31  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.58/3.31  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.58/3.31  tff(c_2306, plain, (![B_141, A_142]: (v4_pre_topc(B_141, A_142) | k2_pre_topc(A_142, B_141)!=B_141 | ~v2_pre_topc(A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.58/3.31  tff(c_2320, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2306])).
% 9.58/3.31  tff(c_2326, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_2320])).
% 9.58/3.31  tff(c_2327, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_90, c_2326])).
% 9.58/3.31  tff(c_488, plain, (![A_87, B_88, C_89]: (k7_subset_1(A_87, B_88, C_89)=k4_xboole_0(B_88, C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.58/3.31  tff(c_551, plain, (![C_92]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_92)=k4_xboole_0('#skF_2', C_92))), inference(resolution, [status(thm)], [c_42, c_488])).
% 9.58/3.31  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.58/3.31  tff(c_232, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_90, c_54])).
% 9.58/3.31  tff(c_557, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_551, c_232])).
% 9.58/3.31  tff(c_22, plain, (![A_21, B_22]: (k6_subset_1(A_21, B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.58/3.31  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(k6_subset_1(A_16, B_17), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.58/3.31  tff(c_55, plain, (![A_16, B_17]: (m1_subset_1(k4_xboole_0(A_16, B_17), k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18])).
% 9.58/3.31  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k3_subset_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.58/3.31  tff(c_2124, plain, (![A_136, B_137, C_138]: (k4_subset_1(A_136, B_137, C_138)=k2_xboole_0(B_137, C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(A_136)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.58/3.31  tff(c_7544, plain, (![A_231, B_232, B_233]: (k4_subset_1(A_231, B_232, k3_subset_1(A_231, B_233))=k2_xboole_0(B_232, k3_subset_1(A_231, B_233)) | ~m1_subset_1(B_232, k1_zfmisc_1(A_231)) | ~m1_subset_1(B_233, k1_zfmisc_1(A_231)))), inference(resolution, [status(thm)], [c_16, c_2124])).
% 9.58/3.31  tff(c_12000, plain, (![A_277, B_278, B_279]: (k4_subset_1(A_277, k4_xboole_0(A_277, B_278), k3_subset_1(A_277, B_279))=k2_xboole_0(k4_xboole_0(A_277, B_278), k3_subset_1(A_277, B_279)) | ~m1_subset_1(B_279, k1_zfmisc_1(A_277)))), inference(resolution, [status(thm)], [c_55, c_7544])).
% 9.58/3.31  tff(c_14, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.58/3.31  tff(c_26, plain, (![A_26, B_27]: (k4_subset_1(A_26, B_27, k3_subset_1(A_26, B_27))=k2_subset_1(A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.58/3.31  tff(c_610, plain, (![A_95, B_96]: (k4_subset_1(A_95, B_96, k3_subset_1(A_95, B_96))=A_95 | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 9.58/3.31  tff(c_621, plain, (![A_16, B_17]: (k4_subset_1(A_16, k4_xboole_0(A_16, B_17), k3_subset_1(A_16, k4_xboole_0(A_16, B_17)))=A_16)), inference(resolution, [status(thm)], [c_55, c_610])).
% 9.58/3.31  tff(c_12007, plain, (![A_277, B_278]: (k2_xboole_0(k4_xboole_0(A_277, B_278), k3_subset_1(A_277, k4_xboole_0(A_277, B_278)))=A_277 | ~m1_subset_1(k4_xboole_0(A_277, B_278), k1_zfmisc_1(A_277)))), inference(superposition, [status(thm), theory('equality')], [c_12000, c_621])).
% 9.58/3.31  tff(c_12049, plain, (![A_277, B_278]: (k2_xboole_0(k4_xboole_0(A_277, B_278), k3_subset_1(A_277, k4_xboole_0(A_277, B_278)))=A_277)), inference(demodulation, [status(thm), theory('equality')], [c_55, c_12007])).
% 9.58/3.31  tff(c_12062, plain, (![A_280, B_281]: (k2_xboole_0(k4_xboole_0(A_280, B_281), k3_subset_1(A_280, k4_xboole_0(A_280, B_281)))=A_280)), inference(demodulation, [status(thm), theory('equality')], [c_55, c_12007])).
% 9.58/3.31  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.58/3.31  tff(c_139, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.58/3.31  tff(c_147, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(resolution, [status(thm)], [c_8, c_139])).
% 9.58/3.31  tff(c_10, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.58/3.31  tff(c_124, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.58/3.31  tff(c_389, plain, (![A_81, B_82]: (k1_setfam_1(k2_tarski(A_81, B_82))=k3_xboole_0(B_82, A_81))), inference(superposition, [status(thm), theory('equality')], [c_10, c_124])).
% 9.58/3.31  tff(c_28, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.58/3.31  tff(c_412, plain, (![B_83, A_84]: (k3_xboole_0(B_83, A_84)=k3_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_389, c_28])).
% 9.58/3.31  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.58/3.31  tff(c_499, plain, (![A_90, B_91]: (k2_xboole_0(A_90, k3_xboole_0(B_91, A_90))=A_90)), inference(superposition, [status(thm), theory('equality')], [c_412, c_4])).
% 9.58/3.31  tff(c_533, plain, (![A_7, B_8]: (k2_xboole_0(k2_xboole_0(A_7, B_8), A_7)=k2_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_147, c_499])).
% 9.58/3.31  tff(c_12158, plain, (![A_280, B_281]: (k2_xboole_0(k4_xboole_0(A_280, B_281), k3_subset_1(A_280, k4_xboole_0(A_280, B_281)))=k2_xboole_0(A_280, k4_xboole_0(A_280, B_281)))), inference(superposition, [status(thm), theory('equality')], [c_12062, c_533])).
% 9.58/3.31  tff(c_12356, plain, (![A_285, B_286]: (k2_xboole_0(A_285, k4_xboole_0(A_285, B_286))=A_285)), inference(demodulation, [status(thm), theory('equality')], [c_12049, c_12158])).
% 9.58/3.31  tff(c_12506, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_557, c_12356])).
% 9.58/3.31  tff(c_2597, plain, (![A_148, B_149]: (k4_subset_1(u1_struct_0(A_148), B_149, k2_tops_1(A_148, B_149))=k2_pre_topc(A_148, B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.58/3.31  tff(c_2607, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2597])).
% 9.58/3.31  tff(c_2613, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2607])).
% 9.58/3.31  tff(c_34, plain, (![A_33, B_34]: (m1_subset_1(k2_tops_1(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.58/3.31  tff(c_9836, plain, (![A_254, B_255, B_256]: (k4_subset_1(u1_struct_0(A_254), B_255, k2_tops_1(A_254, B_256))=k2_xboole_0(B_255, k2_tops_1(A_254, B_256)) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(resolution, [status(thm)], [c_34, c_2124])).
% 9.58/3.31  tff(c_9846, plain, (![B_256]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_256))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_256)) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_9836])).
% 9.58/3.31  tff(c_9855, plain, (![B_257]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_257))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_257)) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_9846])).
% 9.58/3.31  tff(c_9870, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_9855])).
% 9.58/3.31  tff(c_9877, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2613, c_9870])).
% 9.58/3.31  tff(c_12781, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12506, c_9877])).
% 9.58/3.31  tff(c_12783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2327, c_12781])).
% 9.58/3.31  tff(c_12784, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 9.58/3.31  tff(c_13255, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13183, c_12784])).
% 9.58/3.31  tff(c_12785, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 9.58/3.31  tff(c_13623, plain, (![A_344, B_345]: (k2_pre_topc(A_344, B_345)=B_345 | ~v4_pre_topc(B_345, A_344) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.58/3.31  tff(c_13637, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_13623])).
% 9.58/3.31  tff(c_13643, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12785, c_13637])).
% 9.58/3.31  tff(c_15047, plain, (![A_381, B_382]: (k7_subset_1(u1_struct_0(A_381), k2_pre_topc(A_381, B_382), k1_tops_1(A_381, B_382))=k2_tops_1(A_381, B_382) | ~m1_subset_1(B_382, k1_zfmisc_1(u1_struct_0(A_381))) | ~l1_pre_topc(A_381))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.58/3.31  tff(c_15056, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13643, c_15047])).
% 9.58/3.31  tff(c_15060, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_13183, c_15056])).
% 9.58/3.31  tff(c_15062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13255, c_15060])).
% 9.58/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/3.31  
% 9.58/3.31  Inference rules
% 9.58/3.31  ----------------------
% 9.58/3.31  #Ref     : 0
% 9.58/3.31  #Sup     : 3759
% 9.58/3.31  #Fact    : 0
% 9.58/3.31  #Define  : 0
% 9.58/3.31  #Split   : 2
% 9.58/3.31  #Chain   : 0
% 9.58/3.31  #Close   : 0
% 9.58/3.31  
% 9.58/3.31  Ordering : KBO
% 9.58/3.31  
% 9.58/3.31  Simplification rules
% 9.58/3.31  ----------------------
% 9.58/3.31  #Subsume      : 271
% 9.58/3.31  #Demod        : 5681
% 9.58/3.31  #Tautology    : 2882
% 9.58/3.31  #SimpNegUnit  : 4
% 9.58/3.31  #BackRed      : 3
% 9.58/3.31  
% 9.58/3.31  #Partial instantiations: 0
% 9.58/3.31  #Strategies tried      : 1
% 9.58/3.31  
% 9.58/3.31  Timing (in seconds)
% 9.58/3.31  ----------------------
% 9.58/3.31  Preprocessing        : 0.36
% 9.58/3.31  Parsing              : 0.19
% 9.58/3.31  CNF conversion       : 0.02
% 9.58/3.31  Main loop            : 2.17
% 9.58/3.31  Inferencing          : 0.54
% 9.58/3.31  Reduction            : 1.18
% 9.58/3.31  Demodulation         : 1.03
% 9.58/3.31  BG Simplification    : 0.05
% 9.58/3.31  Subsumption          : 0.28
% 9.58/3.31  Abstraction          : 0.11
% 9.58/3.31  MUC search           : 0.00
% 9.58/3.31  Cooper               : 0.00
% 9.58/3.31  Total                : 2.57
% 9.58/3.31  Index Insertion      : 0.00
% 9.58/3.31  Index Deletion       : 0.00
% 9.58/3.31  Index Matching       : 0.00
% 9.58/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

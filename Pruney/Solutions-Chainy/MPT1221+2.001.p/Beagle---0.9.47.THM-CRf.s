%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:23 EST 2020

% Result     : Theorem 12.96s
% Output     : CNFRefutation 13.25s
% Verified   : 
% Statistics : Number of formulae       :  233 (1144 expanded)
%              Number of leaves         :   46 ( 403 expanded)
%              Depth                    :   21
%              Number of atoms          :  357 (2165 expanded)
%              Number of equality atoms :  124 ( 675 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_94,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_68,plain,(
    ! [A_51] :
      ( l1_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_105,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_11096,plain,(
    ! [A_506] :
      ( u1_struct_0(A_506) = k2_struct_0(A_506)
      | ~ l1_pre_topc(A_506) ) ),
    inference(resolution,[status(thm)],[c_68,c_105])).

tff(c_11100,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_11096])).

tff(c_144,plain,(
    ! [A_62] :
      ( u1_struct_0(A_62) = k2_struct_0(A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_68,c_105])).

tff(c_148,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_144])).

tff(c_80,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_110,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_149,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_110])).

tff(c_74,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_227,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_148,c_74])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_150,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_70])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,(
    ! [A_27] : m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_81,plain,(
    ! [A_27] : m1_subset_1(A_27,k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_38,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_155,plain,(
    ! [A_63,B_64] : k1_setfam_1(k2_tarski(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_170,plain,(
    ! [B_65,A_66] : k1_setfam_1(k2_tarski(B_65,A_66)) = k3_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_155])).

tff(c_58,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_176,plain,(
    ! [B_65,A_66] : k3_xboole_0(B_65,A_66) = k3_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_58])).

tff(c_1179,plain,(
    ! [A_147,B_148,C_149] :
      ( k9_subset_1(A_147,B_148,C_149) = k3_xboole_0(B_148,C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1203,plain,(
    ! [A_27,B_148] : k9_subset_1(A_27,B_148,A_27) = k3_xboole_0(B_148,A_27) ),
    inference(resolution,[status(thm)],[c_81,c_1179])).

tff(c_1258,plain,(
    ! [A_157,C_158,B_159] :
      ( k9_subset_1(A_157,C_158,B_159) = k9_subset_1(A_157,B_159,C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1273,plain,(
    ! [A_27,B_159] : k9_subset_1(A_27,B_159,A_27) = k9_subset_1(A_27,A_27,B_159) ),
    inference(resolution,[status(thm)],[c_81,c_1258])).

tff(c_1284,plain,(
    ! [A_27,B_159] : k9_subset_1(A_27,A_27,B_159) = k3_xboole_0(B_159,A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_1273])).

tff(c_2682,plain,(
    ! [A_211,B_212,C_213] :
      ( k9_subset_1(A_211,B_212,k3_subset_1(A_211,C_213)) = k7_subset_1(A_211,B_212,C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(A_211))
      | ~ m1_subset_1(B_212,k1_zfmisc_1(A_211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2704,plain,(
    ! [B_214] :
      ( k9_subset_1(k2_struct_0('#skF_4'),B_214,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) = k7_subset_1(k2_struct_0('#skF_4'),B_214,'#skF_5')
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_150,c_2682])).

tff(c_2726,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_2704])).

tff(c_2736,plain,(
    k3_xboole_0(k2_struct_0('#skF_4'),k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) = k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_176,c_2726])).

tff(c_34,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_324,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3861,plain,(
    ! [A_267,B_268,B_269] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_267,B_268),B_269),A_267)
      | r1_tarski(k4_xboole_0(A_267,B_268),B_269) ) ),
    inference(resolution,[status(thm)],[c_324,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3965,plain,(
    ! [A_267,B_268] : r1_tarski(k4_xboole_0(A_267,B_268),A_267) ),
    inference(resolution,[status(thm)],[c_3861,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_360,plain,(
    ! [C_91,B_92,A_93] :
      ( r2_hidden(C_91,B_92)
      | ~ r2_hidden(C_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3331,plain,(
    ! [A_243,B_244,B_245] :
      ( r2_hidden('#skF_1'(A_243,B_244),B_245)
      | ~ r1_tarski(A_243,B_245)
      | r1_tarski(A_243,B_244) ) ),
    inference(resolution,[status(thm)],[c_6,c_360])).

tff(c_455,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k3_subset_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_465,plain,(
    k4_xboole_0(k2_struct_0('#skF_4'),'#skF_5') = k3_subset_1(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_150,c_455])).

tff(c_573,plain,(
    ! [D_11] :
      ( r2_hidden(D_11,k2_struct_0('#skF_4'))
      | ~ r2_hidden(D_11,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_12])).

tff(c_9469,plain,(
    ! [A_466,B_467] :
      ( r2_hidden('#skF_1'(A_466,B_467),k2_struct_0('#skF_4'))
      | ~ r1_tarski(A_466,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'))
      | r1_tarski(A_466,B_467) ) ),
    inference(resolution,[status(thm)],[c_3331,c_573])).

tff(c_9552,plain,(
    ! [A_471] :
      ( ~ r1_tarski(A_471,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'))
      | r1_tarski(A_471,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_9469,c_4])).

tff(c_9970,plain,(
    ! [B_478] : r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),B_478),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3965,c_9552])).

tff(c_363,plain,(
    ! [A_1,B_2,B_92] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_92)
      | ~ r1_tarski(A_1,B_92)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_360])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4157,plain,(
    ! [A_278,B_279,B_280] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_278,B_279),B_280),B_279)
      | r1_tarski(k4_xboole_0(A_278,B_279),B_280) ) ),
    inference(resolution,[status(thm)],[c_324,c_10])).

tff(c_4205,plain,(
    ! [A_278,B_92,B_2] :
      ( ~ r1_tarski(k4_xboole_0(A_278,B_92),B_92)
      | r1_tarski(k4_xboole_0(A_278,B_92),B_2) ) ),
    inference(resolution,[status(thm)],[c_363,c_4157])).

tff(c_10006,plain,(
    ! [B_2] : r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')),B_2) ),
    inference(resolution,[status(thm)],[c_9970,c_4205])).

tff(c_10040,plain,(
    ! [B_481] : r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')),B_481) ),
    inference(resolution,[status(thm)],[c_9970,c_4205])).

tff(c_1638,plain,(
    ! [A_179,B_180,C_181] :
      ( r2_hidden('#skF_2'(A_179,B_180,C_181),A_179)
      | r2_hidden('#skF_3'(A_179,B_180,C_181),C_181)
      | k4_xboole_0(A_179,B_180) = C_181 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1779,plain,(
    ! [A_179,B_180] :
      ( r2_hidden('#skF_3'(A_179,B_180,A_179),A_179)
      | k4_xboole_0(A_179,B_180) = A_179 ) ),
    inference(resolution,[status(thm)],[c_1638,c_20])).

tff(c_1871,plain,(
    ! [A_186,B_187] :
      ( r2_hidden('#skF_3'(A_186,B_187,A_186),A_186)
      | k4_xboole_0(A_186,B_187) = A_186 ) ),
    inference(resolution,[status(thm)],[c_1638,c_20])).

tff(c_241,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,B_77)
      | ~ r2_hidden(D_76,k4_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_244,plain,(
    ! [D_76,A_16] :
      ( ~ r2_hidden(D_76,k1_xboole_0)
      | ~ r2_hidden(D_76,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_241])).

tff(c_2192,plain,(
    ! [B_198,A_199] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_198,k1_xboole_0),A_199)
      | k4_xboole_0(k1_xboole_0,B_198) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1871,c_244])).

tff(c_2244,plain,(
    ! [B_201] : k4_xboole_0(k1_xboole_0,B_201) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1779,c_2192])).

tff(c_36,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2279,plain,(
    ! [B_201] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_2244,c_36])).

tff(c_2335,plain,(
    ! [B_201] : k3_xboole_0(k1_xboole_0,B_201) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2279])).

tff(c_478,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k3_subset_1(A_112,A_112) ),
    inference(resolution,[status(thm)],[c_81,c_455])).

tff(c_246,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_267,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_246])).

tff(c_512,plain,(
    ! [A_113] : k3_xboole_0(A_113,k1_xboole_0) = k3_subset_1(A_113,A_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_267])).

tff(c_552,plain,(
    ! [A_66] : k3_xboole_0(k1_xboole_0,A_66) = k3_subset_1(A_66,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_512])).

tff(c_2351,plain,(
    ! [A_66] : k3_subset_1(A_66,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2335,c_552])).

tff(c_484,plain,(
    ! [A_112] : k3_xboole_0(A_112,k1_xboole_0) = k3_subset_1(A_112,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_267])).

tff(c_2538,plain,(
    ! [A_112] : k3_xboole_0(A_112,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2351,c_484])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2078,plain,(
    ! [A_193,B_194,C_195] :
      ( ~ r2_hidden('#skF_2'(A_193,B_194,C_195),B_194)
      | r2_hidden('#skF_3'(A_193,B_194,C_195),C_195)
      | k4_xboole_0(A_193,B_194) = C_195 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2081,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_2078])).

tff(c_2089,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k3_xboole_0(A_6,k1_xboole_0) = C_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_2081])).

tff(c_2905,plain,(
    ! [A_228,C_229] :
      ( r2_hidden('#skF_3'(A_228,A_228,C_229),C_229)
      | k1_xboole_0 = C_229 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2538,c_2089])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2965,plain,(
    ! [A_228,C_229,B_2] :
      ( r2_hidden('#skF_3'(A_228,A_228,C_229),B_2)
      | ~ r1_tarski(C_229,B_2)
      | k1_xboole_0 = C_229 ) ),
    inference(resolution,[status(thm)],[c_2905,c_2])).

tff(c_5934,plain,(
    ! [A_373,C_374,B_375] :
      ( r2_hidden('#skF_3'(A_373,A_373,C_374),B_375)
      | ~ r1_tarski(C_374,B_375)
      | k1_xboole_0 = C_374 ) ),
    inference(resolution,[status(thm)],[c_2905,c_2])).

tff(c_570,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_5')
      | ~ r2_hidden(D_11,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_10])).

tff(c_7651,plain,(
    ! [A_417,C_418] :
      ( ~ r2_hidden('#skF_3'(A_417,A_417,C_418),'#skF_5')
      | ~ r1_tarski(C_418,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'))
      | k1_xboole_0 = C_418 ) ),
    inference(resolution,[status(thm)],[c_5934,c_570])).

tff(c_7669,plain,(
    ! [C_229] :
      ( ~ r1_tarski(C_229,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'))
      | ~ r1_tarski(C_229,'#skF_5')
      | k1_xboole_0 = C_229 ) ),
    inference(resolution,[status(thm)],[c_2965,c_7651])).

tff(c_10048,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')),'#skF_5')
    | k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10040,c_7669])).

tff(c_10090,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10006,c_10048])).

tff(c_10161,plain,(
    k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10090,c_36])).

tff(c_10193,plain,(
    k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k3_subset_1(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10161])).

tff(c_4007,plain,(
    ! [A_270,B_271] : r1_tarski(k4_xboole_0(A_270,B_271),A_270) ),
    inference(resolution,[status(thm)],[c_3861,c_4])).

tff(c_4047,plain,(
    ! [A_272,B_273] : r1_tarski(k3_xboole_0(A_272,B_273),A_272) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4007])).

tff(c_4081,plain,(
    ! [B_274,A_275] : r1_tarski(k3_xboole_0(B_274,A_275),A_275) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_4047])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4903,plain,(
    ! [B_319,A_320] :
      ( k3_xboole_0(B_319,A_320) = A_320
      | ~ r1_tarski(A_320,k3_xboole_0(B_319,A_320)) ) ),
    inference(resolution,[status(thm)],[c_4081,c_26])).

tff(c_4933,plain,(
    ! [A_66,B_65] :
      ( k3_xboole_0(A_66,B_65) = B_65
      | ~ r1_tarski(B_65,k3_xboole_0(B_65,A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_4903])).

tff(c_10797,plain,
    ( k3_xboole_0(k2_struct_0('#skF_4'),k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) = k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10193,c_4933])).

tff(c_10847,plain,(
    k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5') = k3_subset_1(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2736,c_10797])).

tff(c_2516,plain,(
    ! [B_204,A_205] :
      ( v4_pre_topc(B_204,A_205)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_205),k2_struct_0(A_205),B_204),A_205)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2519,plain,(
    ! [B_204] :
      ( v4_pre_topc(B_204,'#skF_4')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),B_204),'#skF_4')
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2516])).

tff(c_2521,plain,(
    ! [B_204] :
      ( v4_pre_topc(B_204,'#skF_4')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),B_204),'#skF_4')
      | ~ m1_subset_1(B_204,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_148,c_2519])).

tff(c_11050,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10847,c_2521])).

tff(c_11056,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_149,c_11050])).

tff(c_11058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_11056])).

tff(c_11059,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_11095,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11059,c_74])).

tff(c_11101,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11100,c_11095])).

tff(c_11102,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11100,c_70])).

tff(c_11204,plain,(
    ! [A_525,B_526] :
      ( r2_hidden('#skF_1'(A_525,B_526),A_525)
      | r1_tarski(A_525,B_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14963,plain,(
    ! [A_736,B_737,B_738] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_736,B_737),B_738),A_736)
      | r1_tarski(k4_xboole_0(A_736,B_737),B_738) ) ),
    inference(resolution,[status(thm)],[c_11204,c_12])).

tff(c_15075,plain,(
    ! [A_736,B_737] : r1_tarski(k4_xboole_0(A_736,B_737),A_736) ),
    inference(resolution,[status(thm)],[c_14963,c_4])).

tff(c_11366,plain,(
    ! [A_545,B_546] :
      ( k4_xboole_0(A_545,B_546) = k3_subset_1(A_545,B_546)
      | ~ m1_subset_1(B_546,k1_zfmisc_1(A_545)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_11380,plain,(
    k4_xboole_0(k2_struct_0('#skF_4'),'#skF_5') = k3_subset_1(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_11102,c_11366])).

tff(c_11282,plain,(
    ! [C_532,B_533,A_534] :
      ( r2_hidden(C_532,B_533)
      | ~ r2_hidden(C_532,A_534)
      | ~ r1_tarski(A_534,B_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14205,plain,(
    ! [A_690,B_691,B_692] :
      ( r2_hidden('#skF_1'(A_690,B_691),B_692)
      | ~ r1_tarski(A_690,B_692)
      | r1_tarski(A_690,B_691) ) ),
    inference(resolution,[status(thm)],[c_6,c_11282])).

tff(c_35059,plain,(
    ! [A_1100,B_1101,A_1102,B_1103] :
      ( r2_hidden('#skF_1'(A_1100,B_1101),A_1102)
      | ~ r1_tarski(A_1100,k4_xboole_0(A_1102,B_1103))
      | r1_tarski(A_1100,B_1101) ) ),
    inference(resolution,[status(thm)],[c_14205,c_12])).

tff(c_35520,plain,(
    ! [A_1109,B_1110] :
      ( r2_hidden('#skF_1'(A_1109,B_1110),k2_struct_0('#skF_4'))
      | ~ r1_tarski(A_1109,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'))
      | r1_tarski(A_1109,B_1110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11380,c_35059])).

tff(c_35554,plain,(
    ! [A_1111] :
      ( ~ r1_tarski(A_1111,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'))
      | r1_tarski(A_1111,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_35520,c_4])).

tff(c_35739,plain,(
    ! [B_1114] : r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),B_1114),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_15075,c_35554])).

tff(c_11285,plain,(
    ! [A_1,B_2,B_533] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_533)
      | ~ r1_tarski(A_1,B_533)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_11282])).

tff(c_14472,plain,(
    ! [A_704,B_705,B_706] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_704,B_705),B_706),B_705)
      | r1_tarski(k4_xboole_0(A_704,B_705),B_706) ) ),
    inference(resolution,[status(thm)],[c_11204,c_10])).

tff(c_14509,plain,(
    ! [A_704,B_533,B_2] :
      ( ~ r1_tarski(k4_xboole_0(A_704,B_533),B_533)
      | r1_tarski(k4_xboole_0(A_704,B_533),B_2) ) ),
    inference(resolution,[status(thm)],[c_11285,c_14472])).

tff(c_35787,plain,(
    ! [B_2] : r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')),B_2) ),
    inference(resolution,[status(thm)],[c_35739,c_14509])).

tff(c_35928,plain,(
    ! [B_1119] : r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')),B_1119) ),
    inference(resolution,[status(thm)],[c_35739,c_14509])).

tff(c_11232,plain,(
    ! [A_529,B_530] : k4_xboole_0(A_529,k4_xboole_0(A_529,B_530)) = k3_xboole_0(A_529,B_530) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_11253,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_11232])).

tff(c_12637,plain,(
    ! [A_618,B_619,C_620] :
      ( ~ r2_hidden('#skF_2'(A_618,B_619,C_620),B_619)
      | r2_hidden('#skF_3'(A_618,B_619,C_620),C_620)
      | k4_xboole_0(A_618,B_619) = C_620 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12640,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_12637])).

tff(c_12645,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k3_xboole_0(A_6,k1_xboole_0) = C_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11253,c_12640])).

tff(c_12817,plain,(
    ! [A_631,C_632] :
      ( r2_hidden('#skF_3'(A_631,A_631,C_632),C_632)
      | k3_xboole_0(A_631,k1_xboole_0) = C_632 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11253,c_12640])).

tff(c_11198,plain,(
    ! [D_518,B_519,A_520] :
      ( ~ r2_hidden(D_518,B_519)
      | ~ r2_hidden(D_518,k4_xboole_0(A_520,B_519)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11201,plain,(
    ! [D_518,A_16] :
      ( ~ r2_hidden(D_518,k1_xboole_0)
      | ~ r2_hidden(D_518,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_11198])).

tff(c_13219,plain,(
    ! [A_651,A_652] :
      ( ~ r2_hidden('#skF_3'(A_651,A_651,k1_xboole_0),A_652)
      | k3_xboole_0(A_651,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12817,c_11201])).

tff(c_13240,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12645,c_13219])).

tff(c_14015,plain,(
    ! [A_682,C_683] :
      ( r2_hidden('#skF_3'(A_682,A_682,C_683),C_683)
      | k1_xboole_0 = C_683 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13240,c_12645])).

tff(c_14071,plain,(
    ! [A_682,C_683,B_2] :
      ( r2_hidden('#skF_3'(A_682,A_682,C_683),B_2)
      | ~ r1_tarski(C_683,B_2)
      | k1_xboole_0 = C_683 ) ),
    inference(resolution,[status(thm)],[c_14015,c_2])).

tff(c_16922,plain,(
    ! [A_827,C_828,B_829] :
      ( r2_hidden('#skF_3'(A_827,A_827,C_828),B_829)
      | ~ r1_tarski(C_828,B_829)
      | k1_xboole_0 = C_828 ) ),
    inference(resolution,[status(thm)],[c_14015,c_2])).

tff(c_11758,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_5')
      | ~ r2_hidden(D_11,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11380,c_10])).

tff(c_20154,plain,(
    ! [A_904,C_905] :
      ( ~ r2_hidden('#skF_3'(A_904,A_904,C_905),'#skF_5')
      | ~ r1_tarski(C_905,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'))
      | k1_xboole_0 = C_905 ) ),
    inference(resolution,[status(thm)],[c_16922,c_11758])).

tff(c_20175,plain,(
    ! [C_683] :
      ( ~ r1_tarski(C_683,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'))
      | ~ r1_tarski(C_683,'#skF_5')
      | k1_xboole_0 = C_683 ) ),
    inference(resolution,[status(thm)],[c_14071,c_20154])).

tff(c_35951,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')),'#skF_5')
    | k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35928,c_20175])).

tff(c_36003,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35787,c_35951])).

tff(c_11107,plain,(
    ! [A_507,B_508] : k1_setfam_1(k2_tarski(A_507,B_508)) = k3_xboole_0(A_507,B_508) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_11122,plain,(
    ! [B_509,A_510] : k1_setfam_1(k2_tarski(B_509,A_510)) = k3_xboole_0(A_510,B_509) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_11107])).

tff(c_11128,plain,(
    ! [B_509,A_510] : k3_xboole_0(B_509,A_510) = k3_xboole_0(A_510,B_509) ),
    inference(superposition,[status(thm),theory(equality)],[c_11122,c_58])).

tff(c_12025,plain,(
    ! [A_585,B_586,C_587] :
      ( k9_subset_1(A_585,B_586,C_587) = k3_xboole_0(B_586,C_587)
      | ~ m1_subset_1(C_587,k1_zfmisc_1(A_585)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12049,plain,(
    ! [A_27,B_586] : k9_subset_1(A_27,B_586,A_27) = k3_xboole_0(B_586,A_27) ),
    inference(resolution,[status(thm)],[c_81,c_12025])).

tff(c_12164,plain,(
    ! [A_597,C_598,B_599] :
      ( k9_subset_1(A_597,C_598,B_599) = k9_subset_1(A_597,B_599,C_598)
      | ~ m1_subset_1(C_598,k1_zfmisc_1(A_597)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12179,plain,(
    ! [A_27,B_599] : k9_subset_1(A_27,B_599,A_27) = k9_subset_1(A_27,A_27,B_599) ),
    inference(resolution,[status(thm)],[c_81,c_12164])).

tff(c_12190,plain,(
    ! [A_27,B_599] : k9_subset_1(A_27,A_27,B_599) = k3_xboole_0(B_599,A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12049,c_12179])).

tff(c_13634,plain,(
    ! [A_663,B_664,C_665] :
      ( k9_subset_1(A_663,B_664,k3_subset_1(A_663,C_665)) = k7_subset_1(A_663,B_664,C_665)
      | ~ m1_subset_1(C_665,k1_zfmisc_1(A_663))
      | ~ m1_subset_1(B_664,k1_zfmisc_1(A_663)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_13660,plain,(
    ! [B_666] :
      ( k9_subset_1(k2_struct_0('#skF_4'),B_666,k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) = k7_subset_1(k2_struct_0('#skF_4'),B_666,'#skF_5')
      | ~ m1_subset_1(B_666,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_11102,c_13634])).

tff(c_13682,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12190,c_13660])).

tff(c_13692,plain,(
    k3_xboole_0(k2_struct_0('#skF_4'),k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) = k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_11128,c_13682])).

tff(c_36185,plain,(
    k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36003,c_36])).

tff(c_36250,plain,(
    k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4')) = k3_subset_1(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36185])).

tff(c_11416,plain,(
    ! [A_550] : k4_xboole_0(A_550,A_550) = k3_subset_1(A_550,A_550) ),
    inference(resolution,[status(thm)],[c_81,c_11366])).

tff(c_11422,plain,(
    ! [A_550] : k3_xboole_0(A_550,k1_xboole_0) = k3_subset_1(A_550,A_550) ),
    inference(superposition,[status(thm),theory(equality)],[c_11416,c_11253])).

tff(c_13253,plain,(
    ! [A_550] : k3_subset_1(A_550,A_550) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13240,c_11422])).

tff(c_11450,plain,(
    ! [A_551] : k3_xboole_0(A_551,k1_xboole_0) = k3_subset_1(A_551,A_551) ),
    inference(superposition,[status(thm),theory(equality)],[c_11416,c_11253])).

tff(c_32,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11474,plain,(
    ! [A_551] : k5_xboole_0(A_551,k3_subset_1(A_551,A_551)) = k4_xboole_0(A_551,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11450,c_32])).

tff(c_11503,plain,(
    ! [A_551] : k5_xboole_0(A_551,k3_subset_1(A_551,A_551)) = A_551 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_11474])).

tff(c_13355,plain,(
    ! [A_551] : k5_xboole_0(A_551,k1_xboole_0) = A_551 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13253,c_11503])).

tff(c_13257,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13240,c_11253])).

tff(c_11820,plain,(
    ! [D_570,A_571,B_572] :
      ( r2_hidden(D_570,k4_xboole_0(A_571,B_572))
      | r2_hidden(D_570,B_572)
      | ~ r2_hidden(D_570,A_571) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16999,plain,(
    ! [A_830,A_831,B_832] :
      ( r1_tarski(A_830,k4_xboole_0(A_831,B_832))
      | r2_hidden('#skF_1'(A_830,k4_xboole_0(A_831,B_832)),B_832)
      | ~ r2_hidden('#skF_1'(A_830,k4_xboole_0(A_831,B_832)),A_831) ) ),
    inference(resolution,[status(thm)],[c_11820,c_4])).

tff(c_22982,plain,(
    ! [A_969,B_970] :
      ( r2_hidden('#skF_1'(A_969,k4_xboole_0(A_969,B_970)),B_970)
      | r1_tarski(A_969,k4_xboole_0(A_969,B_970)) ) ),
    inference(resolution,[status(thm)],[c_6,c_16999])).

tff(c_11223,plain,(
    ! [A_6,B_7,B_526] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_526),B_7)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_526) ) ),
    inference(resolution,[status(thm)],[c_11204,c_10])).

tff(c_23161,plain,(
    ! [A_971,B_972] : r1_tarski(k4_xboole_0(A_971,B_972),k4_xboole_0(k4_xboole_0(A_971,B_972),B_972)) ),
    inference(resolution,[status(thm)],[c_22982,c_11223])).

tff(c_15088,plain,(
    ! [A_739,B_740] : r1_tarski(k4_xboole_0(A_739,B_740),A_739) ),
    inference(resolution,[status(thm)],[c_14963,c_4])).

tff(c_15131,plain,(
    ! [A_739,B_740] :
      ( k4_xboole_0(A_739,B_740) = A_739
      | ~ r1_tarski(A_739,k4_xboole_0(A_739,B_740)) ) ),
    inference(resolution,[status(thm)],[c_15088,c_26])).

tff(c_23300,plain,(
    ! [A_973,B_974] : k4_xboole_0(k4_xboole_0(A_973,B_974),B_974) = k4_xboole_0(A_973,B_974) ),
    inference(resolution,[status(thm)],[c_23161,c_15131])).

tff(c_23383,plain,(
    ! [A_973,B_974] : k4_xboole_0(k4_xboole_0(A_973,B_974),k4_xboole_0(A_973,B_974)) = k3_xboole_0(k4_xboole_0(A_973,B_974),B_974) ),
    inference(superposition,[status(thm),theory(equality)],[c_23300,c_36])).

tff(c_23697,plain,(
    ! [B_979,A_980] : k3_xboole_0(B_979,k4_xboole_0(A_980,B_979)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13257,c_11128,c_23383])).

tff(c_24327,plain,(
    ! [A_985,B_986] : k3_xboole_0(k4_xboole_0(A_985,B_986),k3_xboole_0(A_985,B_986)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_23697])).

tff(c_25036,plain,(
    ! [B_996,A_997] : k3_xboole_0(k4_xboole_0(B_996,A_997),k3_xboole_0(A_997,B_996)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11128,c_24327])).

tff(c_11183,plain,(
    ! [A_516,B_517] : k5_xboole_0(A_516,k3_xboole_0(A_516,B_517)) = k4_xboole_0(A_516,B_517) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11192,plain,(
    ! [A_510,B_509] : k5_xboole_0(A_510,k3_xboole_0(B_509,A_510)) = k4_xboole_0(A_510,B_509) ),
    inference(superposition,[status(thm),theory(equality)],[c_11128,c_11183])).

tff(c_25092,plain,(
    ! [A_997,B_996] : k4_xboole_0(k3_xboole_0(A_997,B_996),k4_xboole_0(B_996,A_997)) = k5_xboole_0(k3_xboole_0(A_997,B_996),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_25036,c_11192])).

tff(c_30075,plain,(
    ! [A_1050,B_1051] : k4_xboole_0(k3_xboole_0(A_1050,B_1051),k4_xboole_0(B_1051,A_1050)) = k3_xboole_0(A_1050,B_1051) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13355,c_25092])).

tff(c_30385,plain,(
    ! [A_510,B_509] : k4_xboole_0(k3_xboole_0(A_510,B_509),k4_xboole_0(A_510,B_509)) = k3_xboole_0(B_509,A_510) ),
    inference(superposition,[status(thm),theory(equality)],[c_11128,c_30075])).

tff(c_36298,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),k2_struct_0('#skF_4'))) = k3_xboole_0(k2_struct_0('#skF_4'),k3_subset_1(k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36250,c_30385])).

tff(c_36428,plain,(
    k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5') = k3_subset_1(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36003,c_13692,c_36298])).

tff(c_13475,plain,(
    ! [A_657,B_658] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_657),k2_struct_0(A_657),B_658),A_657)
      | ~ v4_pre_topc(B_658,A_657)
      | ~ m1_subset_1(B_658,k1_zfmisc_1(u1_struct_0(A_657)))
      | ~ l1_pre_topc(A_657) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_13481,plain,(
    ! [B_658] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),B_658),'#skF_4')
      | ~ v4_pre_topc(B_658,'#skF_4')
      | ~ m1_subset_1(B_658,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11100,c_13475])).

tff(c_13484,plain,(
    ! [B_658] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),B_658),'#skF_4')
      | ~ v4_pre_topc(B_658,'#skF_4')
      | ~ m1_subset_1(B_658,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11100,c_13481])).

tff(c_36472,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36428,c_13484])).

tff(c_36479,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11102,c_11059,c_36472])).

tff(c_36481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11101,c_36479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.96/5.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.96/5.86  
% 12.96/5.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.96/5.87  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 12.96/5.87  
% 12.96/5.87  %Foreground sorts:
% 12.96/5.87  
% 12.96/5.87  
% 12.96/5.87  %Background operators:
% 12.96/5.87  
% 12.96/5.87  
% 12.96/5.87  %Foreground operators:
% 12.96/5.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.96/5.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.96/5.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.96/5.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.96/5.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.96/5.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.96/5.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.96/5.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.96/5.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.96/5.87  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.96/5.87  tff('#skF_5', type, '#skF_5': $i).
% 12.96/5.87  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 12.96/5.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.96/5.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.96/5.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.96/5.87  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 12.96/5.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.96/5.87  tff('#skF_4', type, '#skF_4': $i).
% 12.96/5.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.96/5.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.96/5.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.96/5.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.96/5.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.96/5.87  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.96/5.87  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.96/5.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.96/5.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.96/5.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.96/5.87  
% 13.25/5.90  tff(f_127, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 13.25/5.90  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 13.25/5.90  tff(f_104, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 13.25/5.90  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.25/5.90  tff(f_62, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 13.25/5.90  tff(f_68, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 13.25/5.90  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.25/5.90  tff(f_94, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 13.25/5.90  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 13.25/5.90  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 13.25/5.90  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 13.25/5.90  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.25/5.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.25/5.90  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.25/5.90  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 13.25/5.90  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.25/5.90  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 13.25/5.90  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.25/5.90  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.25/5.90  tff(c_68, plain, (![A_51]: (l1_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_117])).
% 13.25/5.90  tff(c_105, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.25/5.90  tff(c_11096, plain, (![A_506]: (u1_struct_0(A_506)=k2_struct_0(A_506) | ~l1_pre_topc(A_506))), inference(resolution, [status(thm)], [c_68, c_105])).
% 13.25/5.90  tff(c_11100, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_11096])).
% 13.25/5.90  tff(c_144, plain, (![A_62]: (u1_struct_0(A_62)=k2_struct_0(A_62) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_68, c_105])).
% 13.25/5.90  tff(c_148, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_144])).
% 13.25/5.90  tff(c_80, plain, (v4_pre_topc('#skF_5', '#skF_4') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.25/5.90  tff(c_110, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_80])).
% 13.25/5.90  tff(c_149, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_110])).
% 13.25/5.90  tff(c_74, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v4_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.25/5.90  tff(c_227, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_148, c_74])).
% 13.25/5.90  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.25/5.90  tff(c_150, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_70])).
% 13.25/5.90  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.25/5.90  tff(c_42, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.25/5.90  tff(c_46, plain, (![A_27]: (m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.25/5.90  tff(c_81, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 13.25/5.90  tff(c_38, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.25/5.90  tff(c_155, plain, (![A_63, B_64]: (k1_setfam_1(k2_tarski(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.25/5.90  tff(c_170, plain, (![B_65, A_66]: (k1_setfam_1(k2_tarski(B_65, A_66))=k3_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_38, c_155])).
% 13.25/5.90  tff(c_58, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.25/5.90  tff(c_176, plain, (![B_65, A_66]: (k3_xboole_0(B_65, A_66)=k3_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_170, c_58])).
% 13.25/5.90  tff(c_1179, plain, (![A_147, B_148, C_149]: (k9_subset_1(A_147, B_148, C_149)=k3_xboole_0(B_148, C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.25/5.90  tff(c_1203, plain, (![A_27, B_148]: (k9_subset_1(A_27, B_148, A_27)=k3_xboole_0(B_148, A_27))), inference(resolution, [status(thm)], [c_81, c_1179])).
% 13.25/5.90  tff(c_1258, plain, (![A_157, C_158, B_159]: (k9_subset_1(A_157, C_158, B_159)=k9_subset_1(A_157, B_159, C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.25/5.90  tff(c_1273, plain, (![A_27, B_159]: (k9_subset_1(A_27, B_159, A_27)=k9_subset_1(A_27, A_27, B_159))), inference(resolution, [status(thm)], [c_81, c_1258])).
% 13.25/5.90  tff(c_1284, plain, (![A_27, B_159]: (k9_subset_1(A_27, A_27, B_159)=k3_xboole_0(B_159, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_1203, c_1273])).
% 13.25/5.90  tff(c_2682, plain, (![A_211, B_212, C_213]: (k9_subset_1(A_211, B_212, k3_subset_1(A_211, C_213))=k7_subset_1(A_211, B_212, C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(A_211)) | ~m1_subset_1(B_212, k1_zfmisc_1(A_211)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.25/5.90  tff(c_2704, plain, (![B_214]: (k9_subset_1(k2_struct_0('#skF_4'), B_214, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'))=k7_subset_1(k2_struct_0('#skF_4'), B_214, '#skF_5') | ~m1_subset_1(B_214, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_150, c_2682])).
% 13.25/5.90  tff(c_2726, plain, (k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1284, c_2704])).
% 13.25/5.90  tff(c_2736, plain, (k3_xboole_0(k2_struct_0('#skF_4'), k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'))=k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_176, c_2726])).
% 13.25/5.90  tff(c_34, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.25/5.90  tff(c_324, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), A_86) | r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.25/5.90  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_3861, plain, (![A_267, B_268, B_269]: (r2_hidden('#skF_1'(k4_xboole_0(A_267, B_268), B_269), A_267) | r1_tarski(k4_xboole_0(A_267, B_268), B_269))), inference(resolution, [status(thm)], [c_324, c_12])).
% 13.25/5.90  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.25/5.90  tff(c_3965, plain, (![A_267, B_268]: (r1_tarski(k4_xboole_0(A_267, B_268), A_267))), inference(resolution, [status(thm)], [c_3861, c_4])).
% 13.25/5.90  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.25/5.90  tff(c_360, plain, (![C_91, B_92, A_93]: (r2_hidden(C_91, B_92) | ~r2_hidden(C_91, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.25/5.90  tff(c_3331, plain, (![A_243, B_244, B_245]: (r2_hidden('#skF_1'(A_243, B_244), B_245) | ~r1_tarski(A_243, B_245) | r1_tarski(A_243, B_244))), inference(resolution, [status(thm)], [c_6, c_360])).
% 13.25/5.90  tff(c_455, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k3_subset_1(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.25/5.90  tff(c_465, plain, (k4_xboole_0(k2_struct_0('#skF_4'), '#skF_5')=k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_150, c_455])).
% 13.25/5.90  tff(c_573, plain, (![D_11]: (r2_hidden(D_11, k2_struct_0('#skF_4')) | ~r2_hidden(D_11, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_465, c_12])).
% 13.25/5.90  tff(c_9469, plain, (![A_466, B_467]: (r2_hidden('#skF_1'(A_466, B_467), k2_struct_0('#skF_4')) | ~r1_tarski(A_466, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')) | r1_tarski(A_466, B_467))), inference(resolution, [status(thm)], [c_3331, c_573])).
% 13.25/5.90  tff(c_9552, plain, (![A_471]: (~r1_tarski(A_471, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')) | r1_tarski(A_471, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_9469, c_4])).
% 13.25/5.90  tff(c_9970, plain, (![B_478]: (r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), B_478), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3965, c_9552])).
% 13.25/5.90  tff(c_363, plain, (![A_1, B_2, B_92]: (r2_hidden('#skF_1'(A_1, B_2), B_92) | ~r1_tarski(A_1, B_92) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_360])).
% 13.25/5.90  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_4157, plain, (![A_278, B_279, B_280]: (~r2_hidden('#skF_1'(k4_xboole_0(A_278, B_279), B_280), B_279) | r1_tarski(k4_xboole_0(A_278, B_279), B_280))), inference(resolution, [status(thm)], [c_324, c_10])).
% 13.25/5.90  tff(c_4205, plain, (![A_278, B_92, B_2]: (~r1_tarski(k4_xboole_0(A_278, B_92), B_92) | r1_tarski(k4_xboole_0(A_278, B_92), B_2))), inference(resolution, [status(thm)], [c_363, c_4157])).
% 13.25/5.90  tff(c_10006, plain, (![B_2]: (r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4')), B_2))), inference(resolution, [status(thm)], [c_9970, c_4205])).
% 13.25/5.90  tff(c_10040, plain, (![B_481]: (r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4')), B_481))), inference(resolution, [status(thm)], [c_9970, c_4205])).
% 13.25/5.90  tff(c_1638, plain, (![A_179, B_180, C_181]: (r2_hidden('#skF_2'(A_179, B_180, C_181), A_179) | r2_hidden('#skF_3'(A_179, B_180, C_181), C_181) | k4_xboole_0(A_179, B_180)=C_181)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_1779, plain, (![A_179, B_180]: (r2_hidden('#skF_3'(A_179, B_180, A_179), A_179) | k4_xboole_0(A_179, B_180)=A_179)), inference(resolution, [status(thm)], [c_1638, c_20])).
% 13.25/5.90  tff(c_1871, plain, (![A_186, B_187]: (r2_hidden('#skF_3'(A_186, B_187, A_186), A_186) | k4_xboole_0(A_186, B_187)=A_186)), inference(resolution, [status(thm)], [c_1638, c_20])).
% 13.25/5.90  tff(c_241, plain, (![D_76, B_77, A_78]: (~r2_hidden(D_76, B_77) | ~r2_hidden(D_76, k4_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_244, plain, (![D_76, A_16]: (~r2_hidden(D_76, k1_xboole_0) | ~r2_hidden(D_76, A_16))), inference(superposition, [status(thm), theory('equality')], [c_34, c_241])).
% 13.25/5.90  tff(c_2192, plain, (![B_198, A_199]: (~r2_hidden('#skF_3'(k1_xboole_0, B_198, k1_xboole_0), A_199) | k4_xboole_0(k1_xboole_0, B_198)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1871, c_244])).
% 13.25/5.90  tff(c_2244, plain, (![B_201]: (k4_xboole_0(k1_xboole_0, B_201)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1779, c_2192])).
% 13.25/5.90  tff(c_36, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.25/5.90  tff(c_2279, plain, (![B_201]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_201))), inference(superposition, [status(thm), theory('equality')], [c_2244, c_36])).
% 13.25/5.90  tff(c_2335, plain, (![B_201]: (k3_xboole_0(k1_xboole_0, B_201)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2279])).
% 13.25/5.90  tff(c_478, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k3_subset_1(A_112, A_112))), inference(resolution, [status(thm)], [c_81, c_455])).
% 13.25/5.90  tff(c_246, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.25/5.90  tff(c_267, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_246])).
% 13.25/5.90  tff(c_512, plain, (![A_113]: (k3_xboole_0(A_113, k1_xboole_0)=k3_subset_1(A_113, A_113))), inference(superposition, [status(thm), theory('equality')], [c_478, c_267])).
% 13.25/5.90  tff(c_552, plain, (![A_66]: (k3_xboole_0(k1_xboole_0, A_66)=k3_subset_1(A_66, A_66))), inference(superposition, [status(thm), theory('equality')], [c_176, c_512])).
% 13.25/5.90  tff(c_2351, plain, (![A_66]: (k3_subset_1(A_66, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2335, c_552])).
% 13.25/5.90  tff(c_484, plain, (![A_112]: (k3_xboole_0(A_112, k1_xboole_0)=k3_subset_1(A_112, A_112))), inference(superposition, [status(thm), theory('equality')], [c_478, c_267])).
% 13.25/5.90  tff(c_2538, plain, (![A_112]: (k3_xboole_0(A_112, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2351, c_484])).
% 13.25/5.90  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_2078, plain, (![A_193, B_194, C_195]: (~r2_hidden('#skF_2'(A_193, B_194, C_195), B_194) | r2_hidden('#skF_3'(A_193, B_194, C_195), C_195) | k4_xboole_0(A_193, B_194)=C_195)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_2081, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_2078])).
% 13.25/5.90  tff(c_2089, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k3_xboole_0(A_6, k1_xboole_0)=C_8)), inference(demodulation, [status(thm), theory('equality')], [c_267, c_2081])).
% 13.25/5.90  tff(c_2905, plain, (![A_228, C_229]: (r2_hidden('#skF_3'(A_228, A_228, C_229), C_229) | k1_xboole_0=C_229)), inference(demodulation, [status(thm), theory('equality')], [c_2538, c_2089])).
% 13.25/5.90  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.25/5.90  tff(c_2965, plain, (![A_228, C_229, B_2]: (r2_hidden('#skF_3'(A_228, A_228, C_229), B_2) | ~r1_tarski(C_229, B_2) | k1_xboole_0=C_229)), inference(resolution, [status(thm)], [c_2905, c_2])).
% 13.25/5.90  tff(c_5934, plain, (![A_373, C_374, B_375]: (r2_hidden('#skF_3'(A_373, A_373, C_374), B_375) | ~r1_tarski(C_374, B_375) | k1_xboole_0=C_374)), inference(resolution, [status(thm)], [c_2905, c_2])).
% 13.25/5.90  tff(c_570, plain, (![D_11]: (~r2_hidden(D_11, '#skF_5') | ~r2_hidden(D_11, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_465, c_10])).
% 13.25/5.90  tff(c_7651, plain, (![A_417, C_418]: (~r2_hidden('#skF_3'(A_417, A_417, C_418), '#skF_5') | ~r1_tarski(C_418, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')) | k1_xboole_0=C_418)), inference(resolution, [status(thm)], [c_5934, c_570])).
% 13.25/5.90  tff(c_7669, plain, (![C_229]: (~r1_tarski(C_229, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')) | ~r1_tarski(C_229, '#skF_5') | k1_xboole_0=C_229)), inference(resolution, [status(thm)], [c_2965, c_7651])).
% 13.25/5.90  tff(c_10048, plain, (~r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4')), '#skF_5') | k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10040, c_7669])).
% 13.25/5.90  tff(c_10090, plain, (k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10006, c_10048])).
% 13.25/5.90  tff(c_10161, plain, (k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10090, c_36])).
% 13.25/5.90  tff(c_10193, plain, (k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10161])).
% 13.25/5.90  tff(c_4007, plain, (![A_270, B_271]: (r1_tarski(k4_xboole_0(A_270, B_271), A_270))), inference(resolution, [status(thm)], [c_3861, c_4])).
% 13.25/5.90  tff(c_4047, plain, (![A_272, B_273]: (r1_tarski(k3_xboole_0(A_272, B_273), A_272))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4007])).
% 13.25/5.90  tff(c_4081, plain, (![B_274, A_275]: (r1_tarski(k3_xboole_0(B_274, A_275), A_275))), inference(superposition, [status(thm), theory('equality')], [c_176, c_4047])).
% 13.25/5.90  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.25/5.90  tff(c_4903, plain, (![B_319, A_320]: (k3_xboole_0(B_319, A_320)=A_320 | ~r1_tarski(A_320, k3_xboole_0(B_319, A_320)))), inference(resolution, [status(thm)], [c_4081, c_26])).
% 13.25/5.90  tff(c_4933, plain, (![A_66, B_65]: (k3_xboole_0(A_66, B_65)=B_65 | ~r1_tarski(B_65, k3_xboole_0(B_65, A_66)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_4903])).
% 13.25/5.90  tff(c_10797, plain, (k3_xboole_0(k2_struct_0('#skF_4'), k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'))=k3_subset_1(k2_struct_0('#skF_4'), '#skF_5') | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10193, c_4933])).
% 13.25/5.90  tff(c_10847, plain, (k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5')=k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2736, c_10797])).
% 13.25/5.90  tff(c_2516, plain, (![B_204, A_205]: (v4_pre_topc(B_204, A_205) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_205), k2_struct_0(A_205), B_204), A_205) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.25/5.90  tff(c_2519, plain, (![B_204]: (v4_pre_topc(B_204, '#skF_4') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), B_204), '#skF_4') | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_2516])).
% 13.25/5.90  tff(c_2521, plain, (![B_204]: (v4_pre_topc(B_204, '#skF_4') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), B_204), '#skF_4') | ~m1_subset_1(B_204, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_148, c_2519])).
% 13.25/5.90  tff(c_11050, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10847, c_2521])).
% 13.25/5.90  tff(c_11056, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_149, c_11050])).
% 13.25/5.90  tff(c_11058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_11056])).
% 13.25/5.90  tff(c_11059, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_80])).
% 13.25/5.90  tff(c_11095, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11059, c_74])).
% 13.25/5.90  tff(c_11101, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11100, c_11095])).
% 13.25/5.90  tff(c_11102, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11100, c_70])).
% 13.25/5.90  tff(c_11204, plain, (![A_525, B_526]: (r2_hidden('#skF_1'(A_525, B_526), A_525) | r1_tarski(A_525, B_526))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.25/5.90  tff(c_14963, plain, (![A_736, B_737, B_738]: (r2_hidden('#skF_1'(k4_xboole_0(A_736, B_737), B_738), A_736) | r1_tarski(k4_xboole_0(A_736, B_737), B_738))), inference(resolution, [status(thm)], [c_11204, c_12])).
% 13.25/5.90  tff(c_15075, plain, (![A_736, B_737]: (r1_tarski(k4_xboole_0(A_736, B_737), A_736))), inference(resolution, [status(thm)], [c_14963, c_4])).
% 13.25/5.90  tff(c_11366, plain, (![A_545, B_546]: (k4_xboole_0(A_545, B_546)=k3_subset_1(A_545, B_546) | ~m1_subset_1(B_546, k1_zfmisc_1(A_545)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.25/5.90  tff(c_11380, plain, (k4_xboole_0(k2_struct_0('#skF_4'), '#skF_5')=k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_11102, c_11366])).
% 13.25/5.90  tff(c_11282, plain, (![C_532, B_533, A_534]: (r2_hidden(C_532, B_533) | ~r2_hidden(C_532, A_534) | ~r1_tarski(A_534, B_533))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.25/5.90  tff(c_14205, plain, (![A_690, B_691, B_692]: (r2_hidden('#skF_1'(A_690, B_691), B_692) | ~r1_tarski(A_690, B_692) | r1_tarski(A_690, B_691))), inference(resolution, [status(thm)], [c_6, c_11282])).
% 13.25/5.90  tff(c_35059, plain, (![A_1100, B_1101, A_1102, B_1103]: (r2_hidden('#skF_1'(A_1100, B_1101), A_1102) | ~r1_tarski(A_1100, k4_xboole_0(A_1102, B_1103)) | r1_tarski(A_1100, B_1101))), inference(resolution, [status(thm)], [c_14205, c_12])).
% 13.25/5.90  tff(c_35520, plain, (![A_1109, B_1110]: (r2_hidden('#skF_1'(A_1109, B_1110), k2_struct_0('#skF_4')) | ~r1_tarski(A_1109, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')) | r1_tarski(A_1109, B_1110))), inference(superposition, [status(thm), theory('equality')], [c_11380, c_35059])).
% 13.25/5.90  tff(c_35554, plain, (![A_1111]: (~r1_tarski(A_1111, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')) | r1_tarski(A_1111, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_35520, c_4])).
% 13.25/5.90  tff(c_35739, plain, (![B_1114]: (r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), B_1114), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_15075, c_35554])).
% 13.25/5.90  tff(c_11285, plain, (![A_1, B_2, B_533]: (r2_hidden('#skF_1'(A_1, B_2), B_533) | ~r1_tarski(A_1, B_533) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_11282])).
% 13.25/5.90  tff(c_14472, plain, (![A_704, B_705, B_706]: (~r2_hidden('#skF_1'(k4_xboole_0(A_704, B_705), B_706), B_705) | r1_tarski(k4_xboole_0(A_704, B_705), B_706))), inference(resolution, [status(thm)], [c_11204, c_10])).
% 13.25/5.90  tff(c_14509, plain, (![A_704, B_533, B_2]: (~r1_tarski(k4_xboole_0(A_704, B_533), B_533) | r1_tarski(k4_xboole_0(A_704, B_533), B_2))), inference(resolution, [status(thm)], [c_11285, c_14472])).
% 13.25/5.90  tff(c_35787, plain, (![B_2]: (r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4')), B_2))), inference(resolution, [status(thm)], [c_35739, c_14509])).
% 13.25/5.90  tff(c_35928, plain, (![B_1119]: (r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4')), B_1119))), inference(resolution, [status(thm)], [c_35739, c_14509])).
% 13.25/5.90  tff(c_11232, plain, (![A_529, B_530]: (k4_xboole_0(A_529, k4_xboole_0(A_529, B_530))=k3_xboole_0(A_529, B_530))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.25/5.90  tff(c_11253, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_11232])).
% 13.25/5.90  tff(c_12637, plain, (![A_618, B_619, C_620]: (~r2_hidden('#skF_2'(A_618, B_619, C_620), B_619) | r2_hidden('#skF_3'(A_618, B_619, C_620), C_620) | k4_xboole_0(A_618, B_619)=C_620)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_12640, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_12637])).
% 13.25/5.90  tff(c_12645, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k3_xboole_0(A_6, k1_xboole_0)=C_8)), inference(demodulation, [status(thm), theory('equality')], [c_11253, c_12640])).
% 13.25/5.90  tff(c_12817, plain, (![A_631, C_632]: (r2_hidden('#skF_3'(A_631, A_631, C_632), C_632) | k3_xboole_0(A_631, k1_xboole_0)=C_632)), inference(demodulation, [status(thm), theory('equality')], [c_11253, c_12640])).
% 13.25/5.90  tff(c_11198, plain, (![D_518, B_519, A_520]: (~r2_hidden(D_518, B_519) | ~r2_hidden(D_518, k4_xboole_0(A_520, B_519)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_11201, plain, (![D_518, A_16]: (~r2_hidden(D_518, k1_xboole_0) | ~r2_hidden(D_518, A_16))), inference(superposition, [status(thm), theory('equality')], [c_34, c_11198])).
% 13.25/5.90  tff(c_13219, plain, (![A_651, A_652]: (~r2_hidden('#skF_3'(A_651, A_651, k1_xboole_0), A_652) | k3_xboole_0(A_651, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12817, c_11201])).
% 13.25/5.90  tff(c_13240, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12645, c_13219])).
% 13.25/5.90  tff(c_14015, plain, (![A_682, C_683]: (r2_hidden('#skF_3'(A_682, A_682, C_683), C_683) | k1_xboole_0=C_683)), inference(demodulation, [status(thm), theory('equality')], [c_13240, c_12645])).
% 13.25/5.90  tff(c_14071, plain, (![A_682, C_683, B_2]: (r2_hidden('#skF_3'(A_682, A_682, C_683), B_2) | ~r1_tarski(C_683, B_2) | k1_xboole_0=C_683)), inference(resolution, [status(thm)], [c_14015, c_2])).
% 13.25/5.90  tff(c_16922, plain, (![A_827, C_828, B_829]: (r2_hidden('#skF_3'(A_827, A_827, C_828), B_829) | ~r1_tarski(C_828, B_829) | k1_xboole_0=C_828)), inference(resolution, [status(thm)], [c_14015, c_2])).
% 13.25/5.90  tff(c_11758, plain, (![D_11]: (~r2_hidden(D_11, '#skF_5') | ~r2_hidden(D_11, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11380, c_10])).
% 13.25/5.90  tff(c_20154, plain, (![A_904, C_905]: (~r2_hidden('#skF_3'(A_904, A_904, C_905), '#skF_5') | ~r1_tarski(C_905, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')) | k1_xboole_0=C_905)), inference(resolution, [status(thm)], [c_16922, c_11758])).
% 13.25/5.90  tff(c_20175, plain, (![C_683]: (~r1_tarski(C_683, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')) | ~r1_tarski(C_683, '#skF_5') | k1_xboole_0=C_683)), inference(resolution, [status(thm)], [c_14071, c_20154])).
% 13.25/5.90  tff(c_35951, plain, (~r1_tarski(k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4')), '#skF_5') | k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_35928, c_20175])).
% 13.25/5.90  tff(c_36003, plain, (k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_35787, c_35951])).
% 13.25/5.90  tff(c_11107, plain, (![A_507, B_508]: (k1_setfam_1(k2_tarski(A_507, B_508))=k3_xboole_0(A_507, B_508))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.25/5.90  tff(c_11122, plain, (![B_509, A_510]: (k1_setfam_1(k2_tarski(B_509, A_510))=k3_xboole_0(A_510, B_509))), inference(superposition, [status(thm), theory('equality')], [c_38, c_11107])).
% 13.25/5.90  tff(c_11128, plain, (![B_509, A_510]: (k3_xboole_0(B_509, A_510)=k3_xboole_0(A_510, B_509))), inference(superposition, [status(thm), theory('equality')], [c_11122, c_58])).
% 13.25/5.90  tff(c_12025, plain, (![A_585, B_586, C_587]: (k9_subset_1(A_585, B_586, C_587)=k3_xboole_0(B_586, C_587) | ~m1_subset_1(C_587, k1_zfmisc_1(A_585)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.25/5.90  tff(c_12049, plain, (![A_27, B_586]: (k9_subset_1(A_27, B_586, A_27)=k3_xboole_0(B_586, A_27))), inference(resolution, [status(thm)], [c_81, c_12025])).
% 13.25/5.90  tff(c_12164, plain, (![A_597, C_598, B_599]: (k9_subset_1(A_597, C_598, B_599)=k9_subset_1(A_597, B_599, C_598) | ~m1_subset_1(C_598, k1_zfmisc_1(A_597)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.25/5.90  tff(c_12179, plain, (![A_27, B_599]: (k9_subset_1(A_27, B_599, A_27)=k9_subset_1(A_27, A_27, B_599))), inference(resolution, [status(thm)], [c_81, c_12164])).
% 13.25/5.90  tff(c_12190, plain, (![A_27, B_599]: (k9_subset_1(A_27, A_27, B_599)=k3_xboole_0(B_599, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_12049, c_12179])).
% 13.25/5.90  tff(c_13634, plain, (![A_663, B_664, C_665]: (k9_subset_1(A_663, B_664, k3_subset_1(A_663, C_665))=k7_subset_1(A_663, B_664, C_665) | ~m1_subset_1(C_665, k1_zfmisc_1(A_663)) | ~m1_subset_1(B_664, k1_zfmisc_1(A_663)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.25/5.90  tff(c_13660, plain, (![B_666]: (k9_subset_1(k2_struct_0('#skF_4'), B_666, k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'))=k7_subset_1(k2_struct_0('#skF_4'), B_666, '#skF_5') | ~m1_subset_1(B_666, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_11102, c_13634])).
% 13.25/5.90  tff(c_13682, plain, (k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_12190, c_13660])).
% 13.25/5.90  tff(c_13692, plain, (k3_xboole_0(k2_struct_0('#skF_4'), k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'))=k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_11128, c_13682])).
% 13.25/5.90  tff(c_36185, plain, (k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36003, c_36])).
% 13.25/5.90  tff(c_36250, plain, (k3_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4'))=k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36185])).
% 13.25/5.90  tff(c_11416, plain, (![A_550]: (k4_xboole_0(A_550, A_550)=k3_subset_1(A_550, A_550))), inference(resolution, [status(thm)], [c_81, c_11366])).
% 13.25/5.90  tff(c_11422, plain, (![A_550]: (k3_xboole_0(A_550, k1_xboole_0)=k3_subset_1(A_550, A_550))), inference(superposition, [status(thm), theory('equality')], [c_11416, c_11253])).
% 13.25/5.90  tff(c_13253, plain, (![A_550]: (k3_subset_1(A_550, A_550)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13240, c_11422])).
% 13.25/5.90  tff(c_11450, plain, (![A_551]: (k3_xboole_0(A_551, k1_xboole_0)=k3_subset_1(A_551, A_551))), inference(superposition, [status(thm), theory('equality')], [c_11416, c_11253])).
% 13.25/5.90  tff(c_32, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.25/5.90  tff(c_11474, plain, (![A_551]: (k5_xboole_0(A_551, k3_subset_1(A_551, A_551))=k4_xboole_0(A_551, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11450, c_32])).
% 13.25/5.90  tff(c_11503, plain, (![A_551]: (k5_xboole_0(A_551, k3_subset_1(A_551, A_551))=A_551)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_11474])).
% 13.25/5.90  tff(c_13355, plain, (![A_551]: (k5_xboole_0(A_551, k1_xboole_0)=A_551)), inference(demodulation, [status(thm), theory('equality')], [c_13253, c_11503])).
% 13.25/5.90  tff(c_13257, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13240, c_11253])).
% 13.25/5.90  tff(c_11820, plain, (![D_570, A_571, B_572]: (r2_hidden(D_570, k4_xboole_0(A_571, B_572)) | r2_hidden(D_570, B_572) | ~r2_hidden(D_570, A_571))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.25/5.90  tff(c_16999, plain, (![A_830, A_831, B_832]: (r1_tarski(A_830, k4_xboole_0(A_831, B_832)) | r2_hidden('#skF_1'(A_830, k4_xboole_0(A_831, B_832)), B_832) | ~r2_hidden('#skF_1'(A_830, k4_xboole_0(A_831, B_832)), A_831))), inference(resolution, [status(thm)], [c_11820, c_4])).
% 13.25/5.90  tff(c_22982, plain, (![A_969, B_970]: (r2_hidden('#skF_1'(A_969, k4_xboole_0(A_969, B_970)), B_970) | r1_tarski(A_969, k4_xboole_0(A_969, B_970)))), inference(resolution, [status(thm)], [c_6, c_16999])).
% 13.25/5.90  tff(c_11223, plain, (![A_6, B_7, B_526]: (~r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_526), B_7) | r1_tarski(k4_xboole_0(A_6, B_7), B_526))), inference(resolution, [status(thm)], [c_11204, c_10])).
% 13.25/5.90  tff(c_23161, plain, (![A_971, B_972]: (r1_tarski(k4_xboole_0(A_971, B_972), k4_xboole_0(k4_xboole_0(A_971, B_972), B_972)))), inference(resolution, [status(thm)], [c_22982, c_11223])).
% 13.25/5.90  tff(c_15088, plain, (![A_739, B_740]: (r1_tarski(k4_xboole_0(A_739, B_740), A_739))), inference(resolution, [status(thm)], [c_14963, c_4])).
% 13.25/5.90  tff(c_15131, plain, (![A_739, B_740]: (k4_xboole_0(A_739, B_740)=A_739 | ~r1_tarski(A_739, k4_xboole_0(A_739, B_740)))), inference(resolution, [status(thm)], [c_15088, c_26])).
% 13.25/5.90  tff(c_23300, plain, (![A_973, B_974]: (k4_xboole_0(k4_xboole_0(A_973, B_974), B_974)=k4_xboole_0(A_973, B_974))), inference(resolution, [status(thm)], [c_23161, c_15131])).
% 13.25/5.90  tff(c_23383, plain, (![A_973, B_974]: (k4_xboole_0(k4_xboole_0(A_973, B_974), k4_xboole_0(A_973, B_974))=k3_xboole_0(k4_xboole_0(A_973, B_974), B_974))), inference(superposition, [status(thm), theory('equality')], [c_23300, c_36])).
% 13.25/5.90  tff(c_23697, plain, (![B_979, A_980]: (k3_xboole_0(B_979, k4_xboole_0(A_980, B_979))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13257, c_11128, c_23383])).
% 13.25/5.90  tff(c_24327, plain, (![A_985, B_986]: (k3_xboole_0(k4_xboole_0(A_985, B_986), k3_xboole_0(A_985, B_986))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_23697])).
% 13.25/5.90  tff(c_25036, plain, (![B_996, A_997]: (k3_xboole_0(k4_xboole_0(B_996, A_997), k3_xboole_0(A_997, B_996))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11128, c_24327])).
% 13.25/5.90  tff(c_11183, plain, (![A_516, B_517]: (k5_xboole_0(A_516, k3_xboole_0(A_516, B_517))=k4_xboole_0(A_516, B_517))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.25/5.90  tff(c_11192, plain, (![A_510, B_509]: (k5_xboole_0(A_510, k3_xboole_0(B_509, A_510))=k4_xboole_0(A_510, B_509))), inference(superposition, [status(thm), theory('equality')], [c_11128, c_11183])).
% 13.25/5.90  tff(c_25092, plain, (![A_997, B_996]: (k4_xboole_0(k3_xboole_0(A_997, B_996), k4_xboole_0(B_996, A_997))=k5_xboole_0(k3_xboole_0(A_997, B_996), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_25036, c_11192])).
% 13.25/5.90  tff(c_30075, plain, (![A_1050, B_1051]: (k4_xboole_0(k3_xboole_0(A_1050, B_1051), k4_xboole_0(B_1051, A_1050))=k3_xboole_0(A_1050, B_1051))), inference(demodulation, [status(thm), theory('equality')], [c_13355, c_25092])).
% 13.25/5.90  tff(c_30385, plain, (![A_510, B_509]: (k4_xboole_0(k3_xboole_0(A_510, B_509), k4_xboole_0(A_510, B_509))=k3_xboole_0(B_509, A_510))), inference(superposition, [status(thm), theory('equality')], [c_11128, c_30075])).
% 13.25/5.90  tff(c_36298, plain, (k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k4_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), k2_struct_0('#skF_4')))=k3_xboole_0(k2_struct_0('#skF_4'), k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36250, c_30385])).
% 13.25/5.90  tff(c_36428, plain, (k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5')=k3_subset_1(k2_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36003, c_13692, c_36298])).
% 13.25/5.90  tff(c_13475, plain, (![A_657, B_658]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_657), k2_struct_0(A_657), B_658), A_657) | ~v4_pre_topc(B_658, A_657) | ~m1_subset_1(B_658, k1_zfmisc_1(u1_struct_0(A_657))) | ~l1_pre_topc(A_657))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.25/5.90  tff(c_13481, plain, (![B_658]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), B_658), '#skF_4') | ~v4_pre_topc(B_658, '#skF_4') | ~m1_subset_1(B_658, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11100, c_13475])).
% 13.25/5.90  tff(c_13484, plain, (![B_658]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), B_658), '#skF_4') | ~v4_pre_topc(B_658, '#skF_4') | ~m1_subset_1(B_658, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_11100, c_13481])).
% 13.25/5.90  tff(c_36472, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v4_pre_topc('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_36428, c_13484])).
% 13.25/5.90  tff(c_36479, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11102, c_11059, c_36472])).
% 13.25/5.90  tff(c_36481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11101, c_36479])).
% 13.25/5.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.25/5.90  
% 13.25/5.90  Inference rules
% 13.25/5.90  ----------------------
% 13.25/5.90  #Ref     : 0
% 13.25/5.90  #Sup     : 8823
% 13.25/5.90  #Fact    : 0
% 13.25/5.90  #Define  : 0
% 13.25/5.90  #Split   : 29
% 13.25/5.90  #Chain   : 0
% 13.25/5.90  #Close   : 0
% 13.25/5.90  
% 13.25/5.90  Ordering : KBO
% 13.25/5.90  
% 13.25/5.90  Simplification rules
% 13.25/5.90  ----------------------
% 13.25/5.90  #Subsume      : 1987
% 13.25/5.90  #Demod        : 8266
% 13.25/5.90  #Tautology    : 3270
% 13.25/5.90  #SimpNegUnit  : 17
% 13.25/5.90  #BackRed      : 127
% 13.25/5.90  
% 13.25/5.90  #Partial instantiations: 0
% 13.25/5.90  #Strategies tried      : 1
% 13.25/5.90  
% 13.25/5.90  Timing (in seconds)
% 13.25/5.90  ----------------------
% 13.25/5.90  Preprocessing        : 0.34
% 13.25/5.90  Parsing              : 0.18
% 13.25/5.90  CNF conversion       : 0.03
% 13.25/5.90  Main loop            : 4.76
% 13.25/5.90  Inferencing          : 1.01
% 13.25/5.90  Reduction            : 2.07
% 13.25/5.90  Demodulation         : 1.69
% 13.25/5.90  BG Simplification    : 0.12
% 13.25/5.90  Subsumption          : 1.27
% 13.25/5.90  Abstraction          : 0.18
% 13.25/5.90  MUC search           : 0.00
% 13.25/5.90  Cooper               : 0.00
% 13.25/5.90  Total                : 5.17
% 13.25/5.90  Index Insertion      : 0.00
% 13.25/5.90  Index Deletion       : 0.00
% 13.25/5.90  Index Matching       : 0.00
% 13.25/5.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------

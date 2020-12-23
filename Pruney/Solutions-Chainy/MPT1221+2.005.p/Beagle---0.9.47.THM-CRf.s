%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:24 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 294 expanded)
%              Number of leaves         :   37 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  142 ( 516 expanded)
%              Number of equality atoms :   50 ( 128 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    ! [A_28] :
      ( l1_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_94,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_30,c_56])).

tff(c_98,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_94])).

tff(c_36,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_99,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_100,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_32])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_196,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_42])).

tff(c_197,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_196])).

tff(c_271,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k3_subset_1(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_278,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_271])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_199,plain,(
    ! [A_49,B_50] : k3_xboole_0(k4_xboole_0(A_49,B_50),A_49) = k4_xboole_0(A_49,B_50) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_134,plain,(
    ! [B_45,A_46] : k1_setfam_1(k2_tarski(B_45,A_46)) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_110])).

tff(c_22,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_22])).

tff(c_205,plain,(
    ! [A_49,B_50] : k3_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_140])).

tff(c_337,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_205])).

tff(c_346,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_337])).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k3_subset_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_430,plain,(
    ! [A_66,B_67,C_68] :
      ( k9_subset_1(A_66,B_67,C_68) = k3_xboole_0(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_715,plain,(
    ! [A_94,B_95,B_96] :
      ( k9_subset_1(A_94,B_95,k3_subset_1(A_94,B_96)) = k3_xboole_0(B_95,k3_subset_1(A_94,B_96))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_16,c_430])).

tff(c_723,plain,(
    ! [B_95] : k9_subset_1(k2_struct_0('#skF_1'),B_95,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(B_95,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_100,c_715])).

tff(c_562,plain,(
    ! [A_81,B_82,C_83] :
      ( k9_subset_1(A_81,B_82,k3_subset_1(A_81,C_83)) = k7_subset_1(A_81,B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_570,plain,(
    ! [B_82] :
      ( k9_subset_1(k2_struct_0('#skF_1'),B_82,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),B_82,'#skF_2')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_100,c_562])).

tff(c_829,plain,(
    ! [B_107] :
      ( k3_xboole_0(B_107,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_570])).

tff(c_840,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_829])).

tff(c_844,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_840])).

tff(c_664,plain,(
    ! [B_88,A_89] :
      ( v4_pre_topc(B_88,A_89)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_89),k2_struct_0(A_89),B_88),A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_670,plain,(
    ! [B_88] :
      ( v4_pre_topc(B_88,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_88),'#skF_1')
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_664])).

tff(c_907,plain,(
    ! [B_112] :
      ( v4_pre_topc(B_112,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_112),'#skF_1')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_98,c_670])).

tff(c_910,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_907])).

tff(c_919,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_197,c_910])).

tff(c_921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_919])).

tff(c_922,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_930,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_922])).

tff(c_925,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_32])).

tff(c_923,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1096,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(A_131,B_132) = k3_subset_1(A_131,B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1107,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_925,c_1096])).

tff(c_946,plain,(
    ! [A_115,B_116] :
      ( k3_xboole_0(A_115,B_116) = A_115
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1024,plain,(
    ! [A_125,B_126] : k3_xboole_0(k4_xboole_0(A_125,B_126),A_125) = k4_xboole_0(A_125,B_126) ),
    inference(resolution,[status(thm)],[c_6,c_946])).

tff(c_931,plain,(
    ! [A_113,B_114] : k1_setfam_1(k2_tarski(A_113,B_114)) = k3_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_960,plain,(
    ! [B_119,A_120] : k1_setfam_1(k2_tarski(B_119,A_120)) = k3_xboole_0(A_120,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_931])).

tff(c_966,plain,(
    ! [B_119,A_120] : k3_xboole_0(B_119,A_120) = k3_xboole_0(A_120,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_22])).

tff(c_1030,plain,(
    ! [A_125,B_126] : k3_xboole_0(A_125,k4_xboole_0(A_125,B_126)) = k4_xboole_0(A_125,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_966])).

tff(c_1166,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1107,c_1030])).

tff(c_1175,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_1166])).

tff(c_1200,plain,(
    ! [A_137,B_138,C_139] :
      ( k9_subset_1(A_137,B_138,C_139) = k3_xboole_0(B_138,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1548,plain,(
    ! [A_169,B_170,B_171] :
      ( k9_subset_1(A_169,B_170,k3_subset_1(A_169,B_171)) = k3_xboole_0(B_170,k3_subset_1(A_169,B_171))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(A_169)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1200])).

tff(c_1556,plain,(
    ! [B_170] : k9_subset_1(k2_struct_0('#skF_1'),B_170,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(B_170,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_925,c_1548])).

tff(c_1304,plain,(
    ! [A_149,B_150,C_151] :
      ( k9_subset_1(A_149,B_150,k3_subset_1(A_149,C_151)) = k7_subset_1(A_149,B_150,C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(A_149))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1312,plain,(
    ! [B_150] :
      ( k9_subset_1(k2_struct_0('#skF_1'),B_150,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),B_150,'#skF_2')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_925,c_1304])).

tff(c_1667,plain,(
    ! [B_182] :
      ( k3_xboole_0(B_182,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),B_182,'#skF_2')
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1556,c_1312])).

tff(c_1678,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_1667])).

tff(c_1682,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_1678])).

tff(c_1264,plain,(
    ! [A_144,B_145] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_144),k2_struct_0(A_144),B_145),A_144)
      | ~ v4_pre_topc(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1267,plain,(
    ! [B_145] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_145),'#skF_1')
      | ~ v4_pre_topc(B_145,'#skF_1')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_1264])).

tff(c_1269,plain,(
    ! [B_145] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_145),'#skF_1')
      | ~ v4_pre_topc(B_145,'#skF_1')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_98,c_1267])).

tff(c_1686,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1682,c_1269])).

tff(c_1690,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_923,c_1686])).

tff(c_1692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_930,c_1690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.61  
% 3.24/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.61  %$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.24/1.61  
% 3.24/1.61  %Foreground sorts:
% 3.24/1.61  
% 3.24/1.61  
% 3.24/1.61  %Background operators:
% 3.24/1.61  
% 3.24/1.61  
% 3.24/1.61  %Foreground operators:
% 3.24/1.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.24/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.24/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.61  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.24/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.61  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.24/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.24/1.61  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.24/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.24/1.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.24/1.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.24/1.61  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.24/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.24/1.61  
% 3.56/1.63  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 3.56/1.63  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.56/1.63  tff(f_64, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.56/1.63  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.56/1.63  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.56/1.63  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.56/1.63  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.56/1.63  tff(f_60, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.56/1.63  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.56/1.63  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.56/1.63  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.56/1.63  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.56/1.63  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 3.56/1.63  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 3.56/1.63  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.56/1.63  tff(c_30, plain, (![A_28]: (l1_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.56/1.63  tff(c_56, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.63  tff(c_94, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_30, c_56])).
% 3.56/1.63  tff(c_98, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_94])).
% 3.56/1.63  tff(c_36, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.56/1.63  tff(c_99, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.56/1.63  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.56/1.63  tff(c_100, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_32])).
% 3.56/1.63  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.56/1.63  tff(c_196, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_42])).
% 3.56/1.63  tff(c_197, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_99, c_196])).
% 3.56/1.63  tff(c_271, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k3_subset_1(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.63  tff(c_278, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_100, c_271])).
% 3.56/1.63  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.63  tff(c_105, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.63  tff(c_199, plain, (![A_49, B_50]: (k3_xboole_0(k4_xboole_0(A_49, B_50), A_49)=k4_xboole_0(A_49, B_50))), inference(resolution, [status(thm)], [c_6, c_105])).
% 3.56/1.63  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.63  tff(c_110, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.56/1.63  tff(c_134, plain, (![B_45, A_46]: (k1_setfam_1(k2_tarski(B_45, A_46))=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_8, c_110])).
% 3.56/1.63  tff(c_22, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.56/1.63  tff(c_140, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_134, c_22])).
% 3.56/1.63  tff(c_205, plain, (![A_49, B_50]: (k3_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_199, c_140])).
% 3.56/1.63  tff(c_337, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_278, c_205])).
% 3.56/1.63  tff(c_346, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_337])).
% 3.56/1.63  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.63  tff(c_14, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.63  tff(c_43, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 3.56/1.63  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(k3_subset_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.56/1.63  tff(c_430, plain, (![A_66, B_67, C_68]: (k9_subset_1(A_66, B_67, C_68)=k3_xboole_0(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.63  tff(c_715, plain, (![A_94, B_95, B_96]: (k9_subset_1(A_94, B_95, k3_subset_1(A_94, B_96))=k3_xboole_0(B_95, k3_subset_1(A_94, B_96)) | ~m1_subset_1(B_96, k1_zfmisc_1(A_94)))), inference(resolution, [status(thm)], [c_16, c_430])).
% 3.56/1.63  tff(c_723, plain, (![B_95]: (k9_subset_1(k2_struct_0('#skF_1'), B_95, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(B_95, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_100, c_715])).
% 3.56/1.63  tff(c_562, plain, (![A_81, B_82, C_83]: (k9_subset_1(A_81, B_82, k3_subset_1(A_81, C_83))=k7_subset_1(A_81, B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.56/1.63  tff(c_570, plain, (![B_82]: (k9_subset_1(k2_struct_0('#skF_1'), B_82, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), B_82, '#skF_2') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_100, c_562])).
% 3.56/1.63  tff(c_829, plain, (![B_107]: (k3_xboole_0(B_107, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_723, c_570])).
% 3.56/1.63  tff(c_840, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_43, c_829])).
% 3.56/1.63  tff(c_844, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_840])).
% 3.56/1.63  tff(c_664, plain, (![B_88, A_89]: (v4_pre_topc(B_88, A_89) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_89), k2_struct_0(A_89), B_88), A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.63  tff(c_670, plain, (![B_88]: (v4_pre_topc(B_88, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_88), '#skF_1') | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_664])).
% 3.56/1.63  tff(c_907, plain, (![B_112]: (v4_pre_topc(B_112, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_112), '#skF_1') | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_98, c_670])).
% 3.56/1.63  tff(c_910, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_844, c_907])).
% 3.56/1.63  tff(c_919, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_197, c_910])).
% 3.56/1.63  tff(c_921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_919])).
% 3.56/1.63  tff(c_922, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.56/1.63  tff(c_930, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_922])).
% 3.56/1.63  tff(c_925, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_32])).
% 3.56/1.63  tff(c_923, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.56/1.63  tff(c_1096, plain, (![A_131, B_132]: (k4_xboole_0(A_131, B_132)=k3_subset_1(A_131, B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.63  tff(c_1107, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_925, c_1096])).
% 3.56/1.63  tff(c_946, plain, (![A_115, B_116]: (k3_xboole_0(A_115, B_116)=A_115 | ~r1_tarski(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.63  tff(c_1024, plain, (![A_125, B_126]: (k3_xboole_0(k4_xboole_0(A_125, B_126), A_125)=k4_xboole_0(A_125, B_126))), inference(resolution, [status(thm)], [c_6, c_946])).
% 3.56/1.63  tff(c_931, plain, (![A_113, B_114]: (k1_setfam_1(k2_tarski(A_113, B_114))=k3_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.56/1.63  tff(c_960, plain, (![B_119, A_120]: (k1_setfam_1(k2_tarski(B_119, A_120))=k3_xboole_0(A_120, B_119))), inference(superposition, [status(thm), theory('equality')], [c_8, c_931])).
% 3.56/1.63  tff(c_966, plain, (![B_119, A_120]: (k3_xboole_0(B_119, A_120)=k3_xboole_0(A_120, B_119))), inference(superposition, [status(thm), theory('equality')], [c_960, c_22])).
% 3.56/1.63  tff(c_1030, plain, (![A_125, B_126]: (k3_xboole_0(A_125, k4_xboole_0(A_125, B_126))=k4_xboole_0(A_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_1024, c_966])).
% 3.56/1.63  tff(c_1166, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1107, c_1030])).
% 3.56/1.63  tff(c_1175, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_1166])).
% 3.56/1.63  tff(c_1200, plain, (![A_137, B_138, C_139]: (k9_subset_1(A_137, B_138, C_139)=k3_xboole_0(B_138, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.63  tff(c_1548, plain, (![A_169, B_170, B_171]: (k9_subset_1(A_169, B_170, k3_subset_1(A_169, B_171))=k3_xboole_0(B_170, k3_subset_1(A_169, B_171)) | ~m1_subset_1(B_171, k1_zfmisc_1(A_169)))), inference(resolution, [status(thm)], [c_16, c_1200])).
% 3.56/1.63  tff(c_1556, plain, (![B_170]: (k9_subset_1(k2_struct_0('#skF_1'), B_170, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(B_170, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_925, c_1548])).
% 3.56/1.63  tff(c_1304, plain, (![A_149, B_150, C_151]: (k9_subset_1(A_149, B_150, k3_subset_1(A_149, C_151))=k7_subset_1(A_149, B_150, C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(A_149)) | ~m1_subset_1(B_150, k1_zfmisc_1(A_149)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.56/1.63  tff(c_1312, plain, (![B_150]: (k9_subset_1(k2_struct_0('#skF_1'), B_150, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), B_150, '#skF_2') | ~m1_subset_1(B_150, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_925, c_1304])).
% 3.56/1.63  tff(c_1667, plain, (![B_182]: (k3_xboole_0(B_182, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), B_182, '#skF_2') | ~m1_subset_1(B_182, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1556, c_1312])).
% 3.56/1.63  tff(c_1678, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_43, c_1667])).
% 3.56/1.63  tff(c_1682, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_1678])).
% 3.56/1.63  tff(c_1264, plain, (![A_144, B_145]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_144), k2_struct_0(A_144), B_145), A_144) | ~v4_pre_topc(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.63  tff(c_1267, plain, (![B_145]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_145), '#skF_1') | ~v4_pre_topc(B_145, '#skF_1') | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_1264])).
% 3.56/1.63  tff(c_1269, plain, (![B_145]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_145), '#skF_1') | ~v4_pre_topc(B_145, '#skF_1') | ~m1_subset_1(B_145, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_98, c_1267])).
% 3.56/1.63  tff(c_1686, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1682, c_1269])).
% 3.56/1.63  tff(c_1690, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_925, c_923, c_1686])).
% 3.56/1.63  tff(c_1692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_930, c_1690])).
% 3.56/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.63  
% 3.56/1.63  Inference rules
% 3.56/1.63  ----------------------
% 3.56/1.63  #Ref     : 0
% 3.56/1.63  #Sup     : 412
% 3.56/1.63  #Fact    : 0
% 3.56/1.63  #Define  : 0
% 3.56/1.63  #Split   : 3
% 3.56/1.63  #Chain   : 0
% 3.56/1.63  #Close   : 0
% 3.56/1.63  
% 3.56/1.63  Ordering : KBO
% 3.56/1.63  
% 3.56/1.63  Simplification rules
% 3.56/1.63  ----------------------
% 3.56/1.63  #Subsume      : 3
% 3.56/1.63  #Demod        : 184
% 3.56/1.63  #Tautology    : 268
% 3.56/1.63  #SimpNegUnit  : 3
% 3.56/1.63  #BackRed      : 9
% 3.56/1.63  
% 3.56/1.63  #Partial instantiations: 0
% 3.56/1.63  #Strategies tried      : 1
% 3.56/1.63  
% 3.56/1.63  Timing (in seconds)
% 3.56/1.63  ----------------------
% 3.56/1.64  Preprocessing        : 0.33
% 3.56/1.64  Parsing              : 0.17
% 3.56/1.64  CNF conversion       : 0.02
% 3.56/1.64  Main loop            : 0.54
% 3.56/1.64  Inferencing          : 0.20
% 3.56/1.64  Reduction            : 0.19
% 3.56/1.64  Demodulation         : 0.14
% 3.56/1.64  BG Simplification    : 0.03
% 3.56/1.64  Subsumption          : 0.08
% 3.56/1.64  Abstraction          : 0.03
% 3.56/1.64  MUC search           : 0.00
% 3.56/1.64  Cooper               : 0.00
% 3.56/1.64  Total                : 0.91
% 3.56/1.64  Index Insertion      : 0.00
% 3.56/1.64  Index Deletion       : 0.00
% 3.56/1.64  Index Matching       : 0.00
% 3.56/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------

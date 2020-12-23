%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:40 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 745 expanded)
%              Number of leaves         :   35 ( 261 expanded)
%              Depth                    :   26
%              Number of atoms          :  134 (1026 expanded)
%              Number of equality atoms :   64 ( 516 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_178,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_200,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ r1_tarski(A_55,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_178])).

tff(c_213,plain,(
    ! [B_6] : k3_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_200])).

tff(c_24,plain,(
    ! [A_18,B_19] : k1_setfam_1(k2_tarski(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_140,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_155,plain,(
    ! [B_51,A_52] : k1_setfam_1(k2_tarski(B_51,A_52)) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_140])).

tff(c_229,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,A_58) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_155])).

tff(c_270,plain,(
    ! [B_6] : k3_xboole_0(B_6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_229])).

tff(c_369,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_384,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_369])).

tff(c_388,plain,(
    ! [A_66] : k4_xboole_0(A_66,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_384])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_393,plain,(
    ! [A_66] : k4_xboole_0(A_66,k1_xboole_0) = k3_xboole_0(A_66,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_18])).

tff(c_405,plain,(
    ! [A_66] : k3_xboole_0(A_66,A_66) = A_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_393])).

tff(c_40,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_57,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    ! [A_42,B_41] : r1_tarski(A_42,k2_xboole_0(B_41,A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_20])).

tff(c_550,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(k4_xboole_0(A_75,B_76),C_77)
      | ~ r1_tarski(A_75,k2_xboole_0(B_76,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_575,plain,(
    ! [A_78,C_79] :
      ( r1_tarski(A_78,C_79)
      | ~ r1_tarski(A_78,k2_xboole_0(k1_xboole_0,C_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_550])).

tff(c_627,plain,(
    ! [C_80] : r1_tarski(k2_xboole_0(k1_xboole_0,C_80),C_80) ),
    inference(resolution,[status(thm)],[c_8,c_575])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_637,plain,(
    ! [C_80] :
      ( k2_xboole_0(k1_xboole_0,C_80) = C_80
      | ~ r1_tarski(C_80,k2_xboole_0(k1_xboole_0,C_80)) ) ),
    inference(resolution,[status(thm)],[c_627,c_4])).

tff(c_674,plain,(
    ! [C_81] : k2_xboole_0(k1_xboole_0,C_81) = C_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_637])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_683,plain,(
    ! [C_81] : k2_xboole_0(C_81,k1_xboole_0) = C_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_2])).

tff(c_199,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_178])).

tff(c_571,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k1_xboole_0
      | ~ r1_tarski(A_75,k2_xboole_0(B_76,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_550,c_199])).

tff(c_918,plain,(
    ! [A_100,B_101] :
      ( k4_xboole_0(A_100,B_101) = k1_xboole_0
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_571])).

tff(c_960,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_918])).

tff(c_1063,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_18])).

tff(c_1067,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1063])).

tff(c_167,plain,(
    ! [B_19,A_18] : k3_xboole_0(B_19,A_18) = k3_xboole_0(A_18,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_155])).

tff(c_255,plain,(
    ! [A_58,B_57] : r1_tarski(k3_xboole_0(A_58,B_57),B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_10])).

tff(c_1180,plain,(
    ! [A_109,B_110] : k4_xboole_0(k3_xboole_0(A_109,B_110),B_110) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_255,c_918])).

tff(c_1191,plain,(
    ! [A_109,B_110] : k4_xboole_0(k3_xboole_0(A_109,B_110),k1_xboole_0) = k3_xboole_0(k3_xboole_0(A_109,B_110),B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_18])).

tff(c_1553,plain,(
    ! [A_119,B_120] : k3_xboole_0(k3_xboole_0(A_119,B_120),B_120) = k3_xboole_0(A_119,B_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1191])).

tff(c_2362,plain,(
    ! [B_137,A_138] : k3_xboole_0(k3_xboole_0(B_137,A_138),B_137) = k3_xboole_0(A_138,B_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_1553])).

tff(c_2473,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_2362])).

tff(c_2540,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_2473])).

tff(c_34,plain,(
    ! [B_30,A_29] :
      ( k3_xboole_0(k1_relat_1(B_30),A_29) = k1_relat_1(k7_relat_1(B_30,A_29))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2585,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2540,c_34])).

tff(c_2623,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2585])).

tff(c_473,plain,(
    ! [B_70,A_71] :
      ( k3_xboole_0(k1_relat_1(B_70),A_71) = k1_relat_1(k7_relat_1(B_70,A_71))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_499,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_70,A_71)),k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_10])).

tff(c_2640,plain,(
    ! [A_71] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_71)),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_499])).

tff(c_4230,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2640])).

tff(c_4233,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_4230])).

tff(c_4237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4233])).

tff(c_4239,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2640])).

tff(c_28,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2649,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_28])).

tff(c_4670,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4239,c_2649])).

tff(c_30,plain,(
    ! [A_23,C_27,B_26] :
      ( k9_relat_1(k7_relat_1(A_23,C_27),B_26) = k9_relat_1(A_23,B_26)
      | ~ r1_tarski(B_26,C_27)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4674,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4670,c_30])).

tff(c_4681,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_4674])).

tff(c_32,plain,(
    ! [A_28] :
      ( k10_relat_1(A_28,k2_relat_1(A_28)) = k1_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4692,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4681,c_32])).

tff(c_4698,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4239,c_2623,c_4692])).

tff(c_750,plain,(
    ! [A_83,C_84,B_85] :
      ( k3_xboole_0(A_83,k10_relat_1(C_84,B_85)) = k10_relat_1(k7_relat_1(C_84,A_83),B_85)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_193,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k3_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_178])).

tff(c_6559,plain,(
    ! [A_201,C_202,B_203] :
      ( k3_xboole_0(A_201,k10_relat_1(C_202,B_203)) = A_201
      | ~ r1_tarski(A_201,k10_relat_1(k7_relat_1(C_202,A_201),B_203))
      | ~ v1_relat_1(C_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_193])).

tff(c_6566,plain,
    ( k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4698,c_6559])).

tff(c_6590,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_6566])).

tff(c_6682,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6590,c_255])).

tff(c_6721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_6682])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.14  
% 5.71/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.14  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.71/2.14  
% 5.71/2.14  %Foreground sorts:
% 5.71/2.14  
% 5.71/2.14  
% 5.71/2.14  %Background operators:
% 5.71/2.14  
% 5.71/2.14  
% 5.71/2.14  %Foreground operators:
% 5.71/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.71/2.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.71/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.71/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.71/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.71/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.71/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.71/2.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.71/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.71/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.71/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.71/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.71/2.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.71/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.71/2.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.71/2.14  
% 5.76/2.16  tff(f_85, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.76/2.16  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.76/2.16  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.76/2.16  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.76/2.16  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.76/2.16  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.76/2.16  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.76/2.16  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.76/2.16  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.76/2.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.76/2.16  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.76/2.16  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.76/2.16  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 5.76/2.16  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 5.76/2.16  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 5.76/2.16  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 5.76/2.16  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 5.76/2.16  tff(c_38, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.76/2.16  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.76/2.16  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.76/2.16  tff(c_26, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.76/2.16  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.76/2.16  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.76/2.16  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.76/2.16  tff(c_178, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.76/2.16  tff(c_200, plain, (![A_55]: (k1_xboole_0=A_55 | ~r1_tarski(A_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_178])).
% 5.76/2.16  tff(c_213, plain, (![B_6]: (k3_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_200])).
% 5.76/2.16  tff(c_24, plain, (![A_18, B_19]: (k1_setfam_1(k2_tarski(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.76/2.16  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.76/2.16  tff(c_140, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.76/2.16  tff(c_155, plain, (![B_51, A_52]: (k1_setfam_1(k2_tarski(B_51, A_52))=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_22, c_140])).
% 5.76/2.16  tff(c_229, plain, (![B_57, A_58]: (k3_xboole_0(B_57, A_58)=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_24, c_155])).
% 5.76/2.16  tff(c_270, plain, (![B_6]: (k3_xboole_0(B_6, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_213, c_229])).
% 5.76/2.16  tff(c_369, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.76/2.16  tff(c_384, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_369])).
% 5.76/2.16  tff(c_388, plain, (![A_66]: (k4_xboole_0(A_66, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_270, c_384])).
% 5.76/2.16  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.76/2.16  tff(c_393, plain, (![A_66]: (k4_xboole_0(A_66, k1_xboole_0)=k3_xboole_0(A_66, A_66))), inference(superposition, [status(thm), theory('equality')], [c_388, c_18])).
% 5.76/2.16  tff(c_405, plain, (![A_66]: (k3_xboole_0(A_66, A_66)=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_393])).
% 5.76/2.16  tff(c_40, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.76/2.16  tff(c_57, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.76/2.16  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.76/2.16  tff(c_72, plain, (![A_42, B_41]: (r1_tarski(A_42, k2_xboole_0(B_41, A_42)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_20])).
% 5.76/2.16  tff(c_550, plain, (![A_75, B_76, C_77]: (r1_tarski(k4_xboole_0(A_75, B_76), C_77) | ~r1_tarski(A_75, k2_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.76/2.16  tff(c_575, plain, (![A_78, C_79]: (r1_tarski(A_78, C_79) | ~r1_tarski(A_78, k2_xboole_0(k1_xboole_0, C_79)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_550])).
% 5.76/2.16  tff(c_627, plain, (![C_80]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_80), C_80))), inference(resolution, [status(thm)], [c_8, c_575])).
% 5.76/2.16  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.76/2.16  tff(c_637, plain, (![C_80]: (k2_xboole_0(k1_xboole_0, C_80)=C_80 | ~r1_tarski(C_80, k2_xboole_0(k1_xboole_0, C_80)))), inference(resolution, [status(thm)], [c_627, c_4])).
% 5.76/2.16  tff(c_674, plain, (![C_81]: (k2_xboole_0(k1_xboole_0, C_81)=C_81)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_637])).
% 5.76/2.16  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.76/2.16  tff(c_683, plain, (![C_81]: (k2_xboole_0(C_81, k1_xboole_0)=C_81)), inference(superposition, [status(thm), theory('equality')], [c_674, c_2])).
% 5.76/2.16  tff(c_199, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_178])).
% 5.76/2.16  tff(c_571, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k1_xboole_0 | ~r1_tarski(A_75, k2_xboole_0(B_76, k1_xboole_0)))), inference(resolution, [status(thm)], [c_550, c_199])).
% 5.76/2.16  tff(c_918, plain, (![A_100, B_101]: (k4_xboole_0(A_100, B_101)=k1_xboole_0 | ~r1_tarski(A_100, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_571])).
% 5.76/2.16  tff(c_960, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_918])).
% 5.76/2.16  tff(c_1063, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_960, c_18])).
% 5.76/2.16  tff(c_1067, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1063])).
% 5.76/2.16  tff(c_167, plain, (![B_19, A_18]: (k3_xboole_0(B_19, A_18)=k3_xboole_0(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_155])).
% 5.76/2.16  tff(c_255, plain, (![A_58, B_57]: (r1_tarski(k3_xboole_0(A_58, B_57), B_57))), inference(superposition, [status(thm), theory('equality')], [c_229, c_10])).
% 5.76/2.16  tff(c_1180, plain, (![A_109, B_110]: (k4_xboole_0(k3_xboole_0(A_109, B_110), B_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_255, c_918])).
% 5.76/2.16  tff(c_1191, plain, (![A_109, B_110]: (k4_xboole_0(k3_xboole_0(A_109, B_110), k1_xboole_0)=k3_xboole_0(k3_xboole_0(A_109, B_110), B_110))), inference(superposition, [status(thm), theory('equality')], [c_1180, c_18])).
% 5.76/2.16  tff(c_1553, plain, (![A_119, B_120]: (k3_xboole_0(k3_xboole_0(A_119, B_120), B_120)=k3_xboole_0(A_119, B_120))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1191])).
% 5.76/2.16  tff(c_2362, plain, (![B_137, A_138]: (k3_xboole_0(k3_xboole_0(B_137, A_138), B_137)=k3_xboole_0(A_138, B_137))), inference(superposition, [status(thm), theory('equality')], [c_167, c_1553])).
% 5.76/2.16  tff(c_2473, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1067, c_2362])).
% 5.76/2.16  tff(c_2540, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_405, c_2473])).
% 5.76/2.16  tff(c_34, plain, (![B_30, A_29]: (k3_xboole_0(k1_relat_1(B_30), A_29)=k1_relat_1(k7_relat_1(B_30, A_29)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.76/2.16  tff(c_2585, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2540, c_34])).
% 5.76/2.16  tff(c_2623, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2585])).
% 5.76/2.16  tff(c_473, plain, (![B_70, A_71]: (k3_xboole_0(k1_relat_1(B_70), A_71)=k1_relat_1(k7_relat_1(B_70, A_71)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.76/2.16  tff(c_499, plain, (![B_70, A_71]: (r1_tarski(k1_relat_1(k7_relat_1(B_70, A_71)), k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(superposition, [status(thm), theory('equality')], [c_473, c_10])).
% 5.76/2.16  tff(c_2640, plain, (![A_71]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_71)), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2623, c_499])).
% 5.76/2.16  tff(c_4230, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2640])).
% 5.76/2.16  tff(c_4233, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_4230])).
% 5.76/2.16  tff(c_4237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_4233])).
% 5.76/2.16  tff(c_4239, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_2640])).
% 5.76/2.16  tff(c_28, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.76/2.16  tff(c_2649, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2623, c_28])).
% 5.76/2.16  tff(c_4670, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4239, c_2649])).
% 5.76/2.16  tff(c_30, plain, (![A_23, C_27, B_26]: (k9_relat_1(k7_relat_1(A_23, C_27), B_26)=k9_relat_1(A_23, B_26) | ~r1_tarski(B_26, C_27) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.76/2.16  tff(c_4674, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4670, c_30])).
% 5.76/2.16  tff(c_4681, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_4674])).
% 5.76/2.16  tff(c_32, plain, (![A_28]: (k10_relat_1(A_28, k2_relat_1(A_28))=k1_relat_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.76/2.16  tff(c_4692, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4681, c_32])).
% 5.76/2.16  tff(c_4698, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4239, c_2623, c_4692])).
% 5.76/2.16  tff(c_750, plain, (![A_83, C_84, B_85]: (k3_xboole_0(A_83, k10_relat_1(C_84, B_85))=k10_relat_1(k7_relat_1(C_84, A_83), B_85) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.76/2.16  tff(c_193, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k3_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_178])).
% 5.76/2.16  tff(c_6559, plain, (![A_201, C_202, B_203]: (k3_xboole_0(A_201, k10_relat_1(C_202, B_203))=A_201 | ~r1_tarski(A_201, k10_relat_1(k7_relat_1(C_202, A_201), B_203)) | ~v1_relat_1(C_202))), inference(superposition, [status(thm), theory('equality')], [c_750, c_193])).
% 5.76/2.16  tff(c_6566, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4698, c_6559])).
% 5.76/2.16  tff(c_6590, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_6566])).
% 5.76/2.16  tff(c_6682, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6590, c_255])).
% 5.76/2.16  tff(c_6721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_6682])).
% 5.76/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.16  
% 5.76/2.16  Inference rules
% 5.76/2.16  ----------------------
% 5.76/2.16  #Ref     : 0
% 5.76/2.16  #Sup     : 1643
% 5.76/2.16  #Fact    : 0
% 5.76/2.16  #Define  : 0
% 5.76/2.16  #Split   : 3
% 5.76/2.16  #Chain   : 0
% 5.76/2.16  #Close   : 0
% 5.76/2.16  
% 5.76/2.16  Ordering : KBO
% 5.76/2.16  
% 5.76/2.16  Simplification rules
% 5.76/2.16  ----------------------
% 5.76/2.16  #Subsume      : 189
% 5.76/2.16  #Demod        : 2023
% 5.76/2.16  #Tautology    : 1075
% 5.76/2.16  #SimpNegUnit  : 1
% 5.76/2.16  #BackRed      : 3
% 5.76/2.16  
% 5.76/2.16  #Partial instantiations: 0
% 5.76/2.16  #Strategies tried      : 1
% 5.76/2.16  
% 5.76/2.16  Timing (in seconds)
% 5.76/2.16  ----------------------
% 5.76/2.16  Preprocessing        : 0.31
% 5.76/2.16  Parsing              : 0.16
% 5.76/2.16  CNF conversion       : 0.02
% 5.76/2.16  Main loop            : 1.09
% 5.76/2.16  Inferencing          : 0.30
% 5.76/2.16  Reduction            : 0.52
% 5.76/2.16  Demodulation         : 0.44
% 5.76/2.16  BG Simplification    : 0.04
% 5.76/2.16  Subsumption          : 0.17
% 5.76/2.16  Abstraction          : 0.06
% 5.76/2.16  MUC search           : 0.00
% 5.76/2.16  Cooper               : 0.00
% 5.76/2.16  Total                : 1.44
% 5.76/2.16  Index Insertion      : 0.00
% 5.76/2.16  Index Deletion       : 0.00
% 5.76/2.16  Index Matching       : 0.00
% 5.76/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

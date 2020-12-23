%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:55 EST 2020

% Result     : Theorem 11.84s
% Output     : CNFRefutation 11.84s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 290 expanded)
%              Number of leaves         :   38 ( 112 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 ( 471 expanded)
%              Number of equality atoms :   53 ( 146 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_98,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_104,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_56,plain,(
    ! [A_39] : ~ v1_xboole_0(k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_756,plain,(
    ! [B_101,A_102] :
      ( r2_hidden(B_101,A_102)
      | ~ m1_subset_1(B_101,A_102)
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [C_34,A_30] :
      ( r1_tarski(C_34,A_30)
      | ~ r2_hidden(C_34,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_760,plain,(
    ! [B_101,A_30] :
      ( r1_tarski(B_101,A_30)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_30))
      | v1_xboole_0(k1_zfmisc_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_756,c_34])).

tff(c_1167,plain,(
    ! [B_127,A_128] :
      ( r1_tarski(B_127,A_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_128)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_760])).

tff(c_1185,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1167])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1249,plain,(
    ! [A_129,B_130] :
      ( k4_xboole_0(A_129,B_130) = k3_subset_1(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1264,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1249])).

tff(c_1448,plain,(
    ! [A_134,B_135,C_136] :
      ( r1_tarski(A_134,k4_xboole_0(B_135,C_136))
      | ~ r1_xboole_0(A_134,C_136)
      | ~ r1_tarski(A_134,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16367,plain,(
    ! [A_396] :
      ( r1_tarski(A_396,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_396,'#skF_4')
      | ~ r1_tarski(A_396,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_1448])).

tff(c_62,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16412,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_16367,c_62])).

tff(c_16431,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_16412])).

tff(c_60,plain,(
    ! [A_42] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1265,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k3_subset_1(A_42,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60,c_1249])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_158,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(A_58,B_59) = B_59
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_213,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(resolution,[status(thm)],[c_22,c_158])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_226,plain,(
    ! [A_63] : k2_xboole_0(A_63,k1_xboole_0) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_2])).

tff(c_1072,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_tarski(k4_xboole_0(A_121,B_122),C_123)
      | ~ r1_tarski(A_121,k2_xboole_0(B_122,C_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_474,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(B_84,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_498,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_474])).

tff(c_1085,plain,(
    ! [A_121,B_122] :
      ( k4_xboole_0(A_121,B_122) = k1_xboole_0
      | ~ r1_tarski(A_121,k2_xboole_0(B_122,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1072,c_498])).

tff(c_2988,plain,(
    ! [A_192,B_193] :
      ( k4_xboole_0(A_192,B_193) = k1_xboole_0
      | ~ r1_tarski(A_192,B_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_1085])).

tff(c_3088,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1185,c_2988])).

tff(c_28,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3198,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3088,c_28])).

tff(c_3226,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_4,c_3198])).

tff(c_1266,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1249])).

tff(c_1355,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_28])).

tff(c_11142,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_1355])).

tff(c_1328,plain,(
    ! [A_131,B_132] :
      ( k3_subset_1(A_131,k3_subset_1(A_131,B_132)) = B_132
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1341,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_66,c_1328])).

tff(c_24,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1370,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_24])).

tff(c_36,plain,(
    ! [C_34,A_30] :
      ( r2_hidden(C_34,k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_861,plain,(
    ! [B_107,A_108] :
      ( m1_subset_1(B_107,A_108)
      | ~ r2_hidden(B_107,A_108)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_867,plain,(
    ! [C_34,A_30] :
      ( m1_subset_1(C_34,k1_zfmisc_1(A_30))
      | v1_xboole_0(k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(resolution,[status(thm)],[c_36,c_861])).

tff(c_2270,plain,(
    ! [C_162,A_163] :
      ( m1_subset_1(C_162,k1_zfmisc_1(A_163))
      | ~ r1_tarski(C_162,A_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_867])).

tff(c_54,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k3_subset_1(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28973,plain,(
    ! [A_534,C_535] :
      ( k4_xboole_0(A_534,C_535) = k3_subset_1(A_534,C_535)
      | ~ r1_tarski(C_535,A_534) ) ),
    inference(resolution,[status(thm)],[c_2270,c_54])).

tff(c_29231,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1370,c_28973])).

tff(c_29361,plain,(
    k3_subset_1('#skF_5',k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11142,c_1341,c_29231])).

tff(c_524,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k4_xboole_0(A_87,B_88)) = k3_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_324,plain,(
    ! [A_65,B_66] : k2_xboole_0(k4_xboole_0(A_65,B_66),A_65) = A_65 ),
    inference(resolution,[status(thm)],[c_24,c_158])).

tff(c_331,plain,(
    ! [B_66] : k4_xboole_0(k1_xboole_0,B_66) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_226])).

tff(c_571,plain,(
    ! [B_89] : k3_xboole_0(k1_xboole_0,B_89) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_331])).

tff(c_602,plain,(
    ! [B_90] : k3_xboole_0(B_90,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_4])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_610,plain,(
    ! [B_90] : k5_xboole_0(B_90,k1_xboole_0) = k4_xboole_0(B_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_12])).

tff(c_1392,plain,(
    ! [B_90] : k5_xboole_0(B_90,k1_xboole_0) = k3_subset_1(B_90,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_610])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3099,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2988])).

tff(c_64,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9293,plain,(
    ! [A_302] :
      ( r1_xboole_0(A_302,'#skF_5')
      | ~ r1_tarski(A_302,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_14])).

tff(c_9418,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_9293])).

tff(c_32,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(A_27,k4_xboole_0(B_28,C_29))
      | ~ r1_xboole_0(A_27,C_29)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5585,plain,(
    ! [A_222,B_223] :
      ( k4_xboole_0(A_222,B_223) = A_222
      | ~ r1_tarski(A_222,k4_xboole_0(A_222,B_223)) ) ),
    inference(resolution,[status(thm)],[c_24,c_474])).

tff(c_5640,plain,(
    ! [B_28,C_29] :
      ( k4_xboole_0(B_28,C_29) = B_28
      | ~ r1_xboole_0(B_28,C_29)
      | ~ r1_tarski(B_28,B_28) ) ),
    inference(resolution,[status(thm)],[c_32,c_5585])).

tff(c_5683,plain,(
    ! [B_28,C_29] :
      ( k4_xboole_0(B_28,C_29) = B_28
      | ~ r1_xboole_0(B_28,C_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5640])).

tff(c_9426,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9418,c_5683])).

tff(c_9492,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9426,c_28])).

tff(c_9520,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3099,c_9492])).

tff(c_459,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_471,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_459])).

tff(c_9579,plain,(
    k5_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9520,c_471])).

tff(c_9631,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k3_subset_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_9579])).

tff(c_638,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_xboole_0(A_91,C_92)
      | ~ r1_tarski(A_91,k4_xboole_0(B_93,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2417,plain,(
    ! [B_167,C_168,B_169] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_167,C_168),B_169),C_168) ),
    inference(resolution,[status(thm)],[c_24,c_638])).

tff(c_2430,plain,(
    ! [B_167,C_168] : r1_xboole_0(k3_subset_1(k4_xboole_0(B_167,C_168),k1_xboole_0),C_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_2417])).

tff(c_11405,plain,(
    r1_xboole_0(k3_subset_1(k3_subset_1('#skF_5',k1_xboole_0),k1_xboole_0),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9631,c_2430])).

tff(c_29486,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29361,c_29361,c_11405])).

tff(c_29504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16431,c_29486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:11:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.84/5.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.84/5.36  
% 11.84/5.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.84/5.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.84/5.36  
% 11.84/5.36  %Foreground sorts:
% 11.84/5.36  
% 11.84/5.36  
% 11.84/5.36  %Background operators:
% 11.84/5.36  
% 11.84/5.36  
% 11.84/5.36  %Foreground operators:
% 11.84/5.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.84/5.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.84/5.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.84/5.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.84/5.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.84/5.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.84/5.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.84/5.36  tff('#skF_5', type, '#skF_5': $i).
% 11.84/5.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.84/5.36  tff('#skF_3', type, '#skF_3': $i).
% 11.84/5.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.84/5.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.84/5.36  tff('#skF_4', type, '#skF_4': $i).
% 11.84/5.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.84/5.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.84/5.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.84/5.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.84/5.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.84/5.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.84/5.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.84/5.36  
% 11.84/5.38  tff(f_114, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 11.84/5.38  tff(f_98, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.84/5.38  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.84/5.38  tff(f_78, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.84/5.38  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.84/5.38  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 11.84/5.38  tff(f_104, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.84/5.38  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.84/5.38  tff(f_55, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.84/5.38  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.84/5.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.84/5.38  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.84/5.38  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.84/5.38  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.84/5.38  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.84/5.38  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.84/5.38  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.84/5.38  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 11.84/5.38  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.84/5.38  tff(c_56, plain, (![A_39]: (~v1_xboole_0(k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.84/5.38  tff(c_756, plain, (![B_101, A_102]: (r2_hidden(B_101, A_102) | ~m1_subset_1(B_101, A_102) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.84/5.38  tff(c_34, plain, (![C_34, A_30]: (r1_tarski(C_34, A_30) | ~r2_hidden(C_34, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.84/5.38  tff(c_760, plain, (![B_101, A_30]: (r1_tarski(B_101, A_30) | ~m1_subset_1(B_101, k1_zfmisc_1(A_30)) | v1_xboole_0(k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_756, c_34])).
% 11.84/5.38  tff(c_1167, plain, (![B_127, A_128]: (r1_tarski(B_127, A_128) | ~m1_subset_1(B_127, k1_zfmisc_1(A_128)))), inference(negUnitSimplification, [status(thm)], [c_56, c_760])).
% 11.84/5.38  tff(c_1185, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_1167])).
% 11.84/5.38  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.84/5.38  tff(c_1249, plain, (![A_129, B_130]: (k4_xboole_0(A_129, B_130)=k3_subset_1(A_129, B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.84/5.38  tff(c_1264, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_1249])).
% 11.84/5.38  tff(c_1448, plain, (![A_134, B_135, C_136]: (r1_tarski(A_134, k4_xboole_0(B_135, C_136)) | ~r1_xboole_0(A_134, C_136) | ~r1_tarski(A_134, B_135))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.84/5.38  tff(c_16367, plain, (![A_396]: (r1_tarski(A_396, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_396, '#skF_4') | ~r1_tarski(A_396, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_1448])).
% 11.84/5.38  tff(c_62, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.84/5.38  tff(c_16412, plain, (~r1_xboole_0('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_16367, c_62])).
% 11.84/5.38  tff(c_16431, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_16412])).
% 11.84/5.38  tff(c_60, plain, (![A_42]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.84/5.38  tff(c_1265, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k3_subset_1(A_42, k1_xboole_0))), inference(resolution, [status(thm)], [c_60, c_1249])).
% 11.84/5.38  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.84/5.38  tff(c_22, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.84/5.38  tff(c_158, plain, (![A_58, B_59]: (k2_xboole_0(A_58, B_59)=B_59 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.84/5.38  tff(c_213, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(resolution, [status(thm)], [c_22, c_158])).
% 11.84/5.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.84/5.38  tff(c_226, plain, (![A_63]: (k2_xboole_0(A_63, k1_xboole_0)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_213, c_2])).
% 11.84/5.38  tff(c_1072, plain, (![A_121, B_122, C_123]: (r1_tarski(k4_xboole_0(A_121, B_122), C_123) | ~r1_tarski(A_121, k2_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.84/5.38  tff(c_474, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(B_84, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.84/5.38  tff(c_498, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_474])).
% 11.84/5.38  tff(c_1085, plain, (![A_121, B_122]: (k4_xboole_0(A_121, B_122)=k1_xboole_0 | ~r1_tarski(A_121, k2_xboole_0(B_122, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1072, c_498])).
% 11.84/5.38  tff(c_2988, plain, (![A_192, B_193]: (k4_xboole_0(A_192, B_193)=k1_xboole_0 | ~r1_tarski(A_192, B_193))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_1085])).
% 11.84/5.38  tff(c_3088, plain, (k4_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1185, c_2988])).
% 11.84/5.38  tff(c_28, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.84/5.38  tff(c_3198, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3088, c_28])).
% 11.84/5.38  tff(c_3226, plain, (k3_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1265, c_4, c_3198])).
% 11.84/5.38  tff(c_1266, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_1249])).
% 11.84/5.38  tff(c_1355, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1266, c_28])).
% 11.84/5.38  tff(c_11142, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_1355])).
% 11.84/5.38  tff(c_1328, plain, (![A_131, B_132]: (k3_subset_1(A_131, k3_subset_1(A_131, B_132))=B_132 | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.84/5.38  tff(c_1341, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_66, c_1328])).
% 11.84/5.38  tff(c_24, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.84/5.38  tff(c_1370, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1266, c_24])).
% 11.84/5.38  tff(c_36, plain, (![C_34, A_30]: (r2_hidden(C_34, k1_zfmisc_1(A_30)) | ~r1_tarski(C_34, A_30))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.84/5.38  tff(c_861, plain, (![B_107, A_108]: (m1_subset_1(B_107, A_108) | ~r2_hidden(B_107, A_108) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.84/5.38  tff(c_867, plain, (![C_34, A_30]: (m1_subset_1(C_34, k1_zfmisc_1(A_30)) | v1_xboole_0(k1_zfmisc_1(A_30)) | ~r1_tarski(C_34, A_30))), inference(resolution, [status(thm)], [c_36, c_861])).
% 11.84/5.38  tff(c_2270, plain, (![C_162, A_163]: (m1_subset_1(C_162, k1_zfmisc_1(A_163)) | ~r1_tarski(C_162, A_163))), inference(negUnitSimplification, [status(thm)], [c_56, c_867])).
% 11.84/5.38  tff(c_54, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k3_subset_1(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.84/5.38  tff(c_28973, plain, (![A_534, C_535]: (k4_xboole_0(A_534, C_535)=k3_subset_1(A_534, C_535) | ~r1_tarski(C_535, A_534))), inference(resolution, [status(thm)], [c_2270, c_54])).
% 11.84/5.38  tff(c_29231, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_1370, c_28973])).
% 11.84/5.38  tff(c_29361, plain, (k3_subset_1('#skF_5', k1_xboole_0)='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_11142, c_1341, c_29231])).
% 11.84/5.38  tff(c_524, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k4_xboole_0(A_87, B_88))=k3_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.84/5.38  tff(c_324, plain, (![A_65, B_66]: (k2_xboole_0(k4_xboole_0(A_65, B_66), A_65)=A_65)), inference(resolution, [status(thm)], [c_24, c_158])).
% 11.84/5.38  tff(c_331, plain, (![B_66]: (k4_xboole_0(k1_xboole_0, B_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_324, c_226])).
% 11.84/5.38  tff(c_571, plain, (![B_89]: (k3_xboole_0(k1_xboole_0, B_89)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_524, c_331])).
% 11.84/5.38  tff(c_602, plain, (![B_90]: (k3_xboole_0(B_90, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_571, c_4])).
% 11.84/5.38  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.84/5.38  tff(c_610, plain, (![B_90]: (k5_xboole_0(B_90, k1_xboole_0)=k4_xboole_0(B_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_602, c_12])).
% 11.84/5.38  tff(c_1392, plain, (![B_90]: (k5_xboole_0(B_90, k1_xboole_0)=k3_subset_1(B_90, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1265, c_610])).
% 11.84/5.38  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.84/5.38  tff(c_3099, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2988])).
% 11.84/5.38  tff(c_64, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.84/5.38  tff(c_14, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_tarski(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.84/5.38  tff(c_9293, plain, (![A_302]: (r1_xboole_0(A_302, '#skF_5') | ~r1_tarski(A_302, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1266, c_14])).
% 11.84/5.38  tff(c_9418, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_9293])).
% 11.84/5.38  tff(c_32, plain, (![A_27, B_28, C_29]: (r1_tarski(A_27, k4_xboole_0(B_28, C_29)) | ~r1_xboole_0(A_27, C_29) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.84/5.38  tff(c_5585, plain, (![A_222, B_223]: (k4_xboole_0(A_222, B_223)=A_222 | ~r1_tarski(A_222, k4_xboole_0(A_222, B_223)))), inference(resolution, [status(thm)], [c_24, c_474])).
% 11.84/5.38  tff(c_5640, plain, (![B_28, C_29]: (k4_xboole_0(B_28, C_29)=B_28 | ~r1_xboole_0(B_28, C_29) | ~r1_tarski(B_28, B_28))), inference(resolution, [status(thm)], [c_32, c_5585])).
% 11.84/5.38  tff(c_5683, plain, (![B_28, C_29]: (k4_xboole_0(B_28, C_29)=B_28 | ~r1_xboole_0(B_28, C_29))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_5640])).
% 11.84/5.38  tff(c_9426, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_9418, c_5683])).
% 11.84/5.38  tff(c_9492, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9426, c_28])).
% 11.84/5.38  tff(c_9520, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3099, c_9492])).
% 11.84/5.38  tff(c_459, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.84/5.38  tff(c_471, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_459])).
% 11.84/5.38  tff(c_9579, plain, (k5_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9520, c_471])).
% 11.84/5.38  tff(c_9631, plain, (k4_xboole_0('#skF_5', '#skF_4')=k3_subset_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1392, c_9579])).
% 11.84/5.38  tff(c_638, plain, (![A_91, C_92, B_93]: (r1_xboole_0(A_91, C_92) | ~r1_tarski(A_91, k4_xboole_0(B_93, C_92)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.84/5.38  tff(c_2417, plain, (![B_167, C_168, B_169]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_167, C_168), B_169), C_168))), inference(resolution, [status(thm)], [c_24, c_638])).
% 11.84/5.38  tff(c_2430, plain, (![B_167, C_168]: (r1_xboole_0(k3_subset_1(k4_xboole_0(B_167, C_168), k1_xboole_0), C_168))), inference(superposition, [status(thm), theory('equality')], [c_1265, c_2417])).
% 11.84/5.38  tff(c_11405, plain, (r1_xboole_0(k3_subset_1(k3_subset_1('#skF_5', k1_xboole_0), k1_xboole_0), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9631, c_2430])).
% 11.84/5.38  tff(c_29486, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29361, c_29361, c_11405])).
% 11.84/5.38  tff(c_29504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16431, c_29486])).
% 11.84/5.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.84/5.38  
% 11.84/5.38  Inference rules
% 11.84/5.38  ----------------------
% 11.84/5.38  #Ref     : 0
% 11.84/5.38  #Sup     : 7063
% 11.84/5.38  #Fact    : 0
% 11.84/5.38  #Define  : 0
% 11.84/5.38  #Split   : 5
% 11.84/5.38  #Chain   : 0
% 11.84/5.38  #Close   : 0
% 11.84/5.38  
% 11.84/5.38  Ordering : KBO
% 11.84/5.38  
% 11.84/5.38  Simplification rules
% 11.84/5.38  ----------------------
% 11.84/5.38  #Subsume      : 510
% 11.84/5.38  #Demod        : 6056
% 11.84/5.38  #Tautology    : 3746
% 11.84/5.38  #SimpNegUnit  : 42
% 11.84/5.38  #BackRed      : 27
% 11.84/5.38  
% 11.84/5.38  #Partial instantiations: 0
% 11.84/5.38  #Strategies tried      : 1
% 11.84/5.38  
% 11.84/5.38  Timing (in seconds)
% 11.84/5.38  ----------------------
% 11.84/5.38  Preprocessing        : 0.33
% 11.84/5.38  Parsing              : 0.17
% 11.84/5.38  CNF conversion       : 0.02
% 11.84/5.38  Main loop            : 4.31
% 11.84/5.38  Inferencing          : 0.73
% 11.84/5.38  Reduction            : 2.25
% 11.84/5.38  Demodulation         : 1.91
% 11.84/5.38  BG Simplification    : 0.08
% 11.84/5.38  Subsumption          : 1.00
% 11.84/5.38  Abstraction          : 0.10
% 11.84/5.38  MUC search           : 0.00
% 11.84/5.38  Cooper               : 0.00
% 11.84/5.38  Total                : 4.67
% 11.84/5.38  Index Insertion      : 0.00
% 11.84/5.38  Index Deletion       : 0.00
% 11.84/5.38  Index Matching       : 0.00
% 11.84/5.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

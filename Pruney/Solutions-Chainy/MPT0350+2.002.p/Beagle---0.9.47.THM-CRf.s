%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:25 EST 2020

% Result     : Theorem 8.92s
% Output     : CNFRefutation 8.92s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 315 expanded)
%              Number of leaves         :   45 ( 124 expanded)
%              Depth                    :   16
%              Number of atoms          :  121 ( 414 expanded)
%              Number of equality atoms :   79 ( 224 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_90,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_64,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_52,plain,(
    ! [A_38] : k2_subset_1(A_38) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_62,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_225,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_245,plain,(
    ! [A_67] : k3_xboole_0(k1_xboole_0,A_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_225])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_253,plain,(
    ! [A_67] : k3_xboole_0(A_67,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_2])).

tff(c_524,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_533,plain,(
    ! [A_67] : k5_xboole_0(A_67,k1_xboole_0) = k4_xboole_0(A_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_524])).

tff(c_548,plain,(
    ! [A_67] : k4_xboole_0(A_67,k1_xboole_0) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_533])).

tff(c_595,plain,(
    ! [A_90,B_91] : k4_xboole_0(A_90,k4_xboole_0(A_90,B_91)) = k3_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_614,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k3_xboole_0(A_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_595])).

tff(c_625,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_614])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_545,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_524])).

tff(c_628,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_545])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    ! [A_43] : ~ v1_xboole_0(k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_680,plain,(
    ! [B_96,A_97] :
      ( r2_hidden(B_96,A_97)
      | ~ m1_subset_1(B_96,A_97)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [C_33,A_29] :
      ( r1_tarski(C_33,A_29)
      | ~ r2_hidden(C_33,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_687,plain,(
    ! [B_96,A_29] :
      ( r1_tarski(B_96,A_29)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_29))
      | v1_xboole_0(k1_zfmisc_1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_680,c_30])).

tff(c_692,plain,(
    ! [B_98,A_99] :
      ( r1_tarski(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_687])).

tff(c_705,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_692])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_718,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_705,c_14])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_722,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_8])).

tff(c_731,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_722])).

tff(c_24,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_230,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_376,plain,(
    ! [B_78,A_79] : k3_tarski(k2_tarski(B_78,A_79)) = k2_xboole_0(A_79,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_230])).

tff(c_42,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_399,plain,(
    ! [B_80,A_81] : k2_xboole_0(B_80,A_81) = k2_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_42])).

tff(c_149,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,A_58) = k3_xboole_0(A_58,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_164,plain,(
    ! [A_58,B_57] : k2_xboole_0(A_58,k3_xboole_0(B_57,A_58)) = A_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_12])).

tff(c_250,plain,(
    ! [A_67] : k2_xboole_0(A_67,k1_xboole_0) = A_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_164])).

tff(c_415,plain,(
    ! [A_81] : k2_xboole_0(k1_xboole_0,A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_250])).

tff(c_1018,plain,(
    ! [A_114,B_115] :
      ( k4_xboole_0(A_114,B_115) = k3_subset_1(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1035,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1018])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1044,plain,(
    k2_xboole_0(k4_xboole_0('#skF_4','#skF_3'),k3_subset_1('#skF_3','#skF_4')) = k5_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_4])).

tff(c_1051,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_731,c_1044])).

tff(c_542,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_524])).

tff(c_1097,plain,(
    ! [A_116,B_117,C_118] : k5_xboole_0(k3_xboole_0(A_116,B_117),k3_xboole_0(C_118,B_117)) = k3_xboole_0(k5_xboole_0(A_116,C_118),B_117) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1155,plain,(
    ! [A_5,C_118] : k5_xboole_0(A_5,k3_xboole_0(C_118,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_118),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1097])).

tff(c_1175,plain,(
    ! [A_119,C_120] : k3_xboole_0(A_119,k5_xboole_0(A_119,C_120)) = k4_xboole_0(A_119,C_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_2,c_1155])).

tff(c_1215,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_1175])).

tff(c_1245,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_1215])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1047,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_18])).

tff(c_1052,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_2,c_1047])).

tff(c_1063,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_18])).

tff(c_1066,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1035,c_1063])).

tff(c_1290,plain,(
    ! [A_122,C_123] : k2_xboole_0(A_122,k4_xboole_0(A_122,C_123)) = A_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_12])).

tff(c_1306,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_1290])).

tff(c_1405,plain,(
    k5_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1066,c_8])).

tff(c_1418,plain,(
    k5_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_1405])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(k5_xboole_0(A_20,B_21),k3_xboole_0(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1458,plain,(
    k5_xboole_0('#skF_4',k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4'))) = k2_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1418,c_22])).

tff(c_1462,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_1306,c_1458])).

tff(c_1518,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4'))) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1462,c_22])).

tff(c_1522,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1245,c_1518])).

tff(c_56,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k3_subset_1(A_41,B_42),k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2594,plain,(
    ! [A_161,B_162,C_163] :
      ( k4_subset_1(A_161,B_162,C_163) = k2_xboole_0(B_162,C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(A_161))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(A_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12606,plain,(
    ! [A_277,B_278,B_279] :
      ( k4_subset_1(A_277,B_278,k3_subset_1(A_277,B_279)) = k2_xboole_0(B_278,k3_subset_1(A_277,B_279))
      | ~ m1_subset_1(B_278,k1_zfmisc_1(A_277))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(A_277)) ) ),
    inference(resolution,[status(thm)],[c_56,c_2594])).

tff(c_12642,plain,(
    ! [B_280] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_280)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_280))
      | ~ m1_subset_1(B_280,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_12606])).

tff(c_12673,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_12642])).

tff(c_12689,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1522,c_12673])).

tff(c_12691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_12689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.92/3.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.92/3.51  
% 8.92/3.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.92/3.51  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.92/3.51  
% 8.92/3.51  %Foreground sorts:
% 8.92/3.51  
% 8.92/3.51  
% 8.92/3.51  %Background operators:
% 8.92/3.51  
% 8.92/3.51  
% 8.92/3.51  %Foreground operators:
% 8.92/3.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.92/3.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.92/3.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.92/3.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.92/3.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.92/3.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.92/3.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.92/3.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.92/3.51  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.92/3.51  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.92/3.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.92/3.51  tff('#skF_3', type, '#skF_3': $i).
% 8.92/3.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.92/3.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.92/3.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.92/3.51  tff('#skF_4', type, '#skF_4': $i).
% 8.92/3.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.92/3.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.92/3.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.92/3.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.92/3.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.92/3.51  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.92/3.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.92/3.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.92/3.51  
% 8.92/3.53  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 8.92/3.53  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 8.92/3.53  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.92/3.53  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.92/3.53  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.92/3.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.92/3.53  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.92/3.53  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.92/3.53  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.92/3.53  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.92/3.53  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 8.92/3.53  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.92/3.53  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.92/3.53  tff(f_64, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.92/3.53  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.92/3.53  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 8.92/3.53  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 8.92/3.53  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 8.92/3.53  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.92/3.53  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.92/3.53  tff(f_96, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.92/3.53  tff(c_52, plain, (![A_38]: (k2_subset_1(A_38)=A_38)), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.92/3.53  tff(c_62, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.92/3.53  tff(c_65, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62])).
% 8.92/3.53  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.92/3.53  tff(c_16, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.92/3.53  tff(c_225, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.92/3.53  tff(c_245, plain, (![A_67]: (k3_xboole_0(k1_xboole_0, A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_225])).
% 8.92/3.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.92/3.53  tff(c_253, plain, (![A_67]: (k3_xboole_0(A_67, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_245, c_2])).
% 8.92/3.53  tff(c_524, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.92/3.53  tff(c_533, plain, (![A_67]: (k5_xboole_0(A_67, k1_xboole_0)=k4_xboole_0(A_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_253, c_524])).
% 8.92/3.53  tff(c_548, plain, (![A_67]: (k4_xboole_0(A_67, k1_xboole_0)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_533])).
% 8.92/3.53  tff(c_595, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k4_xboole_0(A_90, B_91))=k3_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.92/3.53  tff(c_614, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k3_xboole_0(A_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_548, c_595])).
% 8.92/3.53  tff(c_625, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_253, c_614])).
% 8.92/3.53  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.92/3.53  tff(c_545, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_524])).
% 8.92/3.53  tff(c_628, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_625, c_545])).
% 8.92/3.53  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.92/3.53  tff(c_58, plain, (![A_43]: (~v1_xboole_0(k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.92/3.53  tff(c_680, plain, (![B_96, A_97]: (r2_hidden(B_96, A_97) | ~m1_subset_1(B_96, A_97) | v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.92/3.53  tff(c_30, plain, (![C_33, A_29]: (r1_tarski(C_33, A_29) | ~r2_hidden(C_33, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.92/3.53  tff(c_687, plain, (![B_96, A_29]: (r1_tarski(B_96, A_29) | ~m1_subset_1(B_96, k1_zfmisc_1(A_29)) | v1_xboole_0(k1_zfmisc_1(A_29)))), inference(resolution, [status(thm)], [c_680, c_30])).
% 8.92/3.53  tff(c_692, plain, (![B_98, A_99]: (r1_tarski(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)))), inference(negUnitSimplification, [status(thm)], [c_58, c_687])).
% 8.92/3.53  tff(c_705, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_692])).
% 8.92/3.53  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.92/3.53  tff(c_718, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_705, c_14])).
% 8.92/3.53  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.92/3.53  tff(c_722, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_718, c_8])).
% 8.92/3.53  tff(c_731, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_628, c_722])).
% 8.92/3.53  tff(c_24, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.92/3.53  tff(c_230, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.92/3.53  tff(c_376, plain, (![B_78, A_79]: (k3_tarski(k2_tarski(B_78, A_79))=k2_xboole_0(A_79, B_78))), inference(superposition, [status(thm), theory('equality')], [c_24, c_230])).
% 8.92/3.53  tff(c_42, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.92/3.53  tff(c_399, plain, (![B_80, A_81]: (k2_xboole_0(B_80, A_81)=k2_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_376, c_42])).
% 8.92/3.53  tff(c_149, plain, (![B_57, A_58]: (k3_xboole_0(B_57, A_58)=k3_xboole_0(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.92/3.53  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k3_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.92/3.53  tff(c_164, plain, (![A_58, B_57]: (k2_xboole_0(A_58, k3_xboole_0(B_57, A_58))=A_58)), inference(superposition, [status(thm), theory('equality')], [c_149, c_12])).
% 8.92/3.53  tff(c_250, plain, (![A_67]: (k2_xboole_0(A_67, k1_xboole_0)=A_67)), inference(superposition, [status(thm), theory('equality')], [c_245, c_164])).
% 8.92/3.53  tff(c_415, plain, (![A_81]: (k2_xboole_0(k1_xboole_0, A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_399, c_250])).
% 8.92/3.53  tff(c_1018, plain, (![A_114, B_115]: (k4_xboole_0(A_114, B_115)=k3_subset_1(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.92/3.53  tff(c_1035, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_1018])).
% 8.92/3.53  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.92/3.53  tff(c_1044, plain, (k2_xboole_0(k4_xboole_0('#skF_4', '#skF_3'), k3_subset_1('#skF_3', '#skF_4'))=k5_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1035, c_4])).
% 8.92/3.53  tff(c_1051, plain, (k5_xboole_0('#skF_4', '#skF_3')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_415, c_731, c_1044])).
% 8.92/3.53  tff(c_542, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_524])).
% 8.92/3.53  tff(c_1097, plain, (![A_116, B_117, C_118]: (k5_xboole_0(k3_xboole_0(A_116, B_117), k3_xboole_0(C_118, B_117))=k3_xboole_0(k5_xboole_0(A_116, C_118), B_117))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.92/3.53  tff(c_1155, plain, (![A_5, C_118]: (k5_xboole_0(A_5, k3_xboole_0(C_118, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_118), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1097])).
% 8.92/3.53  tff(c_1175, plain, (![A_119, C_120]: (k3_xboole_0(A_119, k5_xboole_0(A_119, C_120))=k4_xboole_0(A_119, C_120))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_2, c_1155])).
% 8.92/3.53  tff(c_1215, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1051, c_1175])).
% 8.92/3.53  tff(c_1245, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_731, c_1215])).
% 8.92/3.53  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.92/3.53  tff(c_1047, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1035, c_18])).
% 8.92/3.53  tff(c_1052, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_718, c_2, c_1047])).
% 8.92/3.53  tff(c_1063, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1052, c_18])).
% 8.92/3.53  tff(c_1066, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1035, c_1063])).
% 8.92/3.53  tff(c_1290, plain, (![A_122, C_123]: (k2_xboole_0(A_122, k4_xboole_0(A_122, C_123))=A_122)), inference(superposition, [status(thm), theory('equality')], [c_1175, c_12])).
% 8.92/3.53  tff(c_1306, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1035, c_1290])).
% 8.92/3.53  tff(c_1405, plain, (k5_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1066, c_8])).
% 8.92/3.53  tff(c_1418, plain, (k5_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_1405])).
% 8.92/3.53  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(k5_xboole_0(A_20, B_21), k3_xboole_0(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.92/3.53  tff(c_1458, plain, (k5_xboole_0('#skF_4', k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4')))=k2_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1418, c_22])).
% 8.92/3.53  tff(c_1462, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_1306, c_1458])).
% 8.92/3.53  tff(c_1518, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1462, c_22])).
% 8.92/3.53  tff(c_1522, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1245, c_1518])).
% 8.92/3.53  tff(c_56, plain, (![A_41, B_42]: (m1_subset_1(k3_subset_1(A_41, B_42), k1_zfmisc_1(A_41)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.92/3.53  tff(c_2594, plain, (![A_161, B_162, C_163]: (k4_subset_1(A_161, B_162, C_163)=k2_xboole_0(B_162, C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | ~m1_subset_1(B_162, k1_zfmisc_1(A_161)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.92/3.53  tff(c_12606, plain, (![A_277, B_278, B_279]: (k4_subset_1(A_277, B_278, k3_subset_1(A_277, B_279))=k2_xboole_0(B_278, k3_subset_1(A_277, B_279)) | ~m1_subset_1(B_278, k1_zfmisc_1(A_277)) | ~m1_subset_1(B_279, k1_zfmisc_1(A_277)))), inference(resolution, [status(thm)], [c_56, c_2594])).
% 8.92/3.53  tff(c_12642, plain, (![B_280]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_280))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_280)) | ~m1_subset_1(B_280, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_64, c_12606])).
% 8.92/3.53  tff(c_12673, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_12642])).
% 8.92/3.53  tff(c_12689, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1522, c_12673])).
% 8.92/3.53  tff(c_12691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_12689])).
% 8.92/3.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.92/3.53  
% 8.92/3.53  Inference rules
% 8.92/3.53  ----------------------
% 8.92/3.53  #Ref     : 0
% 8.92/3.53  #Sup     : 3132
% 8.92/3.53  #Fact    : 0
% 8.92/3.53  #Define  : 0
% 8.92/3.53  #Split   : 0
% 8.92/3.53  #Chain   : 0
% 8.92/3.53  #Close   : 0
% 8.92/3.53  
% 8.92/3.53  Ordering : KBO
% 8.92/3.53  
% 8.92/3.53  Simplification rules
% 8.92/3.53  ----------------------
% 8.92/3.53  #Subsume      : 43
% 8.92/3.53  #Demod        : 4891
% 8.92/3.53  #Tautology    : 1565
% 8.92/3.53  #SimpNegUnit  : 24
% 8.92/3.53  #BackRed      : 9
% 8.92/3.53  
% 8.92/3.53  #Partial instantiations: 0
% 8.92/3.53  #Strategies tried      : 1
% 8.92/3.53  
% 8.92/3.53  Timing (in seconds)
% 8.92/3.53  ----------------------
% 8.92/3.53  Preprocessing        : 0.35
% 8.92/3.53  Parsing              : 0.19
% 8.92/3.53  CNF conversion       : 0.02
% 8.92/3.53  Main loop            : 2.37
% 8.92/3.53  Inferencing          : 0.47
% 8.92/3.53  Reduction            : 1.40
% 8.92/3.53  Demodulation         : 1.24
% 8.92/3.53  BG Simplification    : 0.07
% 8.92/3.53  Subsumption          : 0.33
% 8.92/3.53  Abstraction          : 0.11
% 8.92/3.53  MUC search           : 0.00
% 8.92/3.53  Cooper               : 0.00
% 8.92/3.53  Total                : 2.76
% 8.92/3.53  Index Insertion      : 0.00
% 8.92/3.53  Index Deletion       : 0.00
% 8.92/3.53  Index Matching       : 0.00
% 8.92/3.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

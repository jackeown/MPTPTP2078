%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:34 EST 2020

% Result     : Theorem 11.81s
% Output     : CNFRefutation 11.95s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 259 expanded)
%              Number of leaves         :   43 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  116 ( 348 expanded)
%              Number of equality atoms :   71 ( 182 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_81,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_92,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_54,plain,(
    ! [A_35] : k2_subset_1(A_35) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_67,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_64])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1067,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(A_108,B_109) = k3_subset_1(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1080,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1067])).

tff(c_60,plain,(
    ! [A_40] : ~ v1_xboole_0(k1_zfmisc_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_374,plain,(
    ! [B_77,A_78] :
      ( r2_hidden(B_77,A_78)
      | ~ m1_subset_1(B_77,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [C_30,A_26] :
      ( r1_tarski(C_30,A_26)
      | ~ r2_hidden(C_30,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_378,plain,(
    ! [B_77,A_26] :
      ( r1_tarski(B_77,A_26)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_26))
      | v1_xboole_0(k1_zfmisc_1(A_26)) ) ),
    inference(resolution,[status(thm)],[c_374,c_32])).

tff(c_382,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(B_79,A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_378])).

tff(c_391,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_382])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_395,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_391,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1089,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_22])).

tff(c_1092,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_2,c_1089])).

tff(c_1100,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1092,c_22])).

tff(c_1103,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_1100])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1157,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_14])).

tff(c_28,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1086,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_28])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1151,plain,(
    k5_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_10])).

tff(c_1161,plain,(
    k5_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_1151])).

tff(c_26,plain,(
    ! [A_20,B_21] : k5_xboole_0(k5_xboole_0(A_20,B_21),k3_xboole_0(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1179,plain,(
    k5_xboole_0('#skF_4',k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4'))) = k2_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1161,c_26])).

tff(c_1182,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_1103,c_1179])).

tff(c_2817,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_1182])).

tff(c_24,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_99,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k2_xboole_0(A_51,B_52)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_18,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_192,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_225,plain,(
    ! [A_65] : k3_xboole_0(k1_xboole_0,A_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_257,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_407,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_419,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k4_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_407])).

tff(c_434,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_419])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_519,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_554,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_519])).

tff(c_563,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_554])).

tff(c_428,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_407])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_199,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_192])).

tff(c_1201,plain,(
    ! [A_112,B_113,C_114] : k5_xboole_0(k3_xboole_0(A_112,B_113),k3_xboole_0(C_114,B_113)) = k3_xboole_0(k5_xboole_0(A_112,C_114),B_113) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1259,plain,(
    ! [B_4,C_114] : k5_xboole_0(B_4,k3_xboole_0(C_114,B_4)) = k3_xboole_0(k5_xboole_0(B_4,C_114),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_1201])).

tff(c_1291,plain,(
    ! [B_115,C_116] : k3_xboole_0(B_115,k5_xboole_0(B_115,C_116)) = k4_xboole_0(B_115,C_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_2,c_1259])).

tff(c_1331,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_1291])).

tff(c_1370,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_1331])).

tff(c_1455,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1370,c_22])).

tff(c_1460,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1455])).

tff(c_1138,plain,(
    k5_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4'))) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_26])).

tff(c_1555,plain,(
    k5_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k1_xboole_0) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_1138])).

tff(c_1556,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1555])).

tff(c_2818,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2817,c_1556])).

tff(c_58,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k3_subset_1(A_38,B_39),k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2877,plain,(
    ! [A_145,B_146,C_147] :
      ( k4_subset_1(A_145,B_146,C_147) = k2_xboole_0(B_146,C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_25275,plain,(
    ! [A_342,B_343,B_344] :
      ( k4_subset_1(A_342,B_343,k3_subset_1(A_342,B_344)) = k2_xboole_0(B_343,k3_subset_1(A_342,B_344))
      | ~ m1_subset_1(B_343,k1_zfmisc_1(A_342))
      | ~ m1_subset_1(B_344,k1_zfmisc_1(A_342)) ) ),
    inference(resolution,[status(thm)],[c_58,c_2877])).

tff(c_25304,plain,(
    ! [B_345] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_345)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_345))
      | ~ m1_subset_1(B_345,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_66,c_25275])).

tff(c_25327,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_25304])).

tff(c_25339,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_25327])).

tff(c_25341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_25339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:54:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.81/4.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.95/4.72  
% 11.95/4.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.95/4.72  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.95/4.72  
% 11.95/4.72  %Foreground sorts:
% 11.95/4.72  
% 11.95/4.72  
% 11.95/4.72  %Background operators:
% 11.95/4.72  
% 11.95/4.72  
% 11.95/4.72  %Foreground operators:
% 11.95/4.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.95/4.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.95/4.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.95/4.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.95/4.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.95/4.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.95/4.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.95/4.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.95/4.72  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.95/4.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.95/4.72  tff('#skF_3', type, '#skF_3': $i).
% 11.95/4.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.95/4.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.95/4.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.95/4.72  tff('#skF_4', type, '#skF_4': $i).
% 11.95/4.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.95/4.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.95/4.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.95/4.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.95/4.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.95/4.72  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.95/4.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.95/4.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.95/4.72  
% 11.95/4.74  tff(f_81, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 11.95/4.74  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 11.95/4.74  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.95/4.74  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.95/4.74  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.95/4.74  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.95/4.74  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.95/4.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.95/4.74  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.95/4.74  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 11.95/4.74  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.95/4.74  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.95/4.74  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 11.95/4.74  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 11.95/4.74  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 11.95/4.74  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.95/4.74  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.95/4.74  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 11.95/4.74  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.95/4.74  tff(f_98, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.95/4.74  tff(c_54, plain, (![A_35]: (k2_subset_1(A_35)=A_35)), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.95/4.74  tff(c_64, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.95/4.74  tff(c_67, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_64])).
% 11.95/4.74  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.95/4.74  tff(c_1067, plain, (![A_108, B_109]: (k4_xboole_0(A_108, B_109)=k3_subset_1(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.95/4.74  tff(c_1080, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_1067])).
% 11.95/4.74  tff(c_60, plain, (![A_40]: (~v1_xboole_0(k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.95/4.74  tff(c_374, plain, (![B_77, A_78]: (r2_hidden(B_77, A_78) | ~m1_subset_1(B_77, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.95/4.74  tff(c_32, plain, (![C_30, A_26]: (r1_tarski(C_30, A_26) | ~r2_hidden(C_30, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.95/4.74  tff(c_378, plain, (![B_77, A_26]: (r1_tarski(B_77, A_26) | ~m1_subset_1(B_77, k1_zfmisc_1(A_26)) | v1_xboole_0(k1_zfmisc_1(A_26)))), inference(resolution, [status(thm)], [c_374, c_32])).
% 11.95/4.74  tff(c_382, plain, (![B_79, A_80]: (r1_tarski(B_79, A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)))), inference(negUnitSimplification, [status(thm)], [c_60, c_378])).
% 11.95/4.74  tff(c_391, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_382])).
% 11.95/4.74  tff(c_16, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.95/4.74  tff(c_395, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_391, c_16])).
% 11.95/4.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.95/4.74  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.95/4.74  tff(c_1089, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1080, c_22])).
% 11.95/4.74  tff(c_1092, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_395, c_2, c_1089])).
% 11.95/4.74  tff(c_1100, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1092, c_22])).
% 11.95/4.74  tff(c_1103, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_1100])).
% 11.95/4.74  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k3_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.95/4.74  tff(c_1157, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1103, c_14])).
% 11.95/4.74  tff(c_28, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.95/4.74  tff(c_1086, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1080, c_28])).
% 11.95/4.74  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.95/4.74  tff(c_1151, plain, (k5_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_10])).
% 11.95/4.74  tff(c_1161, plain, (k5_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_1151])).
% 11.95/4.74  tff(c_26, plain, (![A_20, B_21]: (k5_xboole_0(k5_xboole_0(A_20, B_21), k3_xboole_0(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.95/4.74  tff(c_1179, plain, (k5_xboole_0('#skF_4', k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4')))=k2_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1161, c_26])).
% 11.95/4.74  tff(c_1182, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1086, c_1103, c_1179])).
% 11.95/4.74  tff(c_2817, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1157, c_1182])).
% 11.95/4.74  tff(c_24, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.95/4.74  tff(c_99, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k2_xboole_0(A_51, B_52))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.95/4.74  tff(c_106, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_99])).
% 11.95/4.74  tff(c_18, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.95/4.74  tff(c_192, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.95/4.74  tff(c_225, plain, (![A_65]: (k3_xboole_0(k1_xboole_0, A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_192])).
% 11.95/4.74  tff(c_257, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_225])).
% 11.95/4.74  tff(c_407, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.95/4.74  tff(c_419, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k4_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_257, c_407])).
% 11.95/4.74  tff(c_434, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_419])).
% 11.95/4.74  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.95/4.74  tff(c_519, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.95/4.74  tff(c_554, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k4_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_519])).
% 11.95/4.74  tff(c_563, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_434, c_554])).
% 11.95/4.74  tff(c_428, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_407])).
% 11.95/4.74  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.95/4.74  tff(c_199, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_192])).
% 11.95/4.74  tff(c_1201, plain, (![A_112, B_113, C_114]: (k5_xboole_0(k3_xboole_0(A_112, B_113), k3_xboole_0(C_114, B_113))=k3_xboole_0(k5_xboole_0(A_112, C_114), B_113))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.95/4.74  tff(c_1259, plain, (![B_4, C_114]: (k5_xboole_0(B_4, k3_xboole_0(C_114, B_4))=k3_xboole_0(k5_xboole_0(B_4, C_114), B_4))), inference(superposition, [status(thm), theory('equality')], [c_199, c_1201])).
% 11.95/4.74  tff(c_1291, plain, (![B_115, C_116]: (k3_xboole_0(B_115, k5_xboole_0(B_115, C_116))=k4_xboole_0(B_115, C_116))), inference(demodulation, [status(thm), theory('equality')], [c_428, c_2, c_1259])).
% 11.95/4.74  tff(c_1331, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1086, c_1291])).
% 11.95/4.74  tff(c_1370, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_563, c_1331])).
% 11.95/4.74  tff(c_1455, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1370, c_22])).
% 11.95/4.74  tff(c_1460, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1455])).
% 11.95/4.74  tff(c_1138, plain, (k5_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1086, c_26])).
% 11.95/4.74  tff(c_1555, plain, (k5_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k1_xboole_0)=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1460, c_1138])).
% 11.95/4.74  tff(c_1556, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1555])).
% 11.95/4.74  tff(c_2818, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2817, c_1556])).
% 11.95/4.74  tff(c_58, plain, (![A_38, B_39]: (m1_subset_1(k3_subset_1(A_38, B_39), k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.95/4.74  tff(c_2877, plain, (![A_145, B_146, C_147]: (k4_subset_1(A_145, B_146, C_147)=k2_xboole_0(B_146, C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(A_145)) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.95/4.74  tff(c_25275, plain, (![A_342, B_343, B_344]: (k4_subset_1(A_342, B_343, k3_subset_1(A_342, B_344))=k2_xboole_0(B_343, k3_subset_1(A_342, B_344)) | ~m1_subset_1(B_343, k1_zfmisc_1(A_342)) | ~m1_subset_1(B_344, k1_zfmisc_1(A_342)))), inference(resolution, [status(thm)], [c_58, c_2877])).
% 11.95/4.74  tff(c_25304, plain, (![B_345]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_345))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_345)) | ~m1_subset_1(B_345, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_66, c_25275])).
% 11.95/4.74  tff(c_25327, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_25304])).
% 11.95/4.74  tff(c_25339, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2818, c_25327])).
% 11.95/4.74  tff(c_25341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_25339])).
% 11.95/4.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.95/4.74  
% 11.95/4.74  Inference rules
% 11.95/4.74  ----------------------
% 11.95/4.74  #Ref     : 0
% 11.95/4.74  #Sup     : 6383
% 11.95/4.74  #Fact    : 0
% 11.95/4.74  #Define  : 0
% 11.95/4.74  #Split   : 2
% 11.95/4.74  #Chain   : 0
% 11.95/4.74  #Close   : 0
% 11.95/4.74  
% 11.95/4.74  Ordering : KBO
% 11.95/4.74  
% 11.95/4.74  Simplification rules
% 11.95/4.74  ----------------------
% 11.95/4.74  #Subsume      : 78
% 11.95/4.74  #Demod        : 8830
% 11.95/4.74  #Tautology    : 4368
% 11.95/4.74  #SimpNegUnit  : 31
% 11.95/4.74  #BackRed      : 102
% 11.95/4.74  
% 11.95/4.74  #Partial instantiations: 0
% 11.95/4.74  #Strategies tried      : 1
% 11.95/4.74  
% 11.95/4.74  Timing (in seconds)
% 11.95/4.74  ----------------------
% 11.95/4.74  Preprocessing        : 0.34
% 11.95/4.74  Parsing              : 0.18
% 11.95/4.74  CNF conversion       : 0.02
% 11.95/4.74  Main loop            : 3.62
% 11.95/4.74  Inferencing          : 0.68
% 11.95/4.74  Reduction            : 2.10
% 11.95/4.74  Demodulation         : 1.85
% 11.95/4.75  BG Simplification    : 0.09
% 11.95/4.75  Subsumption          : 0.56
% 11.95/4.75  Abstraction          : 0.14
% 11.95/4.75  MUC search           : 0.00
% 11.95/4.75  Cooper               : 0.00
% 11.95/4.75  Total                : 4.00
% 11.95/4.75  Index Insertion      : 0.00
% 11.95/4.75  Index Deletion       : 0.00
% 11.95/4.75  Index Matching       : 0.00
% 11.95/4.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:55:33 EST 2020

% Result     : Theorem 13.02s
% Output     : CNFRefutation 13.02s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 249 expanded)
%              Number of leaves         :   43 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 291 expanded)
%              Number of equality atoms :   71 ( 191 expanded)
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

tff(f_77,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_88,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_50,plain,(
    ! [A_38] : k2_subset_1(A_38) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60])).

tff(c_99,plain,(
    ! [B_53,A_54] : k5_xboole_0(B_53,A_54) = k5_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_115,plain,(
    ! [A_54] : k5_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_18])).

tff(c_22,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_851,plain,(
    ! [A_105,B_106,C_107] : k5_xboole_0(k5_xboole_0(A_105,B_106),C_107) = k5_xboole_0(A_105,k5_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3145,plain,(
    ! [B_156,A_157,B_158] : k5_xboole_0(B_156,k5_xboole_0(A_157,B_158)) = k5_xboole_0(A_157,k5_xboole_0(B_158,B_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_851])).

tff(c_3599,plain,(
    ! [A_159,B_160] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_159,B_160)) = k5_xboole_0(B_160,A_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_3145])).

tff(c_3737,plain,(
    ! [B_23,A_22] : k5_xboole_0(k4_xboole_0(B_23,A_22),A_22) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3599])).

tff(c_3790,plain,(
    ! [B_23,A_22] : k5_xboole_0(k4_xboole_0(B_23,A_22),A_22) = k2_xboole_0(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_3737])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_380,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_396,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_380])).

tff(c_3728,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_3599])).

tff(c_3787,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_3728])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18370,plain,(
    ! [A_290,B_291,C_292] : k5_xboole_0(A_290,k5_xboole_0(k3_xboole_0(A_290,B_291),C_292)) = k5_xboole_0(k4_xboole_0(A_290,B_291),C_292) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_851])).

tff(c_18616,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_18370])).

tff(c_18804,plain,(
    ! [B_293,A_294] : k2_xboole_0(B_293,A_294) = k2_xboole_0(A_294,B_293) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3790,c_22,c_18616])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_799,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = k3_subset_1(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_812,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_799])).

tff(c_56,plain,(
    ! [A_43] : ~ v1_xboole_0(k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_516,plain,(
    ! [B_88,A_89] :
      ( r2_hidden(B_88,A_89)
      | ~ m1_subset_1(B_88,A_89)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [C_33,A_29] :
      ( r1_tarski(C_33,A_29)
      | ~ r2_hidden(C_33,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_523,plain,(
    ! [B_88,A_29] :
      ( r1_tarski(B_88,A_29)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_29))
      | v1_xboole_0(k1_zfmisc_1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_516,c_28])).

tff(c_533,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(B_92,A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_523])).

tff(c_546,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_533])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_550,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_546,c_14])).

tff(c_583,plain,(
    ! [B_94,A_95] : k5_xboole_0(B_94,k3_xboole_0(A_95,B_94)) = k4_xboole_0(B_94,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_380])).

tff(c_600,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_583])).

tff(c_814,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_600])).

tff(c_186,plain,(
    ! [A_56,B_57] : k2_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_192,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_16])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_403,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_380])).

tff(c_406,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_403])).

tff(c_908,plain,(
    ! [A_5,C_107] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_107)) = k5_xboole_0(k1_xboole_0,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_851])).

tff(c_956,plain,(
    ! [A_5,C_107] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_107)) = C_107 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_908])).

tff(c_960,plain,(
    ! [A_108,C_109] : k5_xboole_0(A_108,k5_xboole_0(A_108,C_109)) = C_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_908])).

tff(c_1040,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k5_xboole_0(B_111,A_110)) = B_111 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_960])).

tff(c_1262,plain,(
    ! [A_114,C_115] : k5_xboole_0(k5_xboole_0(A_114,C_115),C_115) = A_114 ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_1040])).

tff(c_1335,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_1262])).

tff(c_1093,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_1040])).

tff(c_1577,plain,(
    ! [A_118,B_119,C_120] : k5_xboole_0(k3_xboole_0(A_118,B_119),k3_xboole_0(C_120,B_119)) = k3_xboole_0(k5_xboole_0(A_118,C_120),B_119) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1659,plain,(
    ! [A_5,C_120] : k5_xboole_0(A_5,k3_xboole_0(C_120,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_120),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1577])).

tff(c_2111,plain,(
    ! [A_134,C_135] : k3_xboole_0(A_134,k5_xboole_0(A_134,C_135)) = k4_xboole_0(A_134,C_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_2,c_1659])).

tff(c_2155,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_2111])).

tff(c_2212,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_2155])).

tff(c_2318,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2212,c_22])).

tff(c_2322,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1335,c_2318])).

tff(c_18951,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_18804,c_2322])).

tff(c_54,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k3_subset_1(A_41,B_42),k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2359,plain,(
    ! [A_140,B_141,C_142] :
      ( k4_subset_1(A_140,B_141,C_142) = k2_xboole_0(B_141,C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(A_140))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_33872,plain,(
    ! [A_392,B_393,B_394] :
      ( k4_subset_1(A_392,B_393,k3_subset_1(A_392,B_394)) = k2_xboole_0(B_393,k3_subset_1(A_392,B_394))
      | ~ m1_subset_1(B_393,k1_zfmisc_1(A_392))
      | ~ m1_subset_1(B_394,k1_zfmisc_1(A_392)) ) ),
    inference(resolution,[status(thm)],[c_54,c_2359])).

tff(c_33901,plain,(
    ! [B_395] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_395)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_395))
      | ~ m1_subset_1(B_395,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_33872])).

tff(c_33924,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_33901])).

tff(c_33936,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18951,c_33924])).

tff(c_33938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_33936])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:27:45 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.02/6.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.02/6.23  
% 13.02/6.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.02/6.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 13.02/6.23  
% 13.02/6.23  %Foreground sorts:
% 13.02/6.23  
% 13.02/6.23  
% 13.02/6.23  %Background operators:
% 13.02/6.23  
% 13.02/6.23  
% 13.02/6.23  %Foreground operators:
% 13.02/6.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.02/6.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.02/6.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.02/6.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.02/6.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.02/6.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.02/6.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.02/6.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.02/6.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.02/6.23  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.02/6.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.02/6.23  tff('#skF_3', type, '#skF_3': $i).
% 13.02/6.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.02/6.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.02/6.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.02/6.23  tff('#skF_4', type, '#skF_4': $i).
% 13.02/6.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.02/6.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.02/6.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.02/6.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.02/6.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.02/6.23  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 13.02/6.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.02/6.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.02/6.23  
% 13.02/6.25  tff(f_77, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 13.02/6.25  tff(f_99, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 13.02/6.25  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.02/6.25  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.02/6.25  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 13.02/6.25  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.02/6.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.02/6.25  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.02/6.25  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 13.02/6.25  tff(f_88, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 13.02/6.25  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 13.02/6.25  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 13.02/6.25  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.02/6.25  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 13.02/6.25  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 13.02/6.25  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 13.02/6.25  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 13.02/6.25  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 13.02/6.25  tff(f_94, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 13.02/6.25  tff(c_50, plain, (![A_38]: (k2_subset_1(A_38)=A_38)), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.02/6.25  tff(c_60, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.02/6.25  tff(c_63, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60])).
% 13.02/6.25  tff(c_99, plain, (![B_53, A_54]: (k5_xboole_0(B_53, A_54)=k5_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.02/6.25  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.02/6.25  tff(c_115, plain, (![A_54]: (k5_xboole_0(k1_xboole_0, A_54)=A_54)), inference(superposition, [status(thm), theory('equality')], [c_99, c_18])).
% 13.02/6.25  tff(c_22, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.02/6.25  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.02/6.25  tff(c_851, plain, (![A_105, B_106, C_107]: (k5_xboole_0(k5_xboole_0(A_105, B_106), C_107)=k5_xboole_0(A_105, k5_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.02/6.25  tff(c_3145, plain, (![B_156, A_157, B_158]: (k5_xboole_0(B_156, k5_xboole_0(A_157, B_158))=k5_xboole_0(A_157, k5_xboole_0(B_158, B_156)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_851])).
% 13.02/6.25  tff(c_3599, plain, (![A_159, B_160]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_159, B_160))=k5_xboole_0(B_160, A_159))), inference(superposition, [status(thm), theory('equality')], [c_115, c_3145])).
% 13.02/6.25  tff(c_3737, plain, (![B_23, A_22]: (k5_xboole_0(k4_xboole_0(B_23, A_22), A_22)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3599])).
% 13.02/6.25  tff(c_3790, plain, (![B_23, A_22]: (k5_xboole_0(k4_xboole_0(B_23, A_22), A_22)=k2_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_3737])).
% 13.02/6.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.02/6.25  tff(c_380, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.02/6.25  tff(c_396, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_380])).
% 13.02/6.25  tff(c_3728, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_396, c_3599])).
% 13.02/6.25  tff(c_3787, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_3728])).
% 13.02/6.25  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.02/6.25  tff(c_18370, plain, (![A_290, B_291, C_292]: (k5_xboole_0(A_290, k5_xboole_0(k3_xboole_0(A_290, B_291), C_292))=k5_xboole_0(k4_xboole_0(A_290, B_291), C_292))), inference(superposition, [status(thm), theory('equality')], [c_8, c_851])).
% 13.02/6.25  tff(c_18616, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_18370])).
% 13.02/6.25  tff(c_18804, plain, (![B_293, A_294]: (k2_xboole_0(B_293, A_294)=k2_xboole_0(A_294, B_293))), inference(demodulation, [status(thm), theory('equality')], [c_3790, c_22, c_18616])).
% 13.02/6.25  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.02/6.25  tff(c_799, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=k3_subset_1(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.02/6.25  tff(c_812, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_799])).
% 13.02/6.25  tff(c_56, plain, (![A_43]: (~v1_xboole_0(k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.02/6.25  tff(c_516, plain, (![B_88, A_89]: (r2_hidden(B_88, A_89) | ~m1_subset_1(B_88, A_89) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.02/6.25  tff(c_28, plain, (![C_33, A_29]: (r1_tarski(C_33, A_29) | ~r2_hidden(C_33, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.02/6.25  tff(c_523, plain, (![B_88, A_29]: (r1_tarski(B_88, A_29) | ~m1_subset_1(B_88, k1_zfmisc_1(A_29)) | v1_xboole_0(k1_zfmisc_1(A_29)))), inference(resolution, [status(thm)], [c_516, c_28])).
% 13.02/6.25  tff(c_533, plain, (![B_92, A_93]: (r1_tarski(B_92, A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)))), inference(negUnitSimplification, [status(thm)], [c_56, c_523])).
% 13.02/6.25  tff(c_546, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_533])).
% 13.02/6.25  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.02/6.25  tff(c_550, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_546, c_14])).
% 13.02/6.25  tff(c_583, plain, (![B_94, A_95]: (k5_xboole_0(B_94, k3_xboole_0(A_95, B_94))=k4_xboole_0(B_94, A_95))), inference(superposition, [status(thm), theory('equality')], [c_2, c_380])).
% 13.02/6.25  tff(c_600, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_550, c_583])).
% 13.02/6.25  tff(c_814, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_812, c_600])).
% 13.02/6.25  tff(c_186, plain, (![A_56, B_57]: (k2_xboole_0(A_56, k3_xboole_0(A_56, B_57))=A_56)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.02/6.25  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.02/6.25  tff(c_192, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_186, c_16])).
% 13.02/6.25  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.02/6.25  tff(c_403, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_380])).
% 13.02/6.25  tff(c_406, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_403])).
% 13.02/6.25  tff(c_908, plain, (![A_5, C_107]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_107))=k5_xboole_0(k1_xboole_0, C_107))), inference(superposition, [status(thm), theory('equality')], [c_406, c_851])).
% 13.02/6.25  tff(c_956, plain, (![A_5, C_107]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_107))=C_107)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_908])).
% 13.02/6.25  tff(c_960, plain, (![A_108, C_109]: (k5_xboole_0(A_108, k5_xboole_0(A_108, C_109))=C_109)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_908])).
% 13.02/6.25  tff(c_1040, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k5_xboole_0(B_111, A_110))=B_111)), inference(superposition, [status(thm), theory('equality')], [c_4, c_960])).
% 13.02/6.25  tff(c_1262, plain, (![A_114, C_115]: (k5_xboole_0(k5_xboole_0(A_114, C_115), C_115)=A_114)), inference(superposition, [status(thm), theory('equality')], [c_956, c_1040])).
% 13.02/6.25  tff(c_1335, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_814, c_1262])).
% 13.02/6.25  tff(c_1093, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_814, c_1040])).
% 13.02/6.25  tff(c_1577, plain, (![A_118, B_119, C_120]: (k5_xboole_0(k3_xboole_0(A_118, B_119), k3_xboole_0(C_120, B_119))=k3_xboole_0(k5_xboole_0(A_118, C_120), B_119))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.02/6.25  tff(c_1659, plain, (![A_5, C_120]: (k5_xboole_0(A_5, k3_xboole_0(C_120, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_120), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1577])).
% 13.02/6.25  tff(c_2111, plain, (![A_134, C_135]: (k3_xboole_0(A_134, k5_xboole_0(A_134, C_135))=k4_xboole_0(A_134, C_135))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_2, c_1659])).
% 13.02/6.25  tff(c_2155, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1093, c_2111])).
% 13.02/6.25  tff(c_2212, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_550, c_2155])).
% 13.02/6.25  tff(c_2318, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2212, c_22])).
% 13.02/6.25  tff(c_2322, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1335, c_2318])).
% 13.02/6.25  tff(c_18951, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_18804, c_2322])).
% 13.02/6.25  tff(c_54, plain, (![A_41, B_42]: (m1_subset_1(k3_subset_1(A_41, B_42), k1_zfmisc_1(A_41)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.02/6.25  tff(c_2359, plain, (![A_140, B_141, C_142]: (k4_subset_1(A_140, B_141, C_142)=k2_xboole_0(B_141, C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(A_140)) | ~m1_subset_1(B_141, k1_zfmisc_1(A_140)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.02/6.25  tff(c_33872, plain, (![A_392, B_393, B_394]: (k4_subset_1(A_392, B_393, k3_subset_1(A_392, B_394))=k2_xboole_0(B_393, k3_subset_1(A_392, B_394)) | ~m1_subset_1(B_393, k1_zfmisc_1(A_392)) | ~m1_subset_1(B_394, k1_zfmisc_1(A_392)))), inference(resolution, [status(thm)], [c_54, c_2359])).
% 13.02/6.25  tff(c_33901, plain, (![B_395]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_395))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_395)) | ~m1_subset_1(B_395, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_33872])).
% 13.02/6.25  tff(c_33924, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_33901])).
% 13.02/6.25  tff(c_33936, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18951, c_33924])).
% 13.02/6.25  tff(c_33938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_33936])).
% 13.02/6.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.02/6.25  
% 13.02/6.25  Inference rules
% 13.02/6.25  ----------------------
% 13.02/6.25  #Ref     : 0
% 13.02/6.25  #Sup     : 8626
% 13.02/6.25  #Fact    : 0
% 13.02/6.25  #Define  : 0
% 13.02/6.25  #Split   : 0
% 13.02/6.25  #Chain   : 0
% 13.02/6.25  #Close   : 0
% 13.02/6.25  
% 13.02/6.25  Ordering : KBO
% 13.02/6.25  
% 13.02/6.25  Simplification rules
% 13.02/6.25  ----------------------
% 13.02/6.25  #Subsume      : 139
% 13.02/6.25  #Demod        : 10665
% 13.02/6.25  #Tautology    : 4805
% 13.02/6.25  #SimpNegUnit  : 22
% 13.02/6.25  #BackRed      : 12
% 13.02/6.25  
% 13.02/6.25  #Partial instantiations: 0
% 13.02/6.25  #Strategies tried      : 1
% 13.02/6.25  
% 13.02/6.25  Timing (in seconds)
% 13.02/6.25  ----------------------
% 13.02/6.25  Preprocessing        : 0.35
% 13.02/6.25  Parsing              : 0.19
% 13.02/6.25  CNF conversion       : 0.02
% 13.02/6.25  Main loop            : 5.13
% 13.02/6.25  Inferencing          : 0.78
% 13.02/6.25  Reduction            : 3.23
% 13.02/6.25  Demodulation         : 2.93
% 13.02/6.25  BG Simplification    : 0.11
% 13.02/6.25  Subsumption          : 0.80
% 13.02/6.25  Abstraction          : 0.20
% 13.02/6.25  MUC search           : 0.00
% 13.02/6.25  Cooper               : 0.00
% 13.02/6.25  Total                : 5.51
% 13.02/6.25  Index Insertion      : 0.00
% 13.02/6.25  Index Deletion       : 0.00
% 13.02/6.25  Index Matching       : 0.00
% 13.02/6.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

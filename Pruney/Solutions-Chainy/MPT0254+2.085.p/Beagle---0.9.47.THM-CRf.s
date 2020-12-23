%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:30 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :  111 (2083 expanded)
%              Number of leaves         :   45 ( 732 expanded)
%              Depth                    :   18
%              Number of atoms          :   96 (2144 expanded)
%              Number of equality atoms :   67 (1963 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_96,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_95,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_26,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_468,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_493,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_468])).

tff(c_30,plain,(
    ! [A_23,B_24,C_25] : k5_xboole_0(k5_xboole_0(A_23,B_24),C_25) = k5_xboole_0(A_23,k5_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_961,plain,(
    ! [A_124,B_125] : k5_xboole_0(k5_xboole_0(A_124,B_125),k3_xboole_0(A_124,B_125)) = k2_xboole_0(A_124,B_125) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1004,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k5_xboole_0(B_24,k3_xboole_0(A_23,B_24))) = k2_xboole_0(A_23,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_961])).

tff(c_1496,plain,(
    ! [A_153,B_154] : k5_xboole_0(A_153,k4_xboole_0(B_154,A_153)) = k2_xboole_0(A_153,B_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_1004])).

tff(c_130,plain,(
    ! [B_73,A_74] : k5_xboole_0(B_73,A_74) = k5_xboole_0(A_74,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_146,plain,(
    ! [A_74] : k5_xboole_0(k1_xboole_0,A_74) = A_74 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_26])).

tff(c_32,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_721,plain,(
    ! [A_117,B_118,C_119] : k5_xboole_0(k5_xboole_0(A_117,B_118),C_119) = k5_xboole_0(A_117,k5_xboole_0(B_118,C_119)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_796,plain,(
    ! [A_26,C_119] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_119)) = k5_xboole_0(k1_xboole_0,C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_721])).

tff(c_809,plain,(
    ! [A_26,C_119] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_119)) = C_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_796])).

tff(c_1840,plain,(
    ! [A_168,B_169] : k5_xboole_0(A_168,k2_xboole_0(A_168,B_169)) = k4_xboole_0(B_169,A_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_809])).

tff(c_1895,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1840])).

tff(c_1907,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1895])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_810,plain,(
    ! [A_120,C_121] : k5_xboole_0(A_120,k5_xboole_0(A_120,C_121)) = C_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_796])).

tff(c_856,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_810])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_281,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_291,plain,(
    ! [A_19,B_20] : k3_xboole_0(k4_xboole_0(A_19,B_20),A_19) = k4_xboole_0(A_19,B_20) ),
    inference(resolution,[status(thm)],[c_24,c_281])).

tff(c_1010,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_19,B_20),A_19),k4_xboole_0(A_19,B_20)) = k2_xboole_0(k4_xboole_0(A_19,B_20),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_961])).

tff(c_1056,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_4,c_4,c_1010])).

tff(c_1963,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1907,c_1056])).

tff(c_1995,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_68])).

tff(c_572,plain,(
    ! [A_111,B_112] : k3_xboole_0(k4_xboole_0(A_111,B_112),A_111) = k4_xboole_0(A_111,B_112) ),
    inference(resolution,[status(thm)],[c_24,c_281])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_578,plain,(
    ! [A_111,B_112] : k5_xboole_0(k4_xboole_0(A_111,B_112),k4_xboole_0(A_111,B_112)) = k4_xboole_0(k4_xboole_0(A_111,B_112),A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_18])).

tff(c_617,plain,(
    ! [A_111,B_112] : k4_xboole_0(k4_xboole_0(A_111,B_112),A_111) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_578])).

tff(c_1966,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1907,c_617])).

tff(c_2083,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_1966])).

tff(c_1535,plain,(
    ! [A_111,B_112] : k2_xboole_0(A_111,k4_xboole_0(A_111,B_112)) = k5_xboole_0(A_111,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_1496])).

tff(c_1552,plain,(
    ! [A_111,B_112] : k2_xboole_0(A_111,k4_xboole_0(A_111,B_112)) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1535])).

tff(c_2096,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_1552])).

tff(c_2113,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_2096])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_378,plain,(
    ! [A_89,B_90] : k3_tarski(k2_tarski(A_89,B_90)) = k2_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_387,plain,(
    ! [A_29] : k3_tarski(k1_tarski(A_29)) = k2_xboole_0(A_29,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_378])).

tff(c_390,plain,(
    ! [A_29] : k3_tarski(k1_tarski(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_387])).

tff(c_2131,plain,(
    k3_tarski('#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2113,c_390])).

tff(c_66,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2023,plain,(
    k3_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_1995,c_66])).

tff(c_2136,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2131,c_2023])).

tff(c_22,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2021,plain,(
    ! [A_18] : r1_tarski('#skF_5',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_22])).

tff(c_2145,plain,(
    ! [A_18] : r1_tarski('#skF_4',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_2021])).

tff(c_28,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_303,plain,(
    ! [A_87] : k3_xboole_0(k1_xboole_0,A_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_281])).

tff(c_312,plain,(
    ! [A_87] : k3_xboole_0(A_87,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_2])).

tff(c_450,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ r1_xboole_0(A_98,B_99)
      | ~ r2_hidden(C_100,k3_xboole_0(A_98,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_453,plain,(
    ! [A_87,C_100] :
      ( ~ r1_xboole_0(A_87,k1_xboole_0)
      | ~ r2_hidden(C_100,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_450])).

tff(c_467,plain,(
    ! [C_100] : ~ r2_hidden(C_100,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_453])).

tff(c_2010,plain,(
    ! [C_100] : ~ r2_hidden(C_100,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_467])).

tff(c_2143,plain,(
    ! [C_100] : ~ r2_hidden(C_100,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_2010])).

tff(c_2142,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_2113])).

tff(c_64,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2018,plain,(
    k1_zfmisc_1('#skF_5') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_1995,c_64])).

tff(c_2518,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2142,c_2136,c_2136,c_2018])).

tff(c_52,plain,(
    ! [C_61,A_57] :
      ( r2_hidden(C_61,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_61,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2522,plain,(
    ! [C_61] :
      ( r2_hidden(C_61,'#skF_4')
      | ~ r1_tarski(C_61,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2518,c_52])).

tff(c_2869,plain,(
    ! [C_202] : ~ r1_tarski(C_202,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_2143,c_2522])).

tff(c_2882,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_2145,c_2869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.88  
% 4.40/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.88  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 4.40/1.88  
% 4.40/1.88  %Foreground sorts:
% 4.40/1.88  
% 4.40/1.88  
% 4.40/1.88  %Background operators:
% 4.40/1.88  
% 4.40/1.88  
% 4.40/1.88  %Foreground operators:
% 4.40/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.40/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.40/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.40/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.40/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.40/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.40/1.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.40/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.40/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.40/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.40/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.40/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.40/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.40/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.40/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.40/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.40/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.88  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.40/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.40/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.40/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.40/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.40/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.40/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.40/1.88  
% 4.40/1.90  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.40/1.90  tff(f_100, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.40/1.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.40/1.90  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.40/1.90  tff(f_67, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.40/1.90  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.40/1.90  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.40/1.90  tff(f_69, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.40/1.90  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.40/1.90  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.40/1.90  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.40/1.90  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.40/1.90  tff(f_94, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.40/1.90  tff(f_96, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 4.40/1.90  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.40/1.90  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.40/1.90  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.40/1.90  tff(f_95, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 4.40/1.90  tff(f_92, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.40/1.90  tff(c_26, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.40/1.90  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.40/1.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.40/1.90  tff(c_468, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.40/1.90  tff(c_493, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_468])).
% 4.40/1.90  tff(c_30, plain, (![A_23, B_24, C_25]: (k5_xboole_0(k5_xboole_0(A_23, B_24), C_25)=k5_xboole_0(A_23, k5_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.40/1.90  tff(c_961, plain, (![A_124, B_125]: (k5_xboole_0(k5_xboole_0(A_124, B_125), k3_xboole_0(A_124, B_125))=k2_xboole_0(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.40/1.90  tff(c_1004, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k5_xboole_0(B_24, k3_xboole_0(A_23, B_24)))=k2_xboole_0(A_23, B_24))), inference(superposition, [status(thm), theory('equality')], [c_30, c_961])).
% 4.40/1.90  tff(c_1496, plain, (![A_153, B_154]: (k5_xboole_0(A_153, k4_xboole_0(B_154, A_153))=k2_xboole_0(A_153, B_154))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_1004])).
% 4.40/1.90  tff(c_130, plain, (![B_73, A_74]: (k5_xboole_0(B_73, A_74)=k5_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.40/1.90  tff(c_146, plain, (![A_74]: (k5_xboole_0(k1_xboole_0, A_74)=A_74)), inference(superposition, [status(thm), theory('equality')], [c_130, c_26])).
% 4.40/1.90  tff(c_32, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.40/1.90  tff(c_721, plain, (![A_117, B_118, C_119]: (k5_xboole_0(k5_xboole_0(A_117, B_118), C_119)=k5_xboole_0(A_117, k5_xboole_0(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.40/1.90  tff(c_796, plain, (![A_26, C_119]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_119))=k5_xboole_0(k1_xboole_0, C_119))), inference(superposition, [status(thm), theory('equality')], [c_32, c_721])).
% 4.40/1.90  tff(c_809, plain, (![A_26, C_119]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_119))=C_119)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_796])).
% 4.40/1.90  tff(c_1840, plain, (![A_168, B_169]: (k5_xboole_0(A_168, k2_xboole_0(A_168, B_169))=k4_xboole_0(B_169, A_168))), inference(superposition, [status(thm), theory('equality')], [c_1496, c_809])).
% 4.40/1.90  tff(c_1895, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1840])).
% 4.40/1.90  tff(c_1907, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1895])).
% 4.40/1.90  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.40/1.90  tff(c_810, plain, (![A_120, C_121]: (k5_xboole_0(A_120, k5_xboole_0(A_120, C_121))=C_121)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_796])).
% 4.40/1.90  tff(c_856, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_810])).
% 4.40/1.90  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.40/1.90  tff(c_281, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.40/1.90  tff(c_291, plain, (![A_19, B_20]: (k3_xboole_0(k4_xboole_0(A_19, B_20), A_19)=k4_xboole_0(A_19, B_20))), inference(resolution, [status(thm)], [c_24, c_281])).
% 4.40/1.90  tff(c_1010, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_19, B_20), A_19), k4_xboole_0(A_19, B_20))=k2_xboole_0(k4_xboole_0(A_19, B_20), A_19))), inference(superposition, [status(thm), theory('equality')], [c_291, c_961])).
% 4.40/1.90  tff(c_1056, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_856, c_4, c_4, c_1010])).
% 4.40/1.90  tff(c_1963, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1907, c_1056])).
% 4.40/1.90  tff(c_1995, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_68])).
% 4.40/1.90  tff(c_572, plain, (![A_111, B_112]: (k3_xboole_0(k4_xboole_0(A_111, B_112), A_111)=k4_xboole_0(A_111, B_112))), inference(resolution, [status(thm)], [c_24, c_281])).
% 4.40/1.90  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.40/1.90  tff(c_578, plain, (![A_111, B_112]: (k5_xboole_0(k4_xboole_0(A_111, B_112), k4_xboole_0(A_111, B_112))=k4_xboole_0(k4_xboole_0(A_111, B_112), A_111))), inference(superposition, [status(thm), theory('equality')], [c_572, c_18])).
% 4.40/1.90  tff(c_617, plain, (![A_111, B_112]: (k4_xboole_0(k4_xboole_0(A_111, B_112), A_111)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_578])).
% 4.40/1.90  tff(c_1966, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1907, c_617])).
% 4.40/1.90  tff(c_2083, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_1966])).
% 4.40/1.90  tff(c_1535, plain, (![A_111, B_112]: (k2_xboole_0(A_111, k4_xboole_0(A_111, B_112))=k5_xboole_0(A_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_617, c_1496])).
% 4.40/1.90  tff(c_1552, plain, (![A_111, B_112]: (k2_xboole_0(A_111, k4_xboole_0(A_111, B_112))=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1535])).
% 4.40/1.90  tff(c_2096, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2083, c_1552])).
% 4.40/1.90  tff(c_2113, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_2096])).
% 4.40/1.90  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.40/1.90  tff(c_36, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.40/1.90  tff(c_378, plain, (![A_89, B_90]: (k3_tarski(k2_tarski(A_89, B_90))=k2_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.40/1.90  tff(c_387, plain, (![A_29]: (k3_tarski(k1_tarski(A_29))=k2_xboole_0(A_29, A_29))), inference(superposition, [status(thm), theory('equality')], [c_36, c_378])).
% 4.40/1.90  tff(c_390, plain, (![A_29]: (k3_tarski(k1_tarski(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_387])).
% 4.40/1.90  tff(c_2131, plain, (k3_tarski('#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2113, c_390])).
% 4.40/1.90  tff(c_66, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.40/1.90  tff(c_2023, plain, (k3_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_1995, c_66])).
% 4.40/1.90  tff(c_2136, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2131, c_2023])).
% 4.40/1.90  tff(c_22, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.40/1.90  tff(c_2021, plain, (![A_18]: (r1_tarski('#skF_5', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_22])).
% 4.40/1.90  tff(c_2145, plain, (![A_18]: (r1_tarski('#skF_4', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_2021])).
% 4.40/1.90  tff(c_28, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.40/1.90  tff(c_303, plain, (![A_87]: (k3_xboole_0(k1_xboole_0, A_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_281])).
% 4.40/1.90  tff(c_312, plain, (![A_87]: (k3_xboole_0(A_87, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_303, c_2])).
% 4.40/1.90  tff(c_450, plain, (![A_98, B_99, C_100]: (~r1_xboole_0(A_98, B_99) | ~r2_hidden(C_100, k3_xboole_0(A_98, B_99)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.40/1.90  tff(c_453, plain, (![A_87, C_100]: (~r1_xboole_0(A_87, k1_xboole_0) | ~r2_hidden(C_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_312, c_450])).
% 4.40/1.90  tff(c_467, plain, (![C_100]: (~r2_hidden(C_100, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_453])).
% 4.40/1.90  tff(c_2010, plain, (![C_100]: (~r2_hidden(C_100, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_467])).
% 4.40/1.90  tff(c_2143, plain, (![C_100]: (~r2_hidden(C_100, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_2010])).
% 4.40/1.90  tff(c_2142, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_2113])).
% 4.40/1.90  tff(c_64, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.40/1.90  tff(c_2018, plain, (k1_zfmisc_1('#skF_5')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_1995, c_64])).
% 4.40/1.90  tff(c_2518, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2142, c_2136, c_2136, c_2018])).
% 4.40/1.90  tff(c_52, plain, (![C_61, A_57]: (r2_hidden(C_61, k1_zfmisc_1(A_57)) | ~r1_tarski(C_61, A_57))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.40/1.90  tff(c_2522, plain, (![C_61]: (r2_hidden(C_61, '#skF_4') | ~r1_tarski(C_61, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2518, c_52])).
% 4.40/1.90  tff(c_2869, plain, (![C_202]: (~r1_tarski(C_202, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_2143, c_2522])).
% 4.40/1.90  tff(c_2882, plain, $false, inference(resolution, [status(thm)], [c_2145, c_2869])).
% 4.40/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.90  
% 4.40/1.90  Inference rules
% 4.40/1.90  ----------------------
% 4.40/1.90  #Ref     : 0
% 4.40/1.90  #Sup     : 696
% 4.40/1.90  #Fact    : 0
% 4.40/1.90  #Define  : 0
% 4.40/1.90  #Split   : 0
% 4.40/1.90  #Chain   : 0
% 4.40/1.90  #Close   : 0
% 4.40/1.90  
% 4.40/1.90  Ordering : KBO
% 4.40/1.90  
% 4.40/1.90  Simplification rules
% 4.40/1.90  ----------------------
% 4.40/1.90  #Subsume      : 30
% 4.40/1.90  #Demod        : 453
% 4.40/1.90  #Tautology    : 409
% 4.40/1.90  #SimpNegUnit  : 3
% 4.40/1.90  #BackRed      : 34
% 4.40/1.90  
% 4.40/1.90  #Partial instantiations: 0
% 4.40/1.90  #Strategies tried      : 1
% 4.40/1.90  
% 4.40/1.90  Timing (in seconds)
% 4.40/1.90  ----------------------
% 4.40/1.90  Preprocessing        : 0.34
% 4.40/1.90  Parsing              : 0.18
% 4.40/1.90  CNF conversion       : 0.02
% 4.40/1.90  Main loop            : 0.79
% 4.40/1.91  Inferencing          : 0.25
% 4.40/1.91  Reduction            : 0.34
% 4.40/1.91  Demodulation         : 0.28
% 4.40/1.91  BG Simplification    : 0.03
% 4.40/1.91  Subsumption          : 0.11
% 4.40/1.91  Abstraction          : 0.04
% 4.40/1.91  MUC search           : 0.00
% 4.40/1.91  Cooper               : 0.00
% 4.40/1.91  Total                : 1.17
% 4.40/1.91  Index Insertion      : 0.00
% 4.40/1.91  Index Deletion       : 0.00
% 4.40/1.91  Index Matching       : 0.00
% 4.40/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------

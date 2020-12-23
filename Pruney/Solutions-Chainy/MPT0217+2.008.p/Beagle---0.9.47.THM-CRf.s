%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:46 EST 2020

% Result     : Theorem 14.49s
% Output     : CNFRefutation 14.76s
% Verified   : 
% Statistics : Number of formulae       :  214 (3719 expanded)
%              Number of leaves         :   31 (1235 expanded)
%              Depth                    :   24
%              Number of atoms          :  283 (4892 expanded)
%              Number of equality atoms :  211 (4607 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( k2_tarski(A,B) = k2_tarski(C,D)
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( A != B
        & A != C
        & k4_xboole_0(k1_enumset1(A,B,C),k1_tarski(A)) != k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_40,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_77,plain,(
    ! [C_46,B_47,A_48] :
      ( C_46 = B_47
      | k2_tarski(B_47,C_46) != k1_tarski(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_80,plain,(
    ! [A_48] :
      ( '#skF_3' = '#skF_4'
      | k2_tarski('#skF_1','#skF_2') != k1_tarski(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_77])).

tff(c_246,plain,(
    ! [A_48] : k2_tarski('#skF_1','#skF_2') != k1_tarski(A_48) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_138,plain,(
    ! [A_54,B_55] : k2_xboole_0(k1_tarski(A_54),k1_tarski(B_55)) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_248,plain,(
    ! [A_62,B_63] : r1_tarski(k1_tarski(A_62),k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_18])).

tff(c_254,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_248])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_359,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_tarski(A_72,C_73)
      | ~ r1_tarski(B_74,C_73)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_381,plain,(
    ! [A_75,A_76] :
      ( r1_tarski(A_75,A_76)
      | ~ r1_tarski(A_75,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_359])).

tff(c_384,plain,(
    ! [A_1,A_76] :
      ( r1_tarski(A_1,A_76)
      | k4_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_381])).

tff(c_404,plain,(
    ! [A_77,A_78] :
      ( r1_tarski(A_77,A_78)
      | k1_xboole_0 != A_77 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_384])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1377,plain,(
    ! [A_131,A_132,A_133] :
      ( r1_tarski(A_131,A_132)
      | ~ r1_tarski(A_131,A_133)
      | k1_xboole_0 != A_133 ) ),
    inference(resolution,[status(thm)],[c_404,c_6])).

tff(c_1435,plain,(
    ! [A_132] :
      ( r1_tarski(k1_tarski('#skF_3'),A_132)
      | k2_tarski('#skF_1','#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_254,c_1377])).

tff(c_1857,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1435])).

tff(c_24,plain,(
    ! [A_23,B_24] : k2_xboole_0(k1_tarski(A_23),k1_tarski(B_24)) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_287,plain,(
    ! [A_66,B_67] : k2_xboole_0(A_66,k2_xboole_0(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_308,plain,(
    ! [A_23,B_24] : k2_xboole_0(k1_tarski(A_23),k2_tarski(A_23,B_24)) = k2_xboole_0(k1_tarski(A_23),k1_tarski(B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_287])).

tff(c_1858,plain,(
    ! [A_148,B_149] : k2_xboole_0(k1_tarski(A_148),k2_tarski(A_148,B_149)) = k2_tarski(A_148,B_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_308])).

tff(c_26,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k1_tarski(A_25),k2_tarski(B_26,C_27)) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1869,plain,(
    ! [A_148,B_149] : k1_enumset1(A_148,A_148,B_149) = k2_tarski(A_148,B_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_1858,c_26])).

tff(c_1108,plain,(
    ! [B_117,A_118,C_119] : k2_xboole_0(k2_tarski(B_117,A_118),k2_tarski(C_119,A_118)) = k1_enumset1(A_118,B_117,C_119) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1135,plain,(
    ! [A_28,C_119] : k2_xboole_0(k1_tarski(A_28),k2_tarski(C_119,A_28)) = k1_enumset1(A_28,A_28,C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1108])).

tff(c_2516,plain,(
    ! [A_165,C_166] : k2_xboole_0(k1_tarski(A_165),k2_tarski(C_166,A_165)) = k2_tarski(A_165,C_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1869,c_1135])).

tff(c_2566,plain,(
    ! [A_167,C_168] : k1_enumset1(A_167,C_168,A_167) = k2_tarski(A_167,C_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_2516,c_26])).

tff(c_854,plain,(
    ! [A_98,B_99,C_100] : k2_xboole_0(k1_tarski(A_98),k2_tarski(B_99,C_100)) = k1_enumset1(A_98,B_99,C_100) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_872,plain,(
    ! [A_98] : k2_xboole_0(k1_tarski(A_98),k2_tarski('#skF_1','#skF_2')) = k1_enumset1(A_98,'#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_854])).

tff(c_879,plain,(
    ! [A_98] : k1_enumset1(A_98,'#skF_3','#skF_4') = k1_enumset1(A_98,'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_872])).

tff(c_2594,plain,(
    k1_enumset1('#skF_4','#skF_1','#skF_2') = k2_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2566,c_879])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( k4_xboole_0(k1_enumset1(A_17,B_18,C_19),k1_tarski(A_17)) = k2_tarski(B_18,C_19)
      | C_19 = A_17
      | B_18 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2662,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski('#skF_4')) = k2_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2594,c_20])).

tff(c_2677,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski('#skF_4')) = k2_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2662])).

tff(c_15022,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2677])).

tff(c_42,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1899,plain,(
    ! [A_150,B_151] : k1_enumset1(A_150,A_150,B_151) = k2_tarski(A_150,B_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_1858,c_26])).

tff(c_1933,plain,(
    k1_enumset1('#skF_3','#skF_1','#skF_2') = k2_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_1899])).

tff(c_1946,plain,(
    k1_enumset1('#skF_3','#skF_1','#skF_2') = k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1933])).

tff(c_2021,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) = k2_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1946,c_20])).

tff(c_2036,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) = k2_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2021])).

tff(c_3329,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2036])).

tff(c_3574,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski('#skF_4')) = k2_tarski('#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3329,c_3329,c_2677])).

tff(c_3575,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3574])).

tff(c_3354,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3329,c_44])).

tff(c_3579,plain,(
    k2_tarski('#skF_1','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3575,c_3575,c_3354])).

tff(c_3589,plain,(
    k2_tarski('#skF_1','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3579])).

tff(c_38,plain,(
    ! [C_35,B_34,A_33] :
      ( C_35 = B_34
      | k2_tarski(B_34,C_35) != k1_tarski(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3645,plain,(
    ! [A_33] :
      ( '#skF_1' = '#skF_4'
      | k1_tarski(A_33) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3589,c_38])).

tff(c_3657,plain,(
    ! [A_33] : k1_tarski(A_33) != k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3645])).

tff(c_3776,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3657])).

tff(c_3778,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3574])).

tff(c_2531,plain,(
    ! [A_165,C_166] : k1_enumset1(A_165,C_166,A_165) = k2_tarski(A_165,C_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_2516,c_26])).

tff(c_1138,plain,(
    ! [B_117,A_28] : k2_xboole_0(k2_tarski(B_117,A_28),k1_tarski(A_28)) = k1_enumset1(A_28,B_117,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1108])).

tff(c_2696,plain,(
    ! [B_169,A_170] : k2_xboole_0(k2_tarski(B_169,A_170),k1_tarski(A_170)) = k2_tarski(A_170,B_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2531,c_1138])).

tff(c_2719,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_4')) = k2_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2696])).

tff(c_3332,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k1_tarski('#skF_4')) = k2_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3329,c_2719])).

tff(c_22,plain,(
    ! [B_21,A_20,C_22] : k2_xboole_0(k2_tarski(B_21,A_20),k2_tarski(C_22,A_20)) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12858,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_4','#skF_3')) = k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3332,c_16])).

tff(c_12877,plain,(
    k1_enumset1('#skF_3','#skF_1','#skF_4') = k2_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3332,c_22,c_12858])).

tff(c_12959,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski('#skF_3')) = k2_tarski('#skF_1','#skF_4')
    | '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12877,c_20])).

tff(c_12979,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski('#skF_3')) = k2_tarski('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3778,c_12959])).

tff(c_2515,plain,(
    ! [A_28,C_119] : k2_xboole_0(k1_tarski(A_28),k2_tarski(C_119,A_28)) = k2_tarski(A_28,C_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1869,c_1135])).

tff(c_860,plain,(
    ! [A_98,B_99,C_100] : k2_xboole_0(k1_tarski(A_98),k1_enumset1(A_98,B_99,C_100)) = k2_xboole_0(k1_tarski(A_98),k2_tarski(B_99,C_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_16])).

tff(c_877,plain,(
    ! [A_98,B_99,C_100] : k2_xboole_0(k1_tarski(A_98),k1_enumset1(A_98,B_99,C_100)) = k1_enumset1(A_98,B_99,C_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_860])).

tff(c_12956,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_3')) = k1_enumset1('#skF_3','#skF_1','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12877,c_877])).

tff(c_12978,plain,(
    k2_tarski('#skF_1','#skF_3') = k2_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12877,c_3354,c_2515,c_12956])).

tff(c_13076,plain,(
    ! [C_22] : k2_xboole_0(k2_tarski('#skF_4','#skF_3'),k2_tarski(C_22,'#skF_3')) = k1_enumset1('#skF_3','#skF_1',C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_12978,c_22])).

tff(c_14678,plain,(
    ! [C_360] : k1_enumset1('#skF_3','#skF_1',C_360) = k1_enumset1('#skF_3','#skF_4',C_360) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_13076])).

tff(c_14691,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_4') = k2_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14678,c_12877])).

tff(c_14820,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_4')
    | '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_14691,c_20])).

tff(c_14848,plain,
    ( k2_tarski('#skF_1','#skF_4') = k1_tarski('#skF_4')
    | '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12979,c_28,c_14820])).

tff(c_14849,plain,(
    k2_tarski('#skF_1','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3778,c_3778,c_14848])).

tff(c_14996,plain,(
    ! [A_33] :
      ( '#skF_1' = '#skF_4'
      | k1_tarski(A_33) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14849,c_38])).

tff(c_15014,plain,(
    ! [A_33] : k1_tarski(A_33) != k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_14996])).

tff(c_15019,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15014])).

tff(c_15021,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2036])).

tff(c_15023,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15022,c_15021])).

tff(c_15028,plain,(
    k1_enumset1('#skF_4','#skF_1','#skF_4') = k2_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15022,c_2594])).

tff(c_15050,plain,(
    k2_tarski('#skF_4','#skF_3') = k2_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2531,c_15028])).

tff(c_15223,plain,(
    ! [A_33] :
      ( '#skF_3' = '#skF_4'
      | k2_tarski('#skF_4','#skF_1') != k1_tarski(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15050,c_38])).

tff(c_15230,plain,(
    ! [A_33] : k2_tarski('#skF_4','#skF_1') != k1_tarski(A_33) ),
    inference(negUnitSimplification,[status(thm)],[c_15023,c_15223])).

tff(c_1129,plain,(
    ! [C_119] : k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski(C_119,'#skF_4')) = k1_enumset1('#skF_4','#skF_3',C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1108])).

tff(c_15030,plain,(
    ! [C_119] : k2_xboole_0(k2_tarski('#skF_1','#skF_4'),k2_tarski(C_119,'#skF_4')) = k1_enumset1('#skF_4','#skF_3',C_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15022,c_1129])).

tff(c_16352,plain,(
    ! [C_394] : k1_enumset1('#skF_4','#skF_3',C_394) = k1_enumset1('#skF_4','#skF_1',C_394) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_15030])).

tff(c_875,plain,(
    ! [A_98,A_28] : k2_xboole_0(k1_tarski(A_98),k1_tarski(A_28)) = k1_enumset1(A_98,A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_854])).

tff(c_880,plain,(
    ! [A_98,A_28] : k1_enumset1(A_98,A_28,A_28) = k2_tarski(A_98,A_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_875])).

tff(c_16381,plain,(
    k1_enumset1('#skF_4','#skF_1','#skF_3') = k2_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16352,c_880])).

tff(c_16403,plain,(
    k1_enumset1('#skF_4','#skF_1','#skF_3') = k2_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15050,c_16381])).

tff(c_16446,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_1'),k1_tarski('#skF_4')) = k2_tarski('#skF_1','#skF_3')
    | '#skF_3' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16403,c_20])).

tff(c_16462,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_1'),k1_tarski('#skF_4')) = k2_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_15023,c_16446])).

tff(c_1132,plain,(
    ! [B_117] : k2_xboole_0(k2_tarski(B_117,'#skF_4'),k2_tarski('#skF_1','#skF_2')) = k1_enumset1('#skF_4',B_117,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1108])).

tff(c_15035,plain,(
    ! [B_117] : k2_xboole_0(k2_tarski(B_117,'#skF_4'),k2_tarski('#skF_1','#skF_4')) = k1_enumset1('#skF_4',B_117,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15022,c_1132])).

tff(c_16598,plain,(
    ! [B_400] : k1_enumset1('#skF_4',B_400,'#skF_3') = k1_enumset1('#skF_4',B_400,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_15035])).

tff(c_16641,plain,(
    k1_enumset1('#skF_4','#skF_3','#skF_1') = k2_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16598,c_880])).

tff(c_16675,plain,(
    k1_enumset1('#skF_4','#skF_3','#skF_1') = k2_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15050,c_16641])).

tff(c_16745,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_1'),k1_tarski('#skF_4')) = k2_tarski('#skF_3','#skF_1')
    | '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16675,c_20])).

tff(c_16765,plain,
    ( k2_tarski('#skF_3','#skF_1') = k2_tarski('#skF_1','#skF_3')
    | '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16462,c_16745])).

tff(c_16766,plain,(
    k2_tarski('#skF_3','#skF_1') = k2_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_15023,c_40,c_16765])).

tff(c_56,plain,(
    ! [A_38,B_39] : r1_tarski(k4_xboole_0(A_38,B_39),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_56])).

tff(c_498,plain,(
    ! [A_83,B_84,C_85] :
      ( r1_tarski(k4_xboole_0(A_83,B_84),C_85)
      | ~ r1_tarski(A_83,k2_xboole_0(B_84,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15555,plain,(
    ! [A_374,B_375,C_376] :
      ( k4_xboole_0(k4_xboole_0(A_374,B_375),C_376) = k1_xboole_0
      | ~ r1_tarski(A_374,k2_xboole_0(B_375,C_376)) ) ),
    inference(resolution,[status(thm)],[c_498,c_4])).

tff(c_15872,plain,(
    ! [B_384,C_385] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_384,C_385),B_384),C_385) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_15555])).

tff(c_15927,plain,(
    ! [B_384] : k4_xboole_0(k2_xboole_0(B_384,k1_xboole_0),B_384) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15872,c_12])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_543,plain,(
    ! [A_86,A_87,B_88] :
      ( r1_tarski(A_86,A_87)
      | ~ r1_tarski(A_86,k4_xboole_0(A_87,B_88)) ) ),
    inference(resolution,[status(thm)],[c_10,c_359])).

tff(c_18005,plain,(
    ! [A_425,A_426,B_427] :
      ( r1_tarski(A_425,A_426)
      | k4_xboole_0(A_425,k4_xboole_0(A_426,B_427)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_543])).

tff(c_18163,plain,(
    ! [A_428,B_429] : r1_tarski(k2_xboole_0(k4_xboole_0(A_428,B_429),k1_xboole_0),A_428) ),
    inference(superposition,[status(thm),theory(equality)],[c_15927,c_18005])).

tff(c_18306,plain,(
    ! [A_430] : r1_tarski(k2_xboole_0(A_430,k1_xboole_0),A_430) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_18163])).

tff(c_421,plain,(
    ! [A_3,A_78,A_77] :
      ( r1_tarski(A_3,A_78)
      | ~ r1_tarski(A_3,A_77)
      | k1_xboole_0 != A_77 ) ),
    inference(resolution,[status(thm)],[c_404,c_6])).

tff(c_18363,plain,(
    ! [A_431,A_432] :
      ( r1_tarski(k2_xboole_0(A_431,k1_xboole_0),A_432)
      | k1_xboole_0 != A_431 ) ),
    inference(resolution,[status(thm)],[c_18306,c_421])).

tff(c_19190,plain,(
    ! [A_447,A_448] :
      ( k4_xboole_0(k2_xboole_0(A_447,k1_xboole_0),A_448) = k1_xboole_0
      | k1_xboole_0 != A_447 ) ),
    inference(resolution,[status(thm)],[c_18363,c_4])).

tff(c_19386,plain,(
    ! [A_449] :
      ( k2_xboole_0(A_449,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_449 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19190,c_12])).

tff(c_96,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_96])).

tff(c_3058,plain,(
    ! [A_174,B_175,A_176] :
      ( r1_tarski(A_174,B_175)
      | ~ r1_tarski(A_174,A_176)
      | k4_xboole_0(A_176,B_175) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_359])).

tff(c_3191,plain,(
    ! [A_177,B_178,B_179] :
      ( r1_tarski(A_177,B_178)
      | k4_xboole_0(k2_xboole_0(A_177,B_179),B_178) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_3058])).

tff(c_3268,plain,(
    ! [A_180,B_181,B_182] : r1_tarski(A_180,k2_xboole_0(k2_xboole_0(A_180,B_181),B_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_3191])).

tff(c_3324,plain,(
    ! [A_180,B_181,B_182] : k4_xboole_0(A_180,k2_xboole_0(k2_xboole_0(A_180,B_181),B_182)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3268,c_4])).

tff(c_19452,plain,(
    ! [A_180,B_181] :
      ( k4_xboole_0(A_180,k1_xboole_0) = k1_xboole_0
      | k2_xboole_0(A_180,B_181) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19386,c_3324])).

tff(c_19572,plain,(
    ! [A_450,B_451] :
      ( k1_xboole_0 = A_450
      | k2_xboole_0(A_450,B_451) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19452])).

tff(c_19612,plain,(
    ! [A_452,C_453] :
      ( k1_tarski(A_452) = k1_xboole_0
      | k2_tarski(A_452,C_453) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2515,c_19572])).

tff(c_19621,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | k2_tarski('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16766,c_19612])).

tff(c_19628,plain,(
    k2_tarski('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_19621])).

tff(c_16836,plain,(
    ! [A_33] :
      ( '#skF_3' = '#skF_1'
      | k2_tarski('#skF_1','#skF_3') != k1_tarski(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16766,c_38])).

tff(c_16851,plain,(
    ! [A_33] : k2_tarski('#skF_1','#skF_3') != k1_tarski(A_33) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_16836])).

tff(c_15659,plain,(
    ! [B_375,C_376] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_375,C_376),B_375),C_376) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_15555])).

tff(c_26505,plain,(
    ! [B_545,A_546,B_547] : r1_tarski(k4_xboole_0(k2_xboole_0(B_545,k4_xboole_0(A_546,B_547)),B_545),A_546) ),
    inference(superposition,[status(thm),theory(equality)],[c_15659,c_18005])).

tff(c_26777,plain,(
    ! [B_548,A_549] : r1_tarski(k4_xboole_0(k2_xboole_0(B_548,A_549),B_548),A_549) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_26505])).

tff(c_29736,plain,(
    ! [A_609,B_610] : r1_tarski(k4_xboole_0(k2_tarski(A_609,B_610),k1_tarski(A_609)),k1_tarski(B_610)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_26777])).

tff(c_29766,plain,(
    r1_tarski(k4_xboole_0(k2_tarski('#skF_4','#skF_1'),k1_tarski('#skF_4')),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15050,c_29736])).

tff(c_29780,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_3'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16462,c_29766])).

tff(c_30,plain,(
    ! [B_30,A_29] :
      ( k1_tarski(B_30) = A_29
      | k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,k1_tarski(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_29794,plain,
    ( k2_tarski('#skF_1','#skF_3') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29780,c_30])).

tff(c_29807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19628,c_16851,c_29794])).

tff(c_29808,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_19621])).

tff(c_36,plain,(
    ! [B_32,A_31] :
      ( B_32 = A_31
      | ~ r1_tarski(k1_tarski(A_31),k1_tarski(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_424,plain,(
    ! [B_32,A_31] :
      ( B_32 = A_31
      | k1_tarski(A_31) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_404,c_36])).

tff(c_30094,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_29808,c_424])).

tff(c_15034,plain,(
    k1_enumset1('#skF_3','#skF_1','#skF_4') = k2_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15022,c_15022,c_1946])).

tff(c_15445,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_4'),k1_tarski('#skF_3')) = k2_tarski('#skF_1','#skF_4')
    | '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_15034,c_20])).

tff(c_15458,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_4'),k1_tarski('#skF_3')) = k2_tarski('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_15023,c_15445])).

tff(c_15048,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15022,c_44])).

tff(c_15214,plain,(
    ! [A_25] : k2_xboole_0(k1_tarski(A_25),k2_tarski('#skF_4','#skF_1')) = k1_enumset1(A_25,'#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15050,c_26])).

tff(c_17319,plain,(
    ! [A_417] : k1_enumset1(A_417,'#skF_4','#skF_3') = k1_enumset1(A_417,'#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_15214])).

tff(c_17345,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_1') = k2_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17319,c_2531])).

tff(c_17384,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_1') = k2_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15048,c_17345])).

tff(c_17412,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_4'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_1')
    | '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_17384,c_20])).

tff(c_17430,plain,
    ( k2_tarski('#skF_1','#skF_4') = k2_tarski('#skF_4','#skF_1')
    | '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15458,c_17412])).

tff(c_17431,plain,(
    k2_tarski('#skF_1','#skF_4') = k2_tarski('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_15023,c_42,c_17430])).

tff(c_17442,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17431,c_15048])).

tff(c_30095,plain,(
    k2_tarski('#skF_4','#skF_1') = k2_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30094,c_17442])).

tff(c_30523,plain,(
    k2_tarski('#skF_4','#skF_1') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30095])).

tff(c_30525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15230,c_30523])).

tff(c_30526,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski('#skF_4')) = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2677])).

tff(c_31181,plain,(
    ! [A_1883,B_1884,C_1885] :
      ( k4_xboole_0(k4_xboole_0(A_1883,B_1884),C_1885) = k1_xboole_0
      | ~ r1_tarski(A_1883,k2_xboole_0(B_1884,C_1885)) ) ),
    inference(resolution,[status(thm)],[c_498,c_4])).

tff(c_31302,plain,(
    ! [B_1884,C_1885] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_1884,C_1885),B_1884),C_1885) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_31181])).

tff(c_33064,plain,(
    ! [A_1925,A_1926,B_1927] :
      ( r1_tarski(A_1925,A_1926)
      | k4_xboole_0(A_1925,k4_xboole_0(A_1926,B_1927)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_543])).

tff(c_42634,plain,(
    ! [B_2044,A_2045,B_2046] : r1_tarski(k4_xboole_0(k2_xboole_0(B_2044,k4_xboole_0(A_2045,B_2046)),B_2044),A_2045) ),
    inference(superposition,[status(thm),theory(equality)],[c_31302,c_33064])).

tff(c_43034,plain,(
    ! [B_2048,A_2049] : r1_tarski(k4_xboole_0(k2_xboole_0(B_2048,A_2049),B_2048),A_2049) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_42634])).

tff(c_50050,plain,(
    ! [A_2146,B_2147] : r1_tarski(k4_xboole_0(k2_tarski(A_2146,B_2147),k1_tarski(A_2146)),k1_tarski(B_2147)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_43034])).

tff(c_50070,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30526,c_50050])).

tff(c_50110,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50070,c_30])).

tff(c_50124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1857,c_246,c_50110])).

tff(c_50169,plain,(
    ! [A_2150] : r1_tarski(k1_tarski('#skF_3'),A_2150) ),
    inference(splitRight,[status(thm)],[c_1435])).

tff(c_50505,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50169,c_36])).

tff(c_50506,plain,(
    k2_tarski('#skF_1','#skF_2') = k2_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50505,c_44])).

tff(c_50537,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50506])).

tff(c_50539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_50537])).

tff(c_50540,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_50541,plain,(
    k2_tarski('#skF_1','#skF_2') = k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50540,c_44])).

tff(c_50543,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50541])).

tff(c_50555,plain,(
    ! [A_2812,B_2813] : r1_tarski(k1_tarski(A_2812),k2_tarski(A_2812,B_2813)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_18])).

tff(c_50561,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50543,c_50555])).

tff(c_50572,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50561,c_36])).

tff(c_50577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:59:32 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.49/6.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.49/6.80  
% 14.49/6.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.49/6.81  %$ r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.49/6.81  
% 14.49/6.81  %Foreground sorts:
% 14.49/6.81  
% 14.49/6.81  
% 14.49/6.81  %Background operators:
% 14.49/6.81  
% 14.49/6.81  
% 14.49/6.81  %Foreground operators:
% 14.49/6.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.49/6.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.49/6.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.49/6.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.49/6.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.49/6.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.49/6.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.49/6.81  tff('#skF_2', type, '#skF_2': $i).
% 14.49/6.81  tff('#skF_3', type, '#skF_3': $i).
% 14.49/6.81  tff('#skF_1', type, '#skF_1': $i).
% 14.49/6.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.49/6.81  tff('#skF_4', type, '#skF_4': $i).
% 14.49/6.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.49/6.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.49/6.81  
% 14.76/6.83  tff(f_91, negated_conjecture, ~(![A, B, C, D]: ~(((k2_tarski(A, B) = k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_zfmisc_1)).
% 14.76/6.83  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 14.76/6.83  tff(f_81, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 14.76/6.83  tff(f_63, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 14.76/6.83  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.76/6.83  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 14.76/6.83  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.76/6.83  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.76/6.83  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.76/6.83  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 14.76/6.83  tff(f_65, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 14.76/6.83  tff(f_61, axiom, (![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 14.76/6.83  tff(f_59, axiom, (![A, B, C]: ~((~(A = B) & ~(A = C)) & ~(k4_xboole_0(k1_enumset1(A, B, C), k1_tarski(A)) = k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_enumset1)).
% 14.76/6.83  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.76/6.83  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 14.76/6.83  tff(f_73, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 14.76/6.83  tff(f_77, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 14.76/6.83  tff(c_40, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.76/6.83  tff(c_28, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.76/6.83  tff(c_44, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.76/6.83  tff(c_77, plain, (![C_46, B_47, A_48]: (C_46=B_47 | k2_tarski(B_47, C_46)!=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.76/6.83  tff(c_80, plain, (![A_48]: ('#skF_3'='#skF_4' | k2_tarski('#skF_1', '#skF_2')!=k1_tarski(A_48))), inference(superposition, [status(thm), theory('equality')], [c_44, c_77])).
% 14.76/6.83  tff(c_246, plain, (![A_48]: (k2_tarski('#skF_1', '#skF_2')!=k1_tarski(A_48))), inference(splitLeft, [status(thm)], [c_80])).
% 14.76/6.83  tff(c_138, plain, (![A_54, B_55]: (k2_xboole_0(k1_tarski(A_54), k1_tarski(B_55))=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.76/6.83  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.76/6.83  tff(c_248, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_18])).
% 14.76/6.83  tff(c_254, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_248])).
% 14.76/6.83  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.76/6.83  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.76/6.83  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.76/6.83  tff(c_359, plain, (![A_72, C_73, B_74]: (r1_tarski(A_72, C_73) | ~r1_tarski(B_74, C_73) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.76/6.83  tff(c_381, plain, (![A_75, A_76]: (r1_tarski(A_75, A_76) | ~r1_tarski(A_75, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_359])).
% 14.76/6.83  tff(c_384, plain, (![A_1, A_76]: (r1_tarski(A_1, A_76) | k4_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_381])).
% 14.76/6.83  tff(c_404, plain, (![A_77, A_78]: (r1_tarski(A_77, A_78) | k1_xboole_0!=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_384])).
% 14.76/6.83  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.76/6.83  tff(c_1377, plain, (![A_131, A_132, A_133]: (r1_tarski(A_131, A_132) | ~r1_tarski(A_131, A_133) | k1_xboole_0!=A_133)), inference(resolution, [status(thm)], [c_404, c_6])).
% 14.76/6.83  tff(c_1435, plain, (![A_132]: (r1_tarski(k1_tarski('#skF_3'), A_132) | k2_tarski('#skF_1', '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_254, c_1377])).
% 14.76/6.83  tff(c_1857, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1435])).
% 14.76/6.83  tff(c_24, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(B_24))=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.76/6.83  tff(c_287, plain, (![A_66, B_67]: (k2_xboole_0(A_66, k2_xboole_0(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.76/6.83  tff(c_308, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), k2_tarski(A_23, B_24))=k2_xboole_0(k1_tarski(A_23), k1_tarski(B_24)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_287])).
% 14.76/6.83  tff(c_1858, plain, (![A_148, B_149]: (k2_xboole_0(k1_tarski(A_148), k2_tarski(A_148, B_149))=k2_tarski(A_148, B_149))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_308])).
% 14.76/6.83  tff(c_26, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k1_tarski(A_25), k2_tarski(B_26, C_27))=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.76/6.83  tff(c_1869, plain, (![A_148, B_149]: (k1_enumset1(A_148, A_148, B_149)=k2_tarski(A_148, B_149))), inference(superposition, [status(thm), theory('equality')], [c_1858, c_26])).
% 14.76/6.83  tff(c_1108, plain, (![B_117, A_118, C_119]: (k2_xboole_0(k2_tarski(B_117, A_118), k2_tarski(C_119, A_118))=k1_enumset1(A_118, B_117, C_119))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.76/6.83  tff(c_1135, plain, (![A_28, C_119]: (k2_xboole_0(k1_tarski(A_28), k2_tarski(C_119, A_28))=k1_enumset1(A_28, A_28, C_119))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1108])).
% 14.76/6.83  tff(c_2516, plain, (![A_165, C_166]: (k2_xboole_0(k1_tarski(A_165), k2_tarski(C_166, A_165))=k2_tarski(A_165, C_166))), inference(demodulation, [status(thm), theory('equality')], [c_1869, c_1135])).
% 14.76/6.83  tff(c_2566, plain, (![A_167, C_168]: (k1_enumset1(A_167, C_168, A_167)=k2_tarski(A_167, C_168))), inference(superposition, [status(thm), theory('equality')], [c_2516, c_26])).
% 14.76/6.83  tff(c_854, plain, (![A_98, B_99, C_100]: (k2_xboole_0(k1_tarski(A_98), k2_tarski(B_99, C_100))=k1_enumset1(A_98, B_99, C_100))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.76/6.83  tff(c_872, plain, (![A_98]: (k2_xboole_0(k1_tarski(A_98), k2_tarski('#skF_1', '#skF_2'))=k1_enumset1(A_98, '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_854])).
% 14.76/6.83  tff(c_879, plain, (![A_98]: (k1_enumset1(A_98, '#skF_3', '#skF_4')=k1_enumset1(A_98, '#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_872])).
% 14.76/6.83  tff(c_2594, plain, (k1_enumset1('#skF_4', '#skF_1', '#skF_2')=k2_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2566, c_879])).
% 14.76/6.83  tff(c_20, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k1_enumset1(A_17, B_18, C_19), k1_tarski(A_17))=k2_tarski(B_18, C_19) | C_19=A_17 | B_18=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.76/6.83  tff(c_2662, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski('#skF_4'))=k2_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2594, c_20])).
% 14.76/6.83  tff(c_2677, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski('#skF_4'))=k2_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_40, c_2662])).
% 14.76/6.83  tff(c_15022, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_2677])).
% 14.76/6.83  tff(c_42, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.76/6.83  tff(c_1899, plain, (![A_150, B_151]: (k1_enumset1(A_150, A_150, B_151)=k2_tarski(A_150, B_151))), inference(superposition, [status(thm), theory('equality')], [c_1858, c_26])).
% 14.76/6.83  tff(c_1933, plain, (k1_enumset1('#skF_3', '#skF_1', '#skF_2')=k2_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_879, c_1899])).
% 14.76/6.83  tff(c_1946, plain, (k1_enumset1('#skF_3', '#skF_1', '#skF_2')=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1933])).
% 14.76/6.83  tff(c_2021, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))=k2_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1946, c_20])).
% 14.76/6.83  tff(c_2036, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))=k2_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_42, c_2021])).
% 14.76/6.83  tff(c_3329, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_2036])).
% 14.76/6.83  tff(c_3574, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski('#skF_4'))=k2_tarski('#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3329, c_3329, c_2677])).
% 14.76/6.83  tff(c_3575, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_3574])).
% 14.76/6.83  tff(c_3354, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3329, c_44])).
% 14.76/6.83  tff(c_3579, plain, (k2_tarski('#skF_1', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3575, c_3575, c_3354])).
% 14.76/6.83  tff(c_3589, plain, (k2_tarski('#skF_1', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3579])).
% 14.76/6.83  tff(c_38, plain, (![C_35, B_34, A_33]: (C_35=B_34 | k2_tarski(B_34, C_35)!=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.76/6.83  tff(c_3645, plain, (![A_33]: ('#skF_1'='#skF_4' | k1_tarski(A_33)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3589, c_38])).
% 14.76/6.83  tff(c_3657, plain, (![A_33]: (k1_tarski(A_33)!=k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_3645])).
% 14.76/6.83  tff(c_3776, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3657])).
% 14.76/6.83  tff(c_3778, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_3574])).
% 14.76/6.83  tff(c_2531, plain, (![A_165, C_166]: (k1_enumset1(A_165, C_166, A_165)=k2_tarski(A_165, C_166))), inference(superposition, [status(thm), theory('equality')], [c_2516, c_26])).
% 14.76/6.83  tff(c_1138, plain, (![B_117, A_28]: (k2_xboole_0(k2_tarski(B_117, A_28), k1_tarski(A_28))=k1_enumset1(A_28, B_117, A_28))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1108])).
% 14.76/6.83  tff(c_2696, plain, (![B_169, A_170]: (k2_xboole_0(k2_tarski(B_169, A_170), k1_tarski(A_170))=k2_tarski(A_170, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_2531, c_1138])).
% 14.76/6.83  tff(c_2719, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_4'))=k2_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_2696])).
% 14.76/6.83  tff(c_3332, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k1_tarski('#skF_4'))=k2_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3329, c_2719])).
% 14.76/6.83  tff(c_22, plain, (![B_21, A_20, C_22]: (k2_xboole_0(k2_tarski(B_21, A_20), k2_tarski(C_22, A_20))=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.76/6.83  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.76/6.83  tff(c_12858, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_4', '#skF_3'))=k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3332, c_16])).
% 14.76/6.83  tff(c_12877, plain, (k1_enumset1('#skF_3', '#skF_1', '#skF_4')=k2_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3332, c_22, c_12858])).
% 14.76/6.83  tff(c_12959, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski('#skF_3'))=k2_tarski('#skF_1', '#skF_4') | '#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12877, c_20])).
% 14.76/6.83  tff(c_12979, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski('#skF_3'))=k2_tarski('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_3778, c_12959])).
% 14.76/6.83  tff(c_2515, plain, (![A_28, C_119]: (k2_xboole_0(k1_tarski(A_28), k2_tarski(C_119, A_28))=k2_tarski(A_28, C_119))), inference(demodulation, [status(thm), theory('equality')], [c_1869, c_1135])).
% 14.76/6.83  tff(c_860, plain, (![A_98, B_99, C_100]: (k2_xboole_0(k1_tarski(A_98), k1_enumset1(A_98, B_99, C_100))=k2_xboole_0(k1_tarski(A_98), k2_tarski(B_99, C_100)))), inference(superposition, [status(thm), theory('equality')], [c_854, c_16])).
% 14.76/6.83  tff(c_877, plain, (![A_98, B_99, C_100]: (k2_xboole_0(k1_tarski(A_98), k1_enumset1(A_98, B_99, C_100))=k1_enumset1(A_98, B_99, C_100))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_860])).
% 14.76/6.83  tff(c_12956, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_3'))=k1_enumset1('#skF_3', '#skF_1', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12877, c_877])).
% 14.76/6.83  tff(c_12978, plain, (k2_tarski('#skF_1', '#skF_3')=k2_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12877, c_3354, c_2515, c_12956])).
% 14.76/6.83  tff(c_13076, plain, (![C_22]: (k2_xboole_0(k2_tarski('#skF_4', '#skF_3'), k2_tarski(C_22, '#skF_3'))=k1_enumset1('#skF_3', '#skF_1', C_22))), inference(superposition, [status(thm), theory('equality')], [c_12978, c_22])).
% 14.76/6.83  tff(c_14678, plain, (![C_360]: (k1_enumset1('#skF_3', '#skF_1', C_360)=k1_enumset1('#skF_3', '#skF_4', C_360))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_13076])).
% 14.76/6.83  tff(c_14691, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_4')=k2_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14678, c_12877])).
% 14.76/6.83  tff(c_14820, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_4') | '#skF_3'='#skF_4' | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_14691, c_20])).
% 14.76/6.83  tff(c_14848, plain, (k2_tarski('#skF_1', '#skF_4')=k1_tarski('#skF_4') | '#skF_3'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12979, c_28, c_14820])).
% 14.76/6.83  tff(c_14849, plain, (k2_tarski('#skF_1', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3778, c_3778, c_14848])).
% 14.76/6.83  tff(c_14996, plain, (![A_33]: ('#skF_1'='#skF_4' | k1_tarski(A_33)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14849, c_38])).
% 14.76/6.83  tff(c_15014, plain, (![A_33]: (k1_tarski(A_33)!=k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_14996])).
% 14.76/6.83  tff(c_15019, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_15014])).
% 14.76/6.83  tff(c_15021, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_2036])).
% 14.76/6.83  tff(c_15023, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15022, c_15021])).
% 14.76/6.83  tff(c_15028, plain, (k1_enumset1('#skF_4', '#skF_1', '#skF_4')=k2_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15022, c_2594])).
% 14.76/6.83  tff(c_15050, plain, (k2_tarski('#skF_4', '#skF_3')=k2_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2531, c_15028])).
% 14.76/6.83  tff(c_15223, plain, (![A_33]: ('#skF_3'='#skF_4' | k2_tarski('#skF_4', '#skF_1')!=k1_tarski(A_33))), inference(superposition, [status(thm), theory('equality')], [c_15050, c_38])).
% 14.76/6.83  tff(c_15230, plain, (![A_33]: (k2_tarski('#skF_4', '#skF_1')!=k1_tarski(A_33))), inference(negUnitSimplification, [status(thm)], [c_15023, c_15223])).
% 14.76/6.83  tff(c_1129, plain, (![C_119]: (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski(C_119, '#skF_4'))=k1_enumset1('#skF_4', '#skF_3', C_119))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1108])).
% 14.76/6.83  tff(c_15030, plain, (![C_119]: (k2_xboole_0(k2_tarski('#skF_1', '#skF_4'), k2_tarski(C_119, '#skF_4'))=k1_enumset1('#skF_4', '#skF_3', C_119))), inference(demodulation, [status(thm), theory('equality')], [c_15022, c_1129])).
% 14.76/6.83  tff(c_16352, plain, (![C_394]: (k1_enumset1('#skF_4', '#skF_3', C_394)=k1_enumset1('#skF_4', '#skF_1', C_394))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_15030])).
% 14.76/6.83  tff(c_875, plain, (![A_98, A_28]: (k2_xboole_0(k1_tarski(A_98), k1_tarski(A_28))=k1_enumset1(A_98, A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_28, c_854])).
% 14.76/6.83  tff(c_880, plain, (![A_98, A_28]: (k1_enumset1(A_98, A_28, A_28)=k2_tarski(A_98, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_875])).
% 14.76/6.83  tff(c_16381, plain, (k1_enumset1('#skF_4', '#skF_1', '#skF_3')=k2_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16352, c_880])).
% 14.76/6.83  tff(c_16403, plain, (k1_enumset1('#skF_4', '#skF_1', '#skF_3')=k2_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15050, c_16381])).
% 14.76/6.83  tff(c_16446, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_1'), k1_tarski('#skF_4'))=k2_tarski('#skF_1', '#skF_3') | '#skF_3'='#skF_4' | '#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16403, c_20])).
% 14.76/6.83  tff(c_16462, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_1'), k1_tarski('#skF_4'))=k2_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_15023, c_16446])).
% 14.76/6.83  tff(c_1132, plain, (![B_117]: (k2_xboole_0(k2_tarski(B_117, '#skF_4'), k2_tarski('#skF_1', '#skF_2'))=k1_enumset1('#skF_4', B_117, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1108])).
% 14.76/6.83  tff(c_15035, plain, (![B_117]: (k2_xboole_0(k2_tarski(B_117, '#skF_4'), k2_tarski('#skF_1', '#skF_4'))=k1_enumset1('#skF_4', B_117, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15022, c_1132])).
% 14.76/6.83  tff(c_16598, plain, (![B_400]: (k1_enumset1('#skF_4', B_400, '#skF_3')=k1_enumset1('#skF_4', B_400, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_15035])).
% 14.76/6.83  tff(c_16641, plain, (k1_enumset1('#skF_4', '#skF_3', '#skF_1')=k2_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16598, c_880])).
% 14.76/6.83  tff(c_16675, plain, (k1_enumset1('#skF_4', '#skF_3', '#skF_1')=k2_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15050, c_16641])).
% 14.76/6.83  tff(c_16745, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_1'), k1_tarski('#skF_4'))=k2_tarski('#skF_3', '#skF_1') | '#skF_1'='#skF_4' | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16675, c_20])).
% 14.76/6.83  tff(c_16765, plain, (k2_tarski('#skF_3', '#skF_1')=k2_tarski('#skF_1', '#skF_3') | '#skF_1'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16462, c_16745])).
% 14.76/6.83  tff(c_16766, plain, (k2_tarski('#skF_3', '#skF_1')=k2_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_15023, c_40, c_16765])).
% 14.76/6.83  tff(c_56, plain, (![A_38, B_39]: (r1_tarski(k4_xboole_0(A_38, B_39), A_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.76/6.83  tff(c_59, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_56])).
% 14.76/6.83  tff(c_498, plain, (![A_83, B_84, C_85]: (r1_tarski(k4_xboole_0(A_83, B_84), C_85) | ~r1_tarski(A_83, k2_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.76/6.83  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.76/6.83  tff(c_15555, plain, (![A_374, B_375, C_376]: (k4_xboole_0(k4_xboole_0(A_374, B_375), C_376)=k1_xboole_0 | ~r1_tarski(A_374, k2_xboole_0(B_375, C_376)))), inference(resolution, [status(thm)], [c_498, c_4])).
% 14.76/6.83  tff(c_15872, plain, (![B_384, C_385]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_384, C_385), B_384), C_385)=k1_xboole_0)), inference(resolution, [status(thm)], [c_59, c_15555])).
% 14.76/6.83  tff(c_15927, plain, (![B_384]: (k4_xboole_0(k2_xboole_0(B_384, k1_xboole_0), B_384)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15872, c_12])).
% 14.76/6.83  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.76/6.83  tff(c_543, plain, (![A_86, A_87, B_88]: (r1_tarski(A_86, A_87) | ~r1_tarski(A_86, k4_xboole_0(A_87, B_88)))), inference(resolution, [status(thm)], [c_10, c_359])).
% 14.76/6.83  tff(c_18005, plain, (![A_425, A_426, B_427]: (r1_tarski(A_425, A_426) | k4_xboole_0(A_425, k4_xboole_0(A_426, B_427))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_543])).
% 14.76/6.83  tff(c_18163, plain, (![A_428, B_429]: (r1_tarski(k2_xboole_0(k4_xboole_0(A_428, B_429), k1_xboole_0), A_428))), inference(superposition, [status(thm), theory('equality')], [c_15927, c_18005])).
% 14.76/6.83  tff(c_18306, plain, (![A_430]: (r1_tarski(k2_xboole_0(A_430, k1_xboole_0), A_430))), inference(superposition, [status(thm), theory('equality')], [c_12, c_18163])).
% 14.76/6.83  tff(c_421, plain, (![A_3, A_78, A_77]: (r1_tarski(A_3, A_78) | ~r1_tarski(A_3, A_77) | k1_xboole_0!=A_77)), inference(resolution, [status(thm)], [c_404, c_6])).
% 14.76/6.83  tff(c_18363, plain, (![A_431, A_432]: (r1_tarski(k2_xboole_0(A_431, k1_xboole_0), A_432) | k1_xboole_0!=A_431)), inference(resolution, [status(thm)], [c_18306, c_421])).
% 14.76/6.83  tff(c_19190, plain, (![A_447, A_448]: (k4_xboole_0(k2_xboole_0(A_447, k1_xboole_0), A_448)=k1_xboole_0 | k1_xboole_0!=A_447)), inference(resolution, [status(thm)], [c_18363, c_4])).
% 14.76/6.83  tff(c_19386, plain, (![A_449]: (k2_xboole_0(A_449, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_449)), inference(superposition, [status(thm), theory('equality')], [c_19190, c_12])).
% 14.76/6.83  tff(c_96, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.76/6.83  tff(c_113, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_96])).
% 14.76/6.83  tff(c_3058, plain, (![A_174, B_175, A_176]: (r1_tarski(A_174, B_175) | ~r1_tarski(A_174, A_176) | k4_xboole_0(A_176, B_175)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_359])).
% 14.76/6.83  tff(c_3191, plain, (![A_177, B_178, B_179]: (r1_tarski(A_177, B_178) | k4_xboole_0(k2_xboole_0(A_177, B_179), B_178)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_3058])).
% 14.76/6.83  tff(c_3268, plain, (![A_180, B_181, B_182]: (r1_tarski(A_180, k2_xboole_0(k2_xboole_0(A_180, B_181), B_182)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_3191])).
% 14.76/6.83  tff(c_3324, plain, (![A_180, B_181, B_182]: (k4_xboole_0(A_180, k2_xboole_0(k2_xboole_0(A_180, B_181), B_182))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3268, c_4])).
% 14.76/6.83  tff(c_19452, plain, (![A_180, B_181]: (k4_xboole_0(A_180, k1_xboole_0)=k1_xboole_0 | k2_xboole_0(A_180, B_181)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_19386, c_3324])).
% 14.76/6.83  tff(c_19572, plain, (![A_450, B_451]: (k1_xboole_0=A_450 | k2_xboole_0(A_450, B_451)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_19452])).
% 14.76/6.83  tff(c_19612, plain, (![A_452, C_453]: (k1_tarski(A_452)=k1_xboole_0 | k2_tarski(A_452, C_453)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2515, c_19572])).
% 14.76/6.83  tff(c_19621, plain, (k1_tarski('#skF_3')=k1_xboole_0 | k2_tarski('#skF_1', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16766, c_19612])).
% 14.76/6.83  tff(c_19628, plain, (k2_tarski('#skF_1', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_19621])).
% 14.76/6.83  tff(c_16836, plain, (![A_33]: ('#skF_3'='#skF_1' | k2_tarski('#skF_1', '#skF_3')!=k1_tarski(A_33))), inference(superposition, [status(thm), theory('equality')], [c_16766, c_38])).
% 14.76/6.83  tff(c_16851, plain, (![A_33]: (k2_tarski('#skF_1', '#skF_3')!=k1_tarski(A_33))), inference(negUnitSimplification, [status(thm)], [c_42, c_16836])).
% 14.76/6.83  tff(c_15659, plain, (![B_375, C_376]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_375, C_376), B_375), C_376)=k1_xboole_0)), inference(resolution, [status(thm)], [c_59, c_15555])).
% 14.76/6.83  tff(c_26505, plain, (![B_545, A_546, B_547]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_545, k4_xboole_0(A_546, B_547)), B_545), A_546))), inference(superposition, [status(thm), theory('equality')], [c_15659, c_18005])).
% 14.76/6.83  tff(c_26777, plain, (![B_548, A_549]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_548, A_549), B_548), A_549))), inference(superposition, [status(thm), theory('equality')], [c_12, c_26505])).
% 14.76/6.83  tff(c_29736, plain, (![A_609, B_610]: (r1_tarski(k4_xboole_0(k2_tarski(A_609, B_610), k1_tarski(A_609)), k1_tarski(B_610)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_26777])).
% 14.76/6.83  tff(c_29766, plain, (r1_tarski(k4_xboole_0(k2_tarski('#skF_4', '#skF_1'), k1_tarski('#skF_4')), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_15050, c_29736])).
% 14.76/6.83  tff(c_29780, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_3'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16462, c_29766])).
% 14.76/6.83  tff(c_30, plain, (![B_30, A_29]: (k1_tarski(B_30)=A_29 | k1_xboole_0=A_29 | ~r1_tarski(A_29, k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.76/6.83  tff(c_29794, plain, (k2_tarski('#skF_1', '#skF_3')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_29780, c_30])).
% 14.76/6.83  tff(c_29807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19628, c_16851, c_29794])).
% 14.76/6.83  tff(c_29808, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_19621])).
% 14.76/6.83  tff(c_36, plain, (![B_32, A_31]: (B_32=A_31 | ~r1_tarski(k1_tarski(A_31), k1_tarski(B_32)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.76/6.83  tff(c_424, plain, (![B_32, A_31]: (B_32=A_31 | k1_tarski(A_31)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_404, c_36])).
% 14.76/6.83  tff(c_30094, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_29808, c_424])).
% 14.76/6.83  tff(c_15034, plain, (k1_enumset1('#skF_3', '#skF_1', '#skF_4')=k2_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15022, c_15022, c_1946])).
% 14.76/6.83  tff(c_15445, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_4'), k1_tarski('#skF_3'))=k2_tarski('#skF_1', '#skF_4') | '#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_15034, c_20])).
% 14.76/6.83  tff(c_15458, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_4'), k1_tarski('#skF_3'))=k2_tarski('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_15023, c_15445])).
% 14.76/6.83  tff(c_15048, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15022, c_44])).
% 14.76/6.83  tff(c_15214, plain, (![A_25]: (k2_xboole_0(k1_tarski(A_25), k2_tarski('#skF_4', '#skF_1'))=k1_enumset1(A_25, '#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_15050, c_26])).
% 14.76/6.83  tff(c_17319, plain, (![A_417]: (k1_enumset1(A_417, '#skF_4', '#skF_3')=k1_enumset1(A_417, '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_15214])).
% 14.76/6.83  tff(c_17345, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_1')=k2_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17319, c_2531])).
% 14.76/6.83  tff(c_17384, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_1')=k2_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15048, c_17345])).
% 14.76/6.83  tff(c_17412, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_4'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_1') | '#skF_3'='#skF_1' | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_17384, c_20])).
% 14.76/6.83  tff(c_17430, plain, (k2_tarski('#skF_1', '#skF_4')=k2_tarski('#skF_4', '#skF_1') | '#skF_3'='#skF_1' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15458, c_17412])).
% 14.76/6.83  tff(c_17431, plain, (k2_tarski('#skF_1', '#skF_4')=k2_tarski('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_15023, c_42, c_17430])).
% 14.76/6.83  tff(c_17442, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17431, c_15048])).
% 14.76/6.83  tff(c_30095, plain, (k2_tarski('#skF_4', '#skF_1')=k2_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30094, c_17442])).
% 14.76/6.83  tff(c_30523, plain, (k2_tarski('#skF_4', '#skF_1')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30095])).
% 14.76/6.83  tff(c_30525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15230, c_30523])).
% 14.76/6.83  tff(c_30526, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski('#skF_4'))=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_2677])).
% 14.76/6.83  tff(c_31181, plain, (![A_1883, B_1884, C_1885]: (k4_xboole_0(k4_xboole_0(A_1883, B_1884), C_1885)=k1_xboole_0 | ~r1_tarski(A_1883, k2_xboole_0(B_1884, C_1885)))), inference(resolution, [status(thm)], [c_498, c_4])).
% 14.76/6.83  tff(c_31302, plain, (![B_1884, C_1885]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_1884, C_1885), B_1884), C_1885)=k1_xboole_0)), inference(resolution, [status(thm)], [c_59, c_31181])).
% 14.76/6.83  tff(c_33064, plain, (![A_1925, A_1926, B_1927]: (r1_tarski(A_1925, A_1926) | k4_xboole_0(A_1925, k4_xboole_0(A_1926, B_1927))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_543])).
% 14.76/6.83  tff(c_42634, plain, (![B_2044, A_2045, B_2046]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_2044, k4_xboole_0(A_2045, B_2046)), B_2044), A_2045))), inference(superposition, [status(thm), theory('equality')], [c_31302, c_33064])).
% 14.76/6.83  tff(c_43034, plain, (![B_2048, A_2049]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_2048, A_2049), B_2048), A_2049))), inference(superposition, [status(thm), theory('equality')], [c_12, c_42634])).
% 14.76/6.83  tff(c_50050, plain, (![A_2146, B_2147]: (r1_tarski(k4_xboole_0(k2_tarski(A_2146, B_2147), k1_tarski(A_2146)), k1_tarski(B_2147)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_43034])).
% 14.76/6.83  tff(c_50070, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_30526, c_50050])).
% 14.76/6.83  tff(c_50110, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_50070, c_30])).
% 14.76/6.83  tff(c_50124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1857, c_246, c_50110])).
% 14.76/6.83  tff(c_50169, plain, (![A_2150]: (r1_tarski(k1_tarski('#skF_3'), A_2150))), inference(splitRight, [status(thm)], [c_1435])).
% 14.76/6.83  tff(c_50505, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_50169, c_36])).
% 14.76/6.83  tff(c_50506, plain, (k2_tarski('#skF_1', '#skF_2')=k2_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50505, c_44])).
% 14.76/6.83  tff(c_50537, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_50506])).
% 14.76/6.83  tff(c_50539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_50537])).
% 14.76/6.83  tff(c_50540, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_80])).
% 14.76/6.83  tff(c_50541, plain, (k2_tarski('#skF_1', '#skF_2')=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50540, c_44])).
% 14.76/6.83  tff(c_50543, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_50541])).
% 14.76/6.83  tff(c_50555, plain, (![A_2812, B_2813]: (r1_tarski(k1_tarski(A_2812), k2_tarski(A_2812, B_2813)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_18])).
% 14.76/6.83  tff(c_50561, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_50543, c_50555])).
% 14.76/6.83  tff(c_50572, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_50561, c_36])).
% 14.76/6.83  tff(c_50577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_50572])).
% 14.76/6.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.76/6.83  
% 14.76/6.83  Inference rules
% 14.76/6.83  ----------------------
% 14.76/6.83  #Ref     : 2
% 14.76/6.83  #Sup     : 12646
% 14.76/6.83  #Fact    : 4
% 14.76/6.84  #Define  : 0
% 14.76/6.84  #Split   : 19
% 14.76/6.84  #Chain   : 0
% 14.76/6.84  #Close   : 0
% 14.76/6.84  
% 14.76/6.84  Ordering : KBO
% 14.76/6.84  
% 14.76/6.84  Simplification rules
% 14.76/6.84  ----------------------
% 14.76/6.84  #Subsume      : 2358
% 14.76/6.84  #Demod        : 9327
% 14.76/6.84  #Tautology    : 7423
% 14.76/6.84  #SimpNegUnit  : 346
% 14.76/6.84  #BackRed      : 238
% 14.76/6.84  
% 14.76/6.84  #Partial instantiations: 378
% 14.76/6.84  #Strategies tried      : 1
% 14.76/6.84  
% 14.76/6.84  Timing (in seconds)
% 14.76/6.84  ----------------------
% 14.76/6.84  Preprocessing        : 0.30
% 14.76/6.84  Parsing              : 0.16
% 14.76/6.84  CNF conversion       : 0.02
% 14.76/6.84  Main loop            : 5.76
% 14.76/6.84  Inferencing          : 1.04
% 14.76/6.84  Reduction            : 3.12
% 14.76/6.84  Demodulation         : 2.67
% 14.76/6.84  BG Simplification    : 0.09
% 14.76/6.84  Subsumption          : 1.23
% 14.76/6.84  Abstraction          : 0.15
% 14.76/6.84  MUC search           : 0.00
% 14.76/6.84  Cooper               : 0.00
% 14.76/6.84  Total                : 6.12
% 14.76/6.84  Index Insertion      : 0.00
% 14.76/6.84  Index Deletion       : 0.00
% 14.76/6.84  Index Matching       : 0.00
% 14.76/6.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------

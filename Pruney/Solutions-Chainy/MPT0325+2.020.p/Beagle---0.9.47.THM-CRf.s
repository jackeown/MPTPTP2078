%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:23 EST 2020

% Result     : Theorem 43.39s
% Output     : CNFRefutation 43.39s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 376 expanded)
%              Number of leaves         :   31 ( 132 expanded)
%              Depth                    :   11
%              Number of atoms          :  146 ( 570 expanded)
%              Number of equality atoms :   62 ( 239 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_114,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_38,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_132,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_145,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_1621,plain,(
    ! [A_122,C_123,B_124,D_125] : k3_xboole_0(k2_zfmisc_1(A_122,C_123),k2_zfmisc_1(B_124,D_125)) = k2_zfmisc_1(k3_xboole_0(A_122,B_124),k3_xboole_0(C_123,D_125)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1722,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_1621])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13799,plain,(
    ! [A_219,B_220,C_221,D_222] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_219,B_220),k3_xboole_0(C_221,D_222)),k2_zfmisc_1(A_219,C_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_18])).

tff(c_18225,plain,(
    ! [A_248,C_249,D_250] : r1_tarski(k2_zfmisc_1(A_248,k3_xboole_0(C_249,D_250)),k2_zfmisc_1(A_248,C_249)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_13799])).

tff(c_18342,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1722,c_18225])).

tff(c_26,plain,(
    ! [B_25,A_24,C_26] :
      ( ~ r1_tarski(k2_zfmisc_1(B_25,A_24),k2_zfmisc_1(C_26,A_24))
      | r1_tarski(B_25,C_26)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20615,plain,
    ( r1_tarski('#skF_3',k3_xboole_0('#skF_3','#skF_5'))
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18342,c_26])).

tff(c_20617,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_20615])).

tff(c_22,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_168,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_189,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_168])).

tff(c_193,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_189])).

tff(c_959,plain,(
    ! [C_91,A_92,B_93] : k4_xboole_0(k2_zfmisc_1(C_91,A_92),k2_zfmisc_1(C_91,B_93)) = k2_zfmisc_1(C_91,k4_xboole_0(A_92,B_93)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_966,plain,(
    ! [C_91,B_93] : k2_zfmisc_1(C_91,k4_xboole_0(B_93,B_93)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_193])).

tff(c_975,plain,(
    ! [C_91] : k2_zfmisc_1(C_91,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_966])).

tff(c_20991,plain,(
    ! [C_91] : k2_zfmisc_1(C_91,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20617,c_20617,c_975])).

tff(c_36,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_21007,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20617,c_36])).

tff(c_21464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20991,c_21007])).

tff(c_21465,plain,(
    r1_tarski('#skF_3',k3_xboole_0('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_20615])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_21550,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_21465,c_20])).

tff(c_266,plain,(
    ! [A_62,B_63,C_64] : k3_xboole_0(k3_xboole_0(A_62,B_63),C_64) = k3_xboole_0(A_62,k3_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_60,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,A_40) = k3_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [B_39,A_40] : r1_tarski(k3_xboole_0(B_39,A_40),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_18])).

tff(c_287,plain,(
    ! [A_62,B_63,C_64] : r1_tarski(k3_xboole_0(A_62,k3_xboole_0(B_63,C_64)),C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_75])).

tff(c_21785,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_21550,c_287])).

tff(c_21878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_21785])).

tff(c_21879,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_21880,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_21898,plain,(
    ! [A_285,B_286] :
      ( k3_xboole_0(A_285,B_286) = A_285
      | ~ r1_tarski(A_285,B_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_21915,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_21880,c_21898])).

tff(c_23603,plain,(
    ! [A_352,C_353,B_354,D_355] : k3_xboole_0(k2_zfmisc_1(A_352,C_353),k2_zfmisc_1(B_354,D_355)) = k2_zfmisc_1(k3_xboole_0(A_352,B_354),k3_xboole_0(C_353,D_355)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_21914,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_21898])).

tff(c_23647,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_23603,c_21914])).

tff(c_23707,plain,(
    k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21915,c_23647])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39183,plain,(
    ! [A_467,B_468,C_469,D_470] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_467,B_468),k3_xboole_0(C_469,D_470)),k2_zfmisc_1(A_467,C_469)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23603,c_18])).

tff(c_110589,plain,(
    ! [A_766,B_767,A_768,B_769] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_766,B_767),k3_xboole_0(A_768,B_769)),k2_zfmisc_1(A_766,B_769)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_39183])).

tff(c_169339,plain,(
    ! [A_893,B_894] : r1_tarski(k2_zfmisc_1('#skF_3',k3_xboole_0(A_893,B_894)),k2_zfmisc_1('#skF_3',B_894)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21915,c_110589])).

tff(c_169690,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_3','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23707,c_169339])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_tarski(k2_zfmisc_1(A_24,B_25),k2_zfmisc_1(A_24,C_26))
      | r1_tarski(B_25,C_26)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_169854,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_169690,c_24])).

tff(c_169860,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_21879,c_169854])).

tff(c_21881,plain,(
    ! [A_282,B_283] : r1_xboole_0(k3_xboole_0(A_282,B_283),k5_xboole_0(A_282,B_283)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_21890,plain,(
    ! [A_3] : r1_xboole_0(A_3,k5_xboole_0(A_3,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_21881])).

tff(c_21894,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_21890])).

tff(c_21997,plain,(
    ! [A_292,B_293,C_294] :
      ( ~ r1_xboole_0(A_292,B_293)
      | ~ r2_hidden(C_294,k3_xboole_0(A_292,B_293)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22040,plain,(
    ! [A_295,C_296] :
      ( ~ r1_xboole_0(A_295,A_295)
      | ~ r2_hidden(C_296,A_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_21997])).

tff(c_22044,plain,(
    ! [C_296] : ~ r2_hidden(C_296,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_21894,c_22040])).

tff(c_22053,plain,(
    ! [A_298,B_299] :
      ( ~ r1_xboole_0(A_298,B_299)
      | k3_xboole_0(A_298,B_299) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_21997])).

tff(c_22095,plain,(
    ! [A_302] : k3_xboole_0(A_302,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21894,c_22053])).

tff(c_22157,plain,(
    ! [A_304] : k3_xboole_0(k1_xboole_0,A_304) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22095,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22165,plain,(
    ! [A_304] :
      ( r2_hidden('#skF_1'(k1_xboole_0,A_304),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22157,c_6])).

tff(c_22213,plain,(
    ! [A_304] : r1_xboole_0(k1_xboole_0,A_304) ),
    inference(negUnitSimplification,[status(thm)],[c_22044,c_22165])).

tff(c_169963,plain,(
    ! [A_304] : r1_xboole_0('#skF_3',A_304) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169860,c_22213])).

tff(c_22000,plain,(
    ! [C_294] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_294,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21915,c_21997])).

tff(c_22052,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_22000])).

tff(c_22074,plain,(
    ! [A_300,B_301] :
      ( r2_hidden('#skF_1'(A_300,B_301),k3_xboole_0(A_300,B_301))
      | r1_xboole_0(A_300,B_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22089,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_1'(B_2,A_1),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22074])).

tff(c_22243,plain,(
    ! [A_306,B_307,C_308] : k3_xboole_0(k3_xboole_0(A_306,B_307),C_308) = k3_xboole_0(A_306,k3_xboole_0(B_307,C_308)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40195,plain,(
    ! [A_475,B_476,C_477,C_478] :
      ( ~ r1_xboole_0(k3_xboole_0(A_475,B_476),C_477)
      | ~ r2_hidden(C_478,k3_xboole_0(A_475,k3_xboole_0(B_476,C_477))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22243,c_8])).

tff(c_95682,plain,(
    ! [A_704,B_705,C_706] :
      ( ~ r1_xboole_0(k3_xboole_0(A_704,B_705),C_706)
      | r1_xboole_0(k3_xboole_0(B_705,C_706),A_704) ) ),
    inference(resolution,[status(thm)],[c_22089,c_40195])).

tff(c_97091,plain,(
    ! [C_711] :
      ( ~ r1_xboole_0('#skF_3',C_711)
      | r1_xboole_0(k3_xboole_0('#skF_5',C_711),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21915,c_95682])).

tff(c_40487,plain,(
    ! [A_1,B_476,C_477] :
      ( ~ r1_xboole_0(k3_xboole_0(A_1,B_476),C_477)
      | r1_xboole_0(k3_xboole_0(B_476,C_477),A_1) ) ),
    inference(resolution,[status(thm)],[c_22089,c_40195])).

tff(c_97812,plain,(
    ! [C_715] :
      ( r1_xboole_0(k3_xboole_0(C_715,'#skF_3'),'#skF_5')
      | ~ r1_xboole_0('#skF_3',C_715) ) ),
    inference(resolution,[status(thm)],[c_97091,c_40487])).

tff(c_97936,plain,
    ( r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_97812])).

tff(c_97978,plain,(
    ~ r1_xboole_0('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_22052,c_97936])).

tff(c_170021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169963,c_97978])).

tff(c_170024,plain,(
    ! [C_895] : ~ r2_hidden(C_895,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_22000])).

tff(c_170029,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_170024])).

tff(c_21956,plain,(
    ! [A_289,B_290] : k5_xboole_0(A_289,k3_xboole_0(A_289,B_290)) = k4_xboole_0(A_289,B_290) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_21980,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_21956])).

tff(c_21985,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_21980])).

tff(c_170032,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170029,c_21985])).

tff(c_170393,plain,(
    ! [C_912,A_913,B_914] : k4_xboole_0(k2_zfmisc_1(C_912,A_913),k2_zfmisc_1(C_912,B_914)) = k2_zfmisc_1(C_912,k4_xboole_0(A_913,B_914)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_170400,plain,(
    ! [C_912,B_914] : k2_zfmisc_1(C_912,k4_xboole_0(B_914,B_914)) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_170393,c_170032])).

tff(c_170409,plain,(
    ! [C_912] : k2_zfmisc_1(C_912,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170032,c_170400])).

tff(c_170617,plain,(
    ! [A_927,C_928,B_929] : k4_xboole_0(k2_zfmisc_1(A_927,C_928),k2_zfmisc_1(B_929,C_928)) = k2_zfmisc_1(k4_xboole_0(A_927,B_929),C_928) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [C_33,A_31,B_32] : k4_xboole_0(k2_zfmisc_1(C_33,A_31),k2_zfmisc_1(C_33,B_32)) = k2_zfmisc_1(C_33,k4_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_170624,plain,(
    ! [B_929,C_928] : k2_zfmisc_1(k4_xboole_0(B_929,B_929),C_928) = k2_zfmisc_1(B_929,k4_xboole_0(C_928,C_928)) ),
    inference(superposition,[status(thm),theory(equality)],[c_170617,c_32])).

tff(c_170647,plain,(
    ! [C_928] : k2_zfmisc_1('#skF_3',C_928) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170409,c_170032,c_170032,c_170624])).

tff(c_170036,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170029,c_36])).

tff(c_170664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170647,c_170036])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:34:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.39/33.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.39/33.12  
% 43.39/33.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.39/33.12  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 43.39/33.12  
% 43.39/33.12  %Foreground sorts:
% 43.39/33.12  
% 43.39/33.12  
% 43.39/33.12  %Background operators:
% 43.39/33.12  
% 43.39/33.12  
% 43.39/33.12  %Foreground operators:
% 43.39/33.12  tff('#skF_2', type, '#skF_2': $i > $i).
% 43.39/33.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.39/33.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 43.39/33.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 43.39/33.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 43.39/33.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 43.39/33.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 43.39/33.12  tff('#skF_5', type, '#skF_5': $i).
% 43.39/33.12  tff('#skF_6', type, '#skF_6': $i).
% 43.39/33.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 43.39/33.12  tff('#skF_3', type, '#skF_3': $i).
% 43.39/33.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.39/33.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 43.39/33.12  tff('#skF_4', type, '#skF_4': $i).
% 43.39/33.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.39/33.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 43.39/33.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 43.39/33.12  
% 43.39/33.14  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 43.39/33.14  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 43.39/33.14  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 43.39/33.14  tff(f_78, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 43.39/33.14  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 43.39/33.14  tff(f_59, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 43.39/33.14  tff(f_76, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 43.39/33.14  tff(f_65, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 43.39/33.14  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 43.39/33.14  tff(f_82, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 43.39/33.14  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 43.39/33.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 43.39/33.14  tff(f_53, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 43.39/33.14  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 43.39/33.14  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 43.39/33.14  tff(c_34, plain, (~r1_tarski('#skF_4', '#skF_6') | ~r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 43.39/33.14  tff(c_114, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_34])).
% 43.39/33.14  tff(c_38, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 43.39/33.14  tff(c_132, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 43.39/33.14  tff(c_145, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_132])).
% 43.39/33.14  tff(c_1621, plain, (![A_122, C_123, B_124, D_125]: (k3_xboole_0(k2_zfmisc_1(A_122, C_123), k2_zfmisc_1(B_124, D_125))=k2_zfmisc_1(k3_xboole_0(A_122, B_124), k3_xboole_0(C_123, D_125)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 43.39/33.14  tff(c_1722, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_145, c_1621])).
% 43.39/33.14  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 43.39/33.14  tff(c_18, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 43.39/33.14  tff(c_13799, plain, (![A_219, B_220, C_221, D_222]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_219, B_220), k3_xboole_0(C_221, D_222)), k2_zfmisc_1(A_219, C_221)))), inference(superposition, [status(thm), theory('equality')], [c_1621, c_18])).
% 43.39/33.14  tff(c_18225, plain, (![A_248, C_249, D_250]: (r1_tarski(k2_zfmisc_1(A_248, k3_xboole_0(C_249, D_250)), k2_zfmisc_1(A_248, C_249)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_13799])).
% 43.39/33.14  tff(c_18342, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1722, c_18225])).
% 43.39/33.14  tff(c_26, plain, (![B_25, A_24, C_26]: (~r1_tarski(k2_zfmisc_1(B_25, A_24), k2_zfmisc_1(C_26, A_24)) | r1_tarski(B_25, C_26) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_76])).
% 43.39/33.14  tff(c_20615, plain, (r1_tarski('#skF_3', k3_xboole_0('#skF_3', '#skF_5')) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18342, c_26])).
% 43.39/33.14  tff(c_20617, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_20615])).
% 43.39/33.14  tff(c_22, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 43.39/33.14  tff(c_168, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 43.39/33.14  tff(c_189, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_168])).
% 43.39/33.14  tff(c_193, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_189])).
% 43.39/33.14  tff(c_959, plain, (![C_91, A_92, B_93]: (k4_xboole_0(k2_zfmisc_1(C_91, A_92), k2_zfmisc_1(C_91, B_93))=k2_zfmisc_1(C_91, k4_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.39/33.14  tff(c_966, plain, (![C_91, B_93]: (k2_zfmisc_1(C_91, k4_xboole_0(B_93, B_93))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_959, c_193])).
% 43.39/33.14  tff(c_975, plain, (![C_91]: (k2_zfmisc_1(C_91, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_193, c_966])).
% 43.39/33.14  tff(c_20991, plain, (![C_91]: (k2_zfmisc_1(C_91, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20617, c_20617, c_975])).
% 43.39/33.14  tff(c_36, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 43.39/33.14  tff(c_21007, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20617, c_36])).
% 43.39/33.14  tff(c_21464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20991, c_21007])).
% 43.39/33.14  tff(c_21465, plain, (r1_tarski('#skF_3', k3_xboole_0('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_20615])).
% 43.39/33.14  tff(c_20, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 43.39/33.14  tff(c_21550, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_21465, c_20])).
% 43.39/33.14  tff(c_266, plain, (![A_62, B_63, C_64]: (k3_xboole_0(k3_xboole_0(A_62, B_63), C_64)=k3_xboole_0(A_62, k3_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 43.39/33.14  tff(c_60, plain, (![B_39, A_40]: (k3_xboole_0(B_39, A_40)=k3_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 43.39/33.14  tff(c_75, plain, (![B_39, A_40]: (r1_tarski(k3_xboole_0(B_39, A_40), A_40))), inference(superposition, [status(thm), theory('equality')], [c_60, c_18])).
% 43.39/33.14  tff(c_287, plain, (![A_62, B_63, C_64]: (r1_tarski(k3_xboole_0(A_62, k3_xboole_0(B_63, C_64)), C_64))), inference(superposition, [status(thm), theory('equality')], [c_266, c_75])).
% 43.39/33.14  tff(c_21785, plain, (r1_tarski('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_21550, c_287])).
% 43.39/33.14  tff(c_21878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_21785])).
% 43.39/33.14  tff(c_21879, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 43.39/33.14  tff(c_21880, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 43.39/33.14  tff(c_21898, plain, (![A_285, B_286]: (k3_xboole_0(A_285, B_286)=A_285 | ~r1_tarski(A_285, B_286))), inference(cnfTransformation, [status(thm)], [f_63])).
% 43.39/33.14  tff(c_21915, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_21880, c_21898])).
% 43.39/33.14  tff(c_23603, plain, (![A_352, C_353, B_354, D_355]: (k3_xboole_0(k2_zfmisc_1(A_352, C_353), k2_zfmisc_1(B_354, D_355))=k2_zfmisc_1(k3_xboole_0(A_352, B_354), k3_xboole_0(C_353, D_355)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 43.39/33.14  tff(c_21914, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_21898])).
% 43.39/33.14  tff(c_23647, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_23603, c_21914])).
% 43.39/33.14  tff(c_23707, plain, (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21915, c_23647])).
% 43.39/33.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 43.39/33.14  tff(c_39183, plain, (![A_467, B_468, C_469, D_470]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_467, B_468), k3_xboole_0(C_469, D_470)), k2_zfmisc_1(A_467, C_469)))), inference(superposition, [status(thm), theory('equality')], [c_23603, c_18])).
% 43.39/33.14  tff(c_110589, plain, (![A_766, B_767, A_768, B_769]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_766, B_767), k3_xboole_0(A_768, B_769)), k2_zfmisc_1(A_766, B_769)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_39183])).
% 43.39/33.14  tff(c_169339, plain, (![A_893, B_894]: (r1_tarski(k2_zfmisc_1('#skF_3', k3_xboole_0(A_893, B_894)), k2_zfmisc_1('#skF_3', B_894)))), inference(superposition, [status(thm), theory('equality')], [c_21915, c_110589])).
% 43.39/33.14  tff(c_169690, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_23707, c_169339])).
% 43.39/33.14  tff(c_24, plain, (![A_24, B_25, C_26]: (~r1_tarski(k2_zfmisc_1(A_24, B_25), k2_zfmisc_1(A_24, C_26)) | r1_tarski(B_25, C_26) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_76])).
% 43.39/33.14  tff(c_169854, plain, (r1_tarski('#skF_4', '#skF_6') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_169690, c_24])).
% 43.39/33.14  tff(c_169860, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_21879, c_169854])).
% 43.39/33.14  tff(c_21881, plain, (![A_282, B_283]: (r1_xboole_0(k3_xboole_0(A_282, B_283), k5_xboole_0(A_282, B_283)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 43.39/33.14  tff(c_21890, plain, (![A_3]: (r1_xboole_0(A_3, k5_xboole_0(A_3, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_21881])).
% 43.39/33.14  tff(c_21894, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_21890])).
% 43.39/33.14  tff(c_21997, plain, (![A_292, B_293, C_294]: (~r1_xboole_0(A_292, B_293) | ~r2_hidden(C_294, k3_xboole_0(A_292, B_293)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.39/33.14  tff(c_22040, plain, (![A_295, C_296]: (~r1_xboole_0(A_295, A_295) | ~r2_hidden(C_296, A_295))), inference(superposition, [status(thm), theory('equality')], [c_4, c_21997])).
% 43.39/33.14  tff(c_22044, plain, (![C_296]: (~r2_hidden(C_296, k1_xboole_0))), inference(resolution, [status(thm)], [c_21894, c_22040])).
% 43.39/33.14  tff(c_22053, plain, (![A_298, B_299]: (~r1_xboole_0(A_298, B_299) | k3_xboole_0(A_298, B_299)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_21997])).
% 43.39/33.14  tff(c_22095, plain, (![A_302]: (k3_xboole_0(A_302, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_21894, c_22053])).
% 43.39/33.14  tff(c_22157, plain, (![A_304]: (k3_xboole_0(k1_xboole_0, A_304)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22095, c_2])).
% 43.39/33.14  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.39/33.14  tff(c_22165, plain, (![A_304]: (r2_hidden('#skF_1'(k1_xboole_0, A_304), k1_xboole_0) | r1_xboole_0(k1_xboole_0, A_304))), inference(superposition, [status(thm), theory('equality')], [c_22157, c_6])).
% 43.39/33.14  tff(c_22213, plain, (![A_304]: (r1_xboole_0(k1_xboole_0, A_304))), inference(negUnitSimplification, [status(thm)], [c_22044, c_22165])).
% 43.39/33.14  tff(c_169963, plain, (![A_304]: (r1_xboole_0('#skF_3', A_304))), inference(demodulation, [status(thm), theory('equality')], [c_169860, c_22213])).
% 43.39/33.14  tff(c_22000, plain, (![C_294]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_294, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_21915, c_21997])).
% 43.39/33.14  tff(c_22052, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_22000])).
% 43.39/33.14  tff(c_22074, plain, (![A_300, B_301]: (r2_hidden('#skF_1'(A_300, B_301), k3_xboole_0(A_300, B_301)) | r1_xboole_0(A_300, B_301))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.39/33.14  tff(c_22089, plain, (![B_2, A_1]: (r2_hidden('#skF_1'(B_2, A_1), k3_xboole_0(A_1, B_2)) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22074])).
% 43.39/33.14  tff(c_22243, plain, (![A_306, B_307, C_308]: (k3_xboole_0(k3_xboole_0(A_306, B_307), C_308)=k3_xboole_0(A_306, k3_xboole_0(B_307, C_308)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 43.39/33.14  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.39/33.14  tff(c_40195, plain, (![A_475, B_476, C_477, C_478]: (~r1_xboole_0(k3_xboole_0(A_475, B_476), C_477) | ~r2_hidden(C_478, k3_xboole_0(A_475, k3_xboole_0(B_476, C_477))))), inference(superposition, [status(thm), theory('equality')], [c_22243, c_8])).
% 43.39/33.14  tff(c_95682, plain, (![A_704, B_705, C_706]: (~r1_xboole_0(k3_xboole_0(A_704, B_705), C_706) | r1_xboole_0(k3_xboole_0(B_705, C_706), A_704))), inference(resolution, [status(thm)], [c_22089, c_40195])).
% 43.39/33.14  tff(c_97091, plain, (![C_711]: (~r1_xboole_0('#skF_3', C_711) | r1_xboole_0(k3_xboole_0('#skF_5', C_711), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_21915, c_95682])).
% 43.39/33.14  tff(c_40487, plain, (![A_1, B_476, C_477]: (~r1_xboole_0(k3_xboole_0(A_1, B_476), C_477) | r1_xboole_0(k3_xboole_0(B_476, C_477), A_1))), inference(resolution, [status(thm)], [c_22089, c_40195])).
% 43.39/33.14  tff(c_97812, plain, (![C_715]: (r1_xboole_0(k3_xboole_0(C_715, '#skF_3'), '#skF_5') | ~r1_xboole_0('#skF_3', C_715))), inference(resolution, [status(thm)], [c_97091, c_40487])).
% 43.39/33.14  tff(c_97936, plain, (r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_97812])).
% 43.39/33.14  tff(c_97978, plain, (~r1_xboole_0('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_22052, c_97936])).
% 43.39/33.14  tff(c_170021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169963, c_97978])).
% 43.39/33.14  tff(c_170024, plain, (![C_895]: (~r2_hidden(C_895, '#skF_3'))), inference(splitRight, [status(thm)], [c_22000])).
% 43.39/33.14  tff(c_170029, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_10, c_170024])).
% 43.39/33.14  tff(c_21956, plain, (![A_289, B_290]: (k5_xboole_0(A_289, k3_xboole_0(A_289, B_290))=k4_xboole_0(A_289, B_290))), inference(cnfTransformation, [status(thm)], [f_55])).
% 43.39/33.14  tff(c_21980, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_21956])).
% 43.39/33.14  tff(c_21985, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_21980])).
% 43.39/33.14  tff(c_170032, plain, (![A_3]: (k4_xboole_0(A_3, A_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170029, c_21985])).
% 43.39/33.14  tff(c_170393, plain, (![C_912, A_913, B_914]: (k4_xboole_0(k2_zfmisc_1(C_912, A_913), k2_zfmisc_1(C_912, B_914))=k2_zfmisc_1(C_912, k4_xboole_0(A_913, B_914)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.39/33.14  tff(c_170400, plain, (![C_912, B_914]: (k2_zfmisc_1(C_912, k4_xboole_0(B_914, B_914))='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_170393, c_170032])).
% 43.39/33.14  tff(c_170409, plain, (![C_912]: (k2_zfmisc_1(C_912, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170032, c_170400])).
% 43.39/33.14  tff(c_170617, plain, (![A_927, C_928, B_929]: (k4_xboole_0(k2_zfmisc_1(A_927, C_928), k2_zfmisc_1(B_929, C_928))=k2_zfmisc_1(k4_xboole_0(A_927, B_929), C_928))), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.39/33.14  tff(c_32, plain, (![C_33, A_31, B_32]: (k4_xboole_0(k2_zfmisc_1(C_33, A_31), k2_zfmisc_1(C_33, B_32))=k2_zfmisc_1(C_33, k4_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.39/33.14  tff(c_170624, plain, (![B_929, C_928]: (k2_zfmisc_1(k4_xboole_0(B_929, B_929), C_928)=k2_zfmisc_1(B_929, k4_xboole_0(C_928, C_928)))), inference(superposition, [status(thm), theory('equality')], [c_170617, c_32])).
% 43.39/33.14  tff(c_170647, plain, (![C_928]: (k2_zfmisc_1('#skF_3', C_928)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170409, c_170032, c_170032, c_170624])).
% 43.39/33.14  tff(c_170036, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_170029, c_36])).
% 43.39/33.14  tff(c_170664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170647, c_170036])).
% 43.39/33.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.39/33.14  
% 43.39/33.14  Inference rules
% 43.39/33.14  ----------------------
% 43.39/33.14  #Ref     : 0
% 43.39/33.14  #Sup     : 42237
% 43.39/33.14  #Fact    : 0
% 43.39/33.14  #Define  : 0
% 43.39/33.14  #Split   : 10
% 43.39/33.14  #Chain   : 0
% 43.39/33.14  #Close   : 0
% 43.39/33.14  
% 43.39/33.14  Ordering : KBO
% 43.39/33.14  
% 43.39/33.14  Simplification rules
% 43.39/33.14  ----------------------
% 43.39/33.14  #Subsume      : 1899
% 43.39/33.14  #Demod        : 59285
% 43.39/33.14  #Tautology    : 23339
% 43.39/33.14  #SimpNegUnit  : 776
% 43.39/33.14  #BackRed      : 214
% 43.39/33.14  
% 43.39/33.14  #Partial instantiations: 0
% 43.39/33.14  #Strategies tried      : 1
% 43.39/33.14  
% 43.39/33.14  Timing (in seconds)
% 43.39/33.14  ----------------------
% 43.39/33.14  Preprocessing        : 0.36
% 43.39/33.14  Parsing              : 0.18
% 43.39/33.14  CNF conversion       : 0.02
% 43.39/33.14  Main loop            : 32.00
% 43.39/33.14  Inferencing          : 2.29
% 43.39/33.14  Reduction            : 23.35
% 43.39/33.14  Demodulation         : 21.94
% 43.39/33.14  BG Simplification    : 0.33
% 43.39/33.14  Subsumption          : 4.97
% 43.39/33.14  Abstraction          : 0.53
% 43.39/33.14  MUC search           : 0.00
% 43.39/33.14  Cooper               : 0.00
% 43.39/33.14  Total                : 32.41
% 43.39/33.14  Index Insertion      : 0.00
% 43.39/33.14  Index Deletion       : 0.00
% 43.39/33.14  Index Matching       : 0.00
% 43.39/33.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

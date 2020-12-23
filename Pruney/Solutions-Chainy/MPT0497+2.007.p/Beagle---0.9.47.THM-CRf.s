%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:40 EST 2020

% Result     : Theorem 15.29s
% Output     : CNFRefutation 15.39s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 197 expanded)
%              Number of leaves         :   39 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 281 expanded)
%              Number of equality atoms :   51 ( 146 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

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

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_477,plain,(
    ! [A_115,B_116] :
      ( r1_xboole_0(A_115,B_116)
      | k4_xboole_0(A_115,B_116) != A_115 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_116,plain,(
    r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4')
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_155,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_72])).

tff(c_70,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_371,plain,(
    ! [B_109,A_110] :
      ( k3_xboole_0(k1_relat_1(B_109),A_110) = k1_relat_1(k7_relat_1(B_109,A_110))
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_177,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_198,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_177])).

tff(c_201,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_198])).

tff(c_135,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = A_66
      | ~ r1_xboole_0(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_139,plain,(
    k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_116,c_135])).

tff(c_195,plain,(
    k4_xboole_0(k1_relat_1('#skF_5'),k1_relat_1('#skF_5')) = k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_177])).

tff(c_246,plain,(
    k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_195])).

tff(c_380,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_246])).

tff(c_411,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_380])).

tff(c_56,plain,(
    ! [A_49,B_50] :
      ( v1_relat_1(k7_relat_1(A_49,B_50))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    ! [B_55,A_54] :
      ( k3_xboole_0(k1_relat_1(B_55),A_54) = k1_relat_1(k7_relat_1(B_55,A_54))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_418,plain,(
    ! [A_54] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_5','#skF_4'),A_54)) = k3_xboole_0(k1_xboole_0,A_54)
      | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_68])).

tff(c_438,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_441,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_438])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_441])).

tff(c_447,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_64,plain,(
    ! [A_51] :
      ( k1_relat_1(A_51) != k1_xboole_0
      | k1_xboole_0 = A_51
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_450,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_447,c_64])).

tff(c_456,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_450])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_456])).

tff(c_460,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_481,plain,(
    k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4') != k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_477,c_460])).

tff(c_579,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_1'(A_140,B_141),A_140)
      | r1_tarski(A_140,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1783,plain,(
    ! [A_249,B_250,B_251] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_249,B_250),B_251),A_249)
      | r1_tarski(k4_xboole_0(A_249,B_250),B_251) ) ),
    inference(resolution,[status(thm)],[c_579,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1849,plain,(
    ! [A_249,B_250] : r1_tarski(k4_xboole_0(A_249,B_250),A_249) ),
    inference(resolution,[status(thm)],[c_1783,c_4])).

tff(c_60,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_459,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_554,plain,(
    ! [A_138,B_139] : k4_xboole_0(A_138,k4_xboole_0(A_138,B_139)) = k3_xboole_0(A_138,B_139) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_926,plain,(
    ! [A_176,B_177] : k4_xboole_0(A_176,k3_xboole_0(A_176,B_177)) = k3_xboole_0(A_176,k4_xboole_0(A_176,B_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_36])).

tff(c_50681,plain,(
    ! [B_908,A_909] :
      ( k4_xboole_0(k1_relat_1(B_908),k1_relat_1(k7_relat_1(B_908,A_909))) = k3_xboole_0(k1_relat_1(B_908),k4_xboole_0(k1_relat_1(B_908),A_909))
      | ~ v1_relat_1(B_908) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_926])).

tff(c_51119,plain,
    ( k3_xboole_0(k1_relat_1('#skF_5'),k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) = k4_xboole_0(k1_relat_1('#skF_5'),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_50681])).

tff(c_51150,plain,(
    k3_xboole_0(k1_relat_1('#skF_5'),k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_34,c_60,c_51119])).

tff(c_51375,plain,
    ( k1_relat_1(k7_relat_1('#skF_5',k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4'))) = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_51150])).

tff(c_51439,plain,(
    k1_relat_1(k7_relat_1('#skF_5',k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4'))) = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_51375])).

tff(c_531,plain,(
    ! [B_126,A_127] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_126,A_127)),A_127)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_537,plain,(
    ! [B_126,A_127] :
      ( k1_relat_1(k7_relat_1(B_126,A_127)) = A_127
      | ~ r1_tarski(A_127,k1_relat_1(k7_relat_1(B_126,A_127)))
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_531,c_26])).

tff(c_55197,plain,
    ( k1_relat_1(k7_relat_1('#skF_5',k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4'))) = k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_51439,c_537])).

tff(c_55261,plain,(
    k4_xboole_0(k1_relat_1('#skF_5'),'#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1849,c_51439,c_55197])).

tff(c_55263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_55261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.29/7.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.29/7.50  
% 15.29/7.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.29/7.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 15.29/7.50  
% 15.29/7.50  %Foreground sorts:
% 15.29/7.50  
% 15.29/7.50  
% 15.29/7.50  %Background operators:
% 15.29/7.50  
% 15.29/7.50  
% 15.29/7.50  %Foreground operators:
% 15.29/7.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.29/7.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.29/7.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.29/7.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.29/7.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.29/7.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.29/7.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.29/7.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.29/7.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.29/7.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.29/7.50  tff('#skF_5', type, '#skF_5': $i).
% 15.29/7.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.29/7.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.29/7.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.29/7.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.29/7.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.29/7.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.29/7.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.29/7.50  tff('#skF_4', type, '#skF_4': $i).
% 15.29/7.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.29/7.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.29/7.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.29/7.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.29/7.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.29/7.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.29/7.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.29/7.50  
% 15.39/7.51  tff(f_58, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.39/7.51  tff(f_102, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 15.39/7.51  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 15.39/7.51  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 15.39/7.51  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 15.39/7.51  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.39/7.51  tff(f_76, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 15.39/7.51  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 15.39/7.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.39/7.51  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 15.39/7.51  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 15.39/7.51  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 15.39/7.51  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.39/7.51  tff(c_477, plain, (![A_115, B_116]: (r1_xboole_0(A_115, B_116) | k4_xboole_0(A_115, B_116)!=A_115)), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.39/7.51  tff(c_78, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.39/7.51  tff(c_116, plain, (r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_78])).
% 15.39/7.51  tff(c_72, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4') | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.39/7.51  tff(c_155, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_116, c_72])).
% 15.39/7.51  tff(c_70, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.39/7.51  tff(c_371, plain, (![B_109, A_110]: (k3_xboole_0(k1_relat_1(B_109), A_110)=k1_relat_1(k7_relat_1(B_109, A_110)) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.39/7.51  tff(c_32, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.39/7.51  tff(c_34, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.39/7.51  tff(c_177, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.39/7.51  tff(c_198, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_177])).
% 15.39/7.51  tff(c_201, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_198])).
% 15.39/7.51  tff(c_135, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=A_66 | ~r1_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.39/7.51  tff(c_139, plain, (k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_116, c_135])).
% 15.39/7.51  tff(c_195, plain, (k4_xboole_0(k1_relat_1('#skF_5'), k1_relat_1('#skF_5'))=k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_139, c_177])).
% 15.39/7.51  tff(c_246, plain, (k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_201, c_195])).
% 15.39/7.51  tff(c_380, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_371, c_246])).
% 15.39/7.51  tff(c_411, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_380])).
% 15.39/7.51  tff(c_56, plain, (![A_49, B_50]: (v1_relat_1(k7_relat_1(A_49, B_50)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.39/7.51  tff(c_68, plain, (![B_55, A_54]: (k3_xboole_0(k1_relat_1(B_55), A_54)=k1_relat_1(k7_relat_1(B_55, A_54)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.39/7.51  tff(c_418, plain, (![A_54]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_5', '#skF_4'), A_54))=k3_xboole_0(k1_xboole_0, A_54) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_411, c_68])).
% 15.39/7.51  tff(c_438, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_418])).
% 15.39/7.51  tff(c_441, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_438])).
% 15.39/7.51  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_441])).
% 15.39/7.51  tff(c_447, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_418])).
% 15.39/7.51  tff(c_64, plain, (![A_51]: (k1_relat_1(A_51)!=k1_xboole_0 | k1_xboole_0=A_51 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.39/7.51  tff(c_450, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_447, c_64])).
% 15.39/7.51  tff(c_456, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_411, c_450])).
% 15.39/7.51  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_456])).
% 15.39/7.51  tff(c_460, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_78])).
% 15.39/7.51  tff(c_481, plain, (k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4')!=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_477, c_460])).
% 15.39/7.51  tff(c_579, plain, (![A_140, B_141]: (r2_hidden('#skF_1'(A_140, B_141), A_140) | r1_tarski(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.39/7.51  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.39/7.51  tff(c_1783, plain, (![A_249, B_250, B_251]: (r2_hidden('#skF_1'(k4_xboole_0(A_249, B_250), B_251), A_249) | r1_tarski(k4_xboole_0(A_249, B_250), B_251))), inference(resolution, [status(thm)], [c_579, c_12])).
% 15.39/7.51  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.39/7.51  tff(c_1849, plain, (![A_249, B_250]: (r1_tarski(k4_xboole_0(A_249, B_250), A_249))), inference(resolution, [status(thm)], [c_1783, c_4])).
% 15.39/7.51  tff(c_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.39/7.51  tff(c_459, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 15.39/7.51  tff(c_554, plain, (![A_138, B_139]: (k4_xboole_0(A_138, k4_xboole_0(A_138, B_139))=k3_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.39/7.51  tff(c_36, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.39/7.51  tff(c_926, plain, (![A_176, B_177]: (k4_xboole_0(A_176, k3_xboole_0(A_176, B_177))=k3_xboole_0(A_176, k4_xboole_0(A_176, B_177)))), inference(superposition, [status(thm), theory('equality')], [c_554, c_36])).
% 15.39/7.51  tff(c_50681, plain, (![B_908, A_909]: (k4_xboole_0(k1_relat_1(B_908), k1_relat_1(k7_relat_1(B_908, A_909)))=k3_xboole_0(k1_relat_1(B_908), k4_xboole_0(k1_relat_1(B_908), A_909)) | ~v1_relat_1(B_908))), inference(superposition, [status(thm), theory('equality')], [c_68, c_926])).
% 15.39/7.51  tff(c_51119, plain, (k3_xboole_0(k1_relat_1('#skF_5'), k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))=k4_xboole_0(k1_relat_1('#skF_5'), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_459, c_50681])).
% 15.39/7.51  tff(c_51150, plain, (k3_xboole_0(k1_relat_1('#skF_5'), k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_34, c_60, c_51119])).
% 15.39/7.51  tff(c_51375, plain, (k1_relat_1(k7_relat_1('#skF_5', k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4')))=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_68, c_51150])).
% 15.39/7.51  tff(c_51439, plain, (k1_relat_1(k7_relat_1('#skF_5', k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4')))=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_51375])).
% 15.39/7.51  tff(c_531, plain, (![B_126, A_127]: (r1_tarski(k1_relat_1(k7_relat_1(B_126, A_127)), A_127) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.39/7.51  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.39/7.51  tff(c_537, plain, (![B_126, A_127]: (k1_relat_1(k7_relat_1(B_126, A_127))=A_127 | ~r1_tarski(A_127, k1_relat_1(k7_relat_1(B_126, A_127))) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_531, c_26])).
% 15.39/7.51  tff(c_55197, plain, (k1_relat_1(k7_relat_1('#skF_5', k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4')))=k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4'), k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_51439, c_537])).
% 15.39/7.51  tff(c_55261, plain, (k4_xboole_0(k1_relat_1('#skF_5'), '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1849, c_51439, c_55197])).
% 15.39/7.51  tff(c_55263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_481, c_55261])).
% 15.39/7.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.39/7.51  
% 15.39/7.51  Inference rules
% 15.39/7.51  ----------------------
% 15.39/7.51  #Ref     : 0
% 15.39/7.51  #Sup     : 14245
% 15.39/7.51  #Fact    : 0
% 15.39/7.51  #Define  : 0
% 15.39/7.51  #Split   : 8
% 15.39/7.51  #Chain   : 0
% 15.39/7.51  #Close   : 0
% 15.39/7.51  
% 15.39/7.51  Ordering : KBO
% 15.39/7.51  
% 15.39/7.51  Simplification rules
% 15.39/7.51  ----------------------
% 15.39/7.51  #Subsume      : 4793
% 15.39/7.51  #Demod        : 10063
% 15.39/7.51  #Tautology    : 5152
% 15.39/7.51  #SimpNegUnit  : 21
% 15.39/7.51  #BackRed      : 6
% 15.39/7.51  
% 15.39/7.51  #Partial instantiations: 0
% 15.39/7.51  #Strategies tried      : 1
% 15.39/7.51  
% 15.39/7.51  Timing (in seconds)
% 15.39/7.51  ----------------------
% 15.39/7.52  Preprocessing        : 0.39
% 15.39/7.52  Parsing              : 0.17
% 15.39/7.52  CNF conversion       : 0.03
% 15.39/7.52  Main loop            : 6.31
% 15.39/7.52  Inferencing          : 1.22
% 15.39/7.52  Reduction            : 2.29
% 15.39/7.52  Demodulation         : 1.83
% 15.39/7.52  BG Simplification    : 0.15
% 15.39/7.52  Subsumption          : 2.31
% 15.39/7.52  Abstraction          : 0.25
% 15.39/7.52  MUC search           : 0.00
% 15.39/7.52  Cooper               : 0.00
% 15.39/7.52  Total                : 6.74
% 15.39/7.52  Index Insertion      : 0.00
% 15.39/7.52  Index Deletion       : 0.00
% 15.39/7.52  Index Matching       : 0.00
% 15.39/7.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

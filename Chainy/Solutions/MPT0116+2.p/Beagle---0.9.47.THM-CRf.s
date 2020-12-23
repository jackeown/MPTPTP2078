%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0116+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:15 EST 2020

% Result     : Theorem 9.98s
% Output     : CNFRefutation 9.98s
% Verified   : 
% Statistics : Number of formulae       :   63 (  64 expanded)
%              Number of leaves         :   46 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_22 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_23 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_23',type,(
    '#skF_23': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_454,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_328,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_464,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_488,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_400,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_402,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_332,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_326,plain,(
    ! [A_209,B_210] : r1_tarski(k4_xboole_0(A_209,B_210),A_209) ),
    inference(cnfTransformation,[status(thm)],[f_454])).

tff(c_256,plain,(
    r1_tarski('#skF_19','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_334,plain,(
    ! [A_215,B_216] : k2_xboole_0(A_215,k4_xboole_0(B_216,A_215)) = k2_xboole_0(A_215,B_216) ),
    inference(cnfTransformation,[status(thm)],[f_464])).

tff(c_350,plain,(
    ! [A_233,B_234] :
      ( k2_xboole_0(A_233,k4_xboole_0(B_234,A_233)) = B_234
      | ~ r1_tarski(A_233,B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_488])).

tff(c_1845,plain,(
    ! [A_499,B_500] :
      ( k2_xboole_0(A_499,B_500) = B_500
      | ~ r1_tarski(A_499,B_500) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_350])).

tff(c_1877,plain,(
    k2_xboole_0('#skF_19','#skF_20') = '#skF_20' ),
    inference(resolution,[status(thm)],[c_256,c_1845])).

tff(c_292,plain,(
    ! [A_164,B_165] : k3_xboole_0(A_164,k2_xboole_0(A_164,B_165)) = A_164 ),
    inference(cnfTransformation,[status(thm)],[f_400])).

tff(c_1892,plain,(
    k3_xboole_0('#skF_19','#skF_20') = '#skF_19' ),
    inference(superposition,[status(thm),theory(equality)],[c_1877,c_292])).

tff(c_1342,plain,(
    ! [B_474,A_475] : k3_xboole_0(B_474,A_475) = k3_xboole_0(A_475,B_474) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_294,plain,(
    ! [A_166,B_167] : k2_xboole_0(A_166,k3_xboole_0(A_166,B_167)) = A_166 ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_1360,plain,(
    ! [B_474,A_475] : k2_xboole_0(B_474,k3_xboole_0(A_475,B_474)) = B_474 ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_294])).

tff(c_1924,plain,(
    k2_xboole_0('#skF_20','#skF_19') = '#skF_20' ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_1360])).

tff(c_13641,plain,(
    ! [A_770,C_771,B_772] :
      ( r1_tarski(A_770,k2_xboole_0(C_771,B_772))
      | ~ r1_tarski(A_770,B_772) ) ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_13715,plain,(
    ! [A_773] :
      ( r1_tarski(A_773,'#skF_20')
      | ~ r1_tarski(A_773,'#skF_19') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1924,c_13641])).

tff(c_254,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_19','#skF_21'),'#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_13735,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_19','#skF_21'),'#skF_19') ),
    inference(resolution,[status(thm)],[c_13715,c_254])).

tff(c_13745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_13735])).
%------------------------------------------------------------------------------

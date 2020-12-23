%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0034+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:10 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :   74 (  87 expanded)
%              Number of leaves         :   47 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  70 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_24 > #skF_23 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_24',type,(
    '#skF_24': $i )).

tff('#skF_23',type,(
    '#skF_23': $i )).

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

tff(f_293,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_345,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_266,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_326,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_328,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_258,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_303,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_220,plain,(
    ! [A_108,B_109] : r1_tarski(k3_xboole_0(A_108,B_109),A_108) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_250,plain,(
    r1_tarski('#skF_23','#skF_24') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_1072,plain,(
    ! [A_224,B_225] :
      ( k2_xboole_0(A_224,B_225) = B_225
      | ~ r1_tarski(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_1104,plain,(
    k2_xboole_0('#skF_23','#skF_24') = '#skF_24' ),
    inference(resolution,[status(thm)],[c_250,c_1072])).

tff(c_236,plain,(
    ! [A_124,B_125] : k3_xboole_0(A_124,k2_xboole_0(A_124,B_125)) = A_124 ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_1165,plain,(
    k3_xboole_0('#skF_23','#skF_24') = '#skF_23' ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_236])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_593,plain,(
    ! [A_198,B_199] : k2_xboole_0(A_198,k3_xboole_0(A_198,B_199)) = A_198 ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_611,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(B_8,A_7)) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_593])).

tff(c_1207,plain,(
    k2_xboole_0('#skF_24','#skF_23') = '#skF_24' ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_611])).

tff(c_2094,plain,(
    ! [A_266,C_267,B_268] :
      ( r1_tarski(A_266,k2_xboole_0(C_267,B_268))
      | ~ r1_tarski(A_266,B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_2114,plain,(
    ! [A_266] :
      ( r1_tarski(A_266,'#skF_24')
      | ~ r1_tarski(A_266,'#skF_23') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_2094])).

tff(c_478,plain,(
    ! [B_192,A_193] : k3_xboole_0(B_192,A_193) = k3_xboole_0(A_193,B_192) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_501,plain,(
    ! [B_192,A_193] : r1_tarski(k3_xboole_0(B_192,A_193),A_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_220])).

tff(c_252,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_1103,plain,(
    k2_xboole_0('#skF_21','#skF_22') = '#skF_22' ),
    inference(resolution,[status(thm)],[c_252,c_1072])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1119,plain,(
    k2_xboole_0('#skF_22','#skF_21') = '#skF_22' ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_6])).

tff(c_2173,plain,(
    ! [A_271] :
      ( r1_tarski(A_271,'#skF_22')
      | ~ r1_tarski(A_271,'#skF_21') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1119,c_2094])).

tff(c_2196,plain,(
    ! [B_192] : r1_tarski(k3_xboole_0(B_192,'#skF_21'),'#skF_22') ),
    inference(resolution,[status(thm)],[c_501,c_2173])).

tff(c_10961,plain,(
    ! [A_480,B_481,C_482] :
      ( r1_tarski(A_480,k3_xboole_0(B_481,C_482))
      | ~ r1_tarski(A_480,C_482)
      | ~ r1_tarski(A_480,B_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_248,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_21','#skF_23'),k3_xboole_0('#skF_22','#skF_24')) ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_282,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_23','#skF_21'),k3_xboole_0('#skF_24','#skF_22')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_248])).

tff(c_10994,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_23','#skF_21'),'#skF_22')
    | ~ r1_tarski(k3_xboole_0('#skF_23','#skF_21'),'#skF_24') ),
    inference(resolution,[status(thm)],[c_10961,c_282])).

tff(c_11060,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_23','#skF_21'),'#skF_24') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2196,c_10994])).

tff(c_11075,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_23','#skF_21'),'#skF_23') ),
    inference(resolution,[status(thm)],[c_2114,c_11060])).

tff(c_11089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_11075])).
%------------------------------------------------------------------------------

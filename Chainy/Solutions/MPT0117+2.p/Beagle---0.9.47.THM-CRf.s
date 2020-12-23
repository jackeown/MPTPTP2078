%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0117+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:15 EST 2020

% Result     : Theorem 25.10s
% Output     : CNFRefutation 25.10s
% Verified   : 
% Statistics : Number of formulae       :   67 (  93 expanded)
%              Number of leaves         :   46 (  57 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  82 expanded)
%              Number of equality atoms :   10 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_338,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_470,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_494,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_460,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_693,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_342,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_769,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k4_xboole_0(A,B),C)
        & r1_tarski(k4_xboole_0(B,A),C) )
     => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

tff(c_260,plain,(
    r1_tarski('#skF_21','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_338])).

tff(c_338,plain,(
    ! [A_218,B_219] : k2_xboole_0(A_218,k4_xboole_0(B_219,A_218)) = k2_xboole_0(A_218,B_219) ),
    inference(cnfTransformation,[status(thm)],[f_470])).

tff(c_354,plain,(
    ! [A_236,B_237] :
      ( k2_xboole_0(A_236,k4_xboole_0(B_237,A_236)) = B_237
      | ~ r1_tarski(A_236,B_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_494])).

tff(c_2151,plain,(
    ! [A_516,B_517] :
      ( k2_xboole_0(A_516,B_517) = B_517
      | ~ r1_tarski(A_516,B_517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_354])).

tff(c_2186,plain,(
    k2_xboole_0('#skF_21','#skF_20') = '#skF_20' ),
    inference(resolution,[status(thm)],[c_260,c_2151])).

tff(c_330,plain,(
    ! [A_212,B_213] : r1_tarski(k4_xboole_0(A_212,B_213),A_212) ),
    inference(cnfTransformation,[status(thm)],[f_460])).

tff(c_2182,plain,(
    ! [A_212,B_213] : k2_xboole_0(k4_xboole_0(A_212,B_213),A_212) = A_212 ),
    inference(resolution,[status(thm)],[c_330,c_2151])).

tff(c_444,plain,(
    ! [A_337,B_338] : r1_tarski(A_337,k2_xboole_0(A_337,B_338)) ),
    inference(cnfTransformation,[status(thm)],[f_693])).

tff(c_10862,plain,(
    ! [A_664,C_665,B_666] :
      ( r1_tarski(A_664,C_665)
      | ~ r1_tarski(k2_xboole_0(A_664,B_666),C_665) ) ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_21221,plain,(
    ! [A_857,B_858,B_859] : r1_tarski(A_857,k2_xboole_0(k2_xboole_0(A_857,B_858),B_859)) ),
    inference(resolution,[status(thm)],[c_444,c_10862])).

tff(c_22161,plain,(
    ! [A_867,B_868,B_869] : r1_tarski(k4_xboole_0(A_867,B_868),k2_xboole_0(A_867,B_869)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2182,c_21221])).

tff(c_22307,plain,(
    ! [B_868] : r1_tarski(k4_xboole_0('#skF_21',B_868),'#skF_20') ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_22161])).

tff(c_262,plain,(
    r1_tarski('#skF_19','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_338])).

tff(c_2187,plain,(
    k2_xboole_0('#skF_19','#skF_20') = '#skF_20' ),
    inference(resolution,[status(thm)],[c_262,c_2151])).

tff(c_22304,plain,(
    ! [B_868] : r1_tarski(k4_xboole_0('#skF_19',B_868),'#skF_20') ),
    inference(superposition,[status(thm),theory(equality)],[c_2187,c_22161])).

tff(c_82845,plain,(
    ! [A_1483,B_1484,C_1485] :
      ( r1_tarski(k5_xboole_0(A_1483,B_1484),C_1485)
      | ~ r1_tarski(k4_xboole_0(B_1484,A_1483),C_1485)
      | ~ r1_tarski(k4_xboole_0(A_1483,B_1484),C_1485) ) ),
    inference(cnfTransformation,[status(thm)],[f_769])).

tff(c_10,plain,(
    ! [B_10,A_9] : k5_xboole_0(B_10,A_9) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_258,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_19','#skF_21'),'#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_338])).

tff(c_512,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_21','#skF_19'),'#skF_20') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_258])).

tff(c_82935,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_19','#skF_21'),'#skF_20')
    | ~ r1_tarski(k4_xboole_0('#skF_21','#skF_19'),'#skF_20') ),
    inference(resolution,[status(thm)],[c_82845,c_512])).

tff(c_83050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22307,c_22304,c_82935])).
%------------------------------------------------------------------------------

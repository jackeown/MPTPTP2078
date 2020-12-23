%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:22 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 106 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :   64 (  96 expanded)
%              Number of equality atoms :   51 (  77 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_70,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_60,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_62,plain,(
    ! [A_36,B_37,C_38] : k2_enumset1(A_36,A_36,B_37,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2484,plain,(
    ! [A_3196,B_3197,C_3198,D_3199] : k2_xboole_0(k1_enumset1(A_3196,B_3197,C_3198),k1_tarski(D_3199)) = k2_enumset1(A_3196,B_3197,C_3198,D_3199) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2556,plain,(
    ! [A_34,B_35,D_3199] : k2_xboole_0(k2_tarski(A_34,B_35),k1_tarski(D_3199)) = k2_enumset1(A_34,A_34,B_35,D_3199) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2484])).

tff(c_2561,plain,(
    ! [A_3248,B_3249,D_3250] : k2_xboole_0(k2_tarski(A_3248,B_3249),k1_tarski(D_3250)) = k1_enumset1(A_3248,B_3249,D_3250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2556])).

tff(c_2624,plain,(
    ! [A_33,D_3250] : k2_xboole_0(k1_tarski(A_33),k1_tarski(D_3250)) = k1_enumset1(A_33,A_33,D_3250) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2561])).

tff(c_2629,plain,(
    ! [A_3299,D_3300] : k2_xboole_0(k1_tarski(A_3299),k1_tarski(D_3300)) = k2_tarski(A_3299,D_3300) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2624])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_266,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_287,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_266])).

tff(c_149,plain,(
    ! [A_79,B_80] : r1_xboole_0(k3_xboole_0(A_79,B_80),k5_xboole_0(A_79,B_80)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_161,plain,(
    ! [A_3] : r1_xboole_0(A_3,k5_xboole_0(A_3,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_149])).

tff(c_335,plain,(
    ! [A_90] : r1_xboole_0(A_90,k4_xboole_0(A_90,A_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_161])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_342,plain,(
    ! [A_90] : k3_xboole_0(A_90,k4_xboole_0(A_90,A_90)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_335,c_2])).

tff(c_345,plain,(
    ! [A_91] : k3_xboole_0(A_91,k4_xboole_0(A_91,A_91)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_335,c_2])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_350,plain,(
    ! [A_91] : k4_xboole_0(A_91,k4_xboole_0(A_91,A_91)) = k5_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_10])).

tff(c_360,plain,(
    ! [A_91] : k4_xboole_0(A_91,k4_xboole_0(A_91,A_91)) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_350])).

tff(c_532,plain,(
    ! [A_102,B_103] : k4_xboole_0(A_102,k4_xboole_0(A_102,B_103)) = k3_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_557,plain,(
    ! [A_91] : k3_xboole_0(A_91,k4_xboole_0(A_91,A_91)) = k4_xboole_0(A_91,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_532])).

tff(c_568,plain,(
    ! [A_91] : k4_xboole_0(A_91,A_91) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_557])).

tff(c_72,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_284,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_266])).

tff(c_324,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_287])).

tff(c_623,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_324])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_631,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_16])).

tff(c_635,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_631])).

tff(c_2641,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2629,c_635])).

tff(c_114,plain,(
    ! [A_69,B_70] : k1_enumset1(A_69,A_69,B_70) = k2_tarski(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_126,plain,(
    ! [B_70,A_69] : r2_hidden(B_70,k2_tarski(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_20])).

tff(c_2766,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2641,c_126])).

tff(c_42,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2798,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2766,c_42])).

tff(c_2838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.65  
% 3.74/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.65  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 3.74/1.65  
% 3.74/1.65  %Foreground sorts:
% 3.74/1.65  
% 3.74/1.65  
% 3.74/1.65  %Background operators:
% 3.74/1.65  
% 3.74/1.65  
% 3.74/1.65  %Foreground operators:
% 3.74/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.74/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.74/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.74/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.74/1.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.74/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.74/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.74/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.74/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.74/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.74/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.74/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.74/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.74/1.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.74/1.65  
% 3.74/1.67  tff(f_84, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.74/1.67  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.74/1.67  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.74/1.67  tff(f_73, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.74/1.67  tff(f_67, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.74/1.67  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.74/1.67  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.74/1.67  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.74/1.67  tff(f_33, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.74/1.67  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.74/1.67  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.74/1.67  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.74/1.67  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.74/1.67  tff(f_63, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.74/1.67  tff(c_70, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.74/1.67  tff(c_60, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.74/1.67  tff(c_58, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.74/1.67  tff(c_62, plain, (![A_36, B_37, C_38]: (k2_enumset1(A_36, A_36, B_37, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.74/1.67  tff(c_2484, plain, (![A_3196, B_3197, C_3198, D_3199]: (k2_xboole_0(k1_enumset1(A_3196, B_3197, C_3198), k1_tarski(D_3199))=k2_enumset1(A_3196, B_3197, C_3198, D_3199))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.74/1.67  tff(c_2556, plain, (![A_34, B_35, D_3199]: (k2_xboole_0(k2_tarski(A_34, B_35), k1_tarski(D_3199))=k2_enumset1(A_34, A_34, B_35, D_3199))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2484])).
% 3.74/1.67  tff(c_2561, plain, (![A_3248, B_3249, D_3250]: (k2_xboole_0(k2_tarski(A_3248, B_3249), k1_tarski(D_3250))=k1_enumset1(A_3248, B_3249, D_3250))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2556])).
% 3.74/1.67  tff(c_2624, plain, (![A_33, D_3250]: (k2_xboole_0(k1_tarski(A_33), k1_tarski(D_3250))=k1_enumset1(A_33, A_33, D_3250))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2561])).
% 3.74/1.67  tff(c_2629, plain, (![A_3299, D_3300]: (k2_xboole_0(k1_tarski(A_3299), k1_tarski(D_3300))=k2_tarski(A_3299, D_3300))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2624])).
% 3.74/1.67  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.74/1.67  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.74/1.67  tff(c_266, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.74/1.67  tff(c_287, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_266])).
% 3.74/1.67  tff(c_149, plain, (![A_79, B_80]: (r1_xboole_0(k3_xboole_0(A_79, B_80), k5_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.67  tff(c_161, plain, (![A_3]: (r1_xboole_0(A_3, k5_xboole_0(A_3, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_149])).
% 3.74/1.67  tff(c_335, plain, (![A_90]: (r1_xboole_0(A_90, k4_xboole_0(A_90, A_90)))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_161])).
% 3.74/1.67  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.74/1.67  tff(c_342, plain, (![A_90]: (k3_xboole_0(A_90, k4_xboole_0(A_90, A_90))=k1_xboole_0)), inference(resolution, [status(thm)], [c_335, c_2])).
% 3.74/1.67  tff(c_345, plain, (![A_91]: (k3_xboole_0(A_91, k4_xboole_0(A_91, A_91))=k1_xboole_0)), inference(resolution, [status(thm)], [c_335, c_2])).
% 3.74/1.67  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.74/1.67  tff(c_350, plain, (![A_91]: (k4_xboole_0(A_91, k4_xboole_0(A_91, A_91))=k5_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_345, c_10])).
% 3.74/1.67  tff(c_360, plain, (![A_91]: (k4_xboole_0(A_91, k4_xboole_0(A_91, A_91))=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_350])).
% 3.74/1.67  tff(c_532, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k4_xboole_0(A_102, B_103))=k3_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.67  tff(c_557, plain, (![A_91]: (k3_xboole_0(A_91, k4_xboole_0(A_91, A_91))=k4_xboole_0(A_91, A_91))), inference(superposition, [status(thm), theory('equality')], [c_360, c_532])).
% 3.74/1.67  tff(c_568, plain, (![A_91]: (k4_xboole_0(A_91, A_91)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_342, c_557])).
% 3.74/1.67  tff(c_72, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.74/1.67  tff(c_284, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_266])).
% 3.74/1.67  tff(c_324, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_284, c_287])).
% 3.74/1.67  tff(c_623, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_568, c_324])).
% 3.74/1.67  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.67  tff(c_631, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_623, c_16])).
% 3.74/1.67  tff(c_635, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_631])).
% 3.74/1.67  tff(c_2641, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2629, c_635])).
% 3.74/1.67  tff(c_114, plain, (![A_69, B_70]: (k1_enumset1(A_69, A_69, B_70)=k2_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.74/1.67  tff(c_20, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.74/1.67  tff(c_126, plain, (![B_70, A_69]: (r2_hidden(B_70, k2_tarski(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_20])).
% 3.74/1.67  tff(c_2766, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2641, c_126])).
% 3.74/1.67  tff(c_42, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.74/1.67  tff(c_2798, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2766, c_42])).
% 3.74/1.67  tff(c_2838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_2798])).
% 3.74/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.67  
% 3.74/1.67  Inference rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Ref     : 0
% 3.74/1.67  #Sup     : 467
% 3.74/1.67  #Fact    : 0
% 3.74/1.67  #Define  : 0
% 3.74/1.67  #Split   : 6
% 3.74/1.67  #Chain   : 0
% 3.74/1.67  #Close   : 0
% 3.74/1.67  
% 3.74/1.67  Ordering : KBO
% 3.74/1.67  
% 3.74/1.67  Simplification rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Subsume      : 13
% 3.74/1.67  #Demod        : 400
% 3.74/1.67  #Tautology    : 315
% 3.74/1.67  #SimpNegUnit  : 1
% 3.74/1.67  #BackRed      : 11
% 3.74/1.67  
% 3.74/1.67  #Partial instantiations: 1224
% 3.74/1.67  #Strategies tried      : 1
% 3.74/1.67  
% 3.74/1.67  Timing (in seconds)
% 3.74/1.67  ----------------------
% 3.74/1.67  Preprocessing        : 0.33
% 3.74/1.67  Parsing              : 0.17
% 3.74/1.67  CNF conversion       : 0.03
% 3.74/1.67  Main loop            : 0.58
% 3.74/1.67  Inferencing          : 0.25
% 3.74/1.67  Reduction            : 0.19
% 3.74/1.67  Demodulation         : 0.14
% 3.74/1.67  BG Simplification    : 0.03
% 3.74/1.67  Subsumption          : 0.09
% 3.74/1.67  Abstraction          : 0.02
% 3.74/1.67  MUC search           : 0.00
% 3.74/1.67  Cooper               : 0.00
% 3.74/1.67  Total                : 0.94
% 3.74/1.67  Index Insertion      : 0.00
% 3.74/1.67  Index Deletion       : 0.00
% 3.74/1.67  Index Matching       : 0.00
% 3.74/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------

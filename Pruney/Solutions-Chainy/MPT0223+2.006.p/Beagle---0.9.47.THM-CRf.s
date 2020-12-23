%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:17 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 183 expanded)
%              Number of leaves         :   33 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :   62 ( 199 expanded)
%              Number of equality atoms :   56 ( 186 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    ! [A_27,B_28,C_29] : k2_enumset1(A_27,A_27,B_28,C_29) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_477,plain,(
    ! [A_95,B_96,C_97,D_98] : k2_xboole_0(k1_enumset1(A_95,B_96,C_97),k1_tarski(D_98)) = k2_enumset1(A_95,B_96,C_97,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_492,plain,(
    ! [A_25,B_26,D_98] : k2_xboole_0(k2_tarski(A_25,B_26),k1_tarski(D_98)) = k2_enumset1(A_25,A_25,B_26,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_477])).

tff(c_535,plain,(
    ! [A_100,B_101,D_102] : k2_xboole_0(k2_tarski(A_100,B_101),k1_tarski(D_102)) = k1_enumset1(A_100,B_101,D_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_492])).

tff(c_556,plain,(
    ! [A_24,D_102] : k2_xboole_0(k1_tarski(A_24),k1_tarski(D_102)) = k1_enumset1(A_24,A_24,D_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_535])).

tff(c_559,plain,(
    ! [A_24,D_102] : k2_xboole_0(k1_tarski(A_24),k1_tarski(D_102)) = k2_tarski(A_24,D_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_556])).

tff(c_560,plain,(
    ! [A_103,D_104] : k2_xboole_0(k1_tarski(A_103),k1_tarski(D_104)) = k2_tarski(A_103,D_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_556])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_200,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_215,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_200])).

tff(c_219,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_215])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_212,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_200])).

tff(c_218,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_212])).

tff(c_58,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_209,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_200])).

tff(c_338,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_209])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_342,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_12])).

tff(c_345,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_342])).

tff(c_569,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_345])).

tff(c_495,plain,(
    ! [A_25,B_26,D_98] : k2_xboole_0(k2_tarski(A_25,B_26),k1_tarski(D_98)) = k1_enumset1(A_25,B_26,D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_492])).

tff(c_592,plain,(
    ! [D_98] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_98)) = k1_enumset1('#skF_4','#skF_3',D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_495])).

tff(c_660,plain,(
    ! [D_112] : k1_enumset1('#skF_4','#skF_3',D_112) = k2_tarski('#skF_4',D_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_592])).

tff(c_20,plain,(
    ! [E_19,A_13,C_15] : r2_hidden(E_19,k1_enumset1(A_13,E_19,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_675,plain,(
    ! [D_112] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_20])).

tff(c_604,plain,(
    ! [E_105,C_106,B_107,A_108] :
      ( E_105 = C_106
      | E_105 = B_107
      | E_105 = A_108
      | ~ r2_hidden(E_105,k1_enumset1(A_108,B_107,C_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4226,plain,(
    ! [E_279,B_280,A_281] :
      ( E_279 = B_280
      | E_279 = A_281
      | E_279 = A_281
      | ~ r2_hidden(E_279,k2_tarski(A_281,B_280)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_604])).

tff(c_4243,plain,(
    ! [D_112] :
      ( D_112 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_675,c_4226])).

tff(c_4275,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_4243])).

tff(c_4269,plain,(
    ! [D_112] : D_112 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_4243])).

tff(c_4756,plain,(
    ! [D_5650] : D_5650 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4275,c_4269])).

tff(c_5220,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4756,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:56:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.05  
% 5.16/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.05  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.16/2.05  
% 5.16/2.05  %Foreground sorts:
% 5.16/2.05  
% 5.16/2.05  
% 5.16/2.05  %Background operators:
% 5.16/2.05  
% 5.16/2.05  
% 5.16/2.05  %Foreground operators:
% 5.16/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.16/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.16/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.16/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.16/2.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.16/2.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.16/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.16/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.16/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.16/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.16/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.16/2.05  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.16/2.05  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.16/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.16/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.16/2.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.16/2.05  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.16/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.16/2.05  
% 5.16/2.06  tff(f_75, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 5.16/2.06  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.16/2.06  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.16/2.06  tff(f_62, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.16/2.06  tff(f_56, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 5.16/2.06  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.16/2.06  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.16/2.06  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.16/2.06  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.16/2.06  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.16/2.06  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.16/2.06  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.16/2.06  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.16/2.06  tff(c_44, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.16/2.06  tff(c_42, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.16/2.06  tff(c_46, plain, (![A_27, B_28, C_29]: (k2_enumset1(A_27, A_27, B_28, C_29)=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.16/2.06  tff(c_477, plain, (![A_95, B_96, C_97, D_98]: (k2_xboole_0(k1_enumset1(A_95, B_96, C_97), k1_tarski(D_98))=k2_enumset1(A_95, B_96, C_97, D_98))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.16/2.06  tff(c_492, plain, (![A_25, B_26, D_98]: (k2_xboole_0(k2_tarski(A_25, B_26), k1_tarski(D_98))=k2_enumset1(A_25, A_25, B_26, D_98))), inference(superposition, [status(thm), theory('equality')], [c_44, c_477])).
% 5.16/2.06  tff(c_535, plain, (![A_100, B_101, D_102]: (k2_xboole_0(k2_tarski(A_100, B_101), k1_tarski(D_102))=k1_enumset1(A_100, B_101, D_102))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_492])).
% 5.16/2.06  tff(c_556, plain, (![A_24, D_102]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(D_102))=k1_enumset1(A_24, A_24, D_102))), inference(superposition, [status(thm), theory('equality')], [c_42, c_535])).
% 5.16/2.06  tff(c_559, plain, (![A_24, D_102]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(D_102))=k2_tarski(A_24, D_102))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_556])).
% 5.16/2.06  tff(c_560, plain, (![A_103, D_104]: (k2_xboole_0(k1_tarski(A_103), k1_tarski(D_104))=k2_tarski(A_103, D_104))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_556])).
% 5.16/2.06  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.16/2.06  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.16/2.06  tff(c_200, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/2.06  tff(c_215, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_200])).
% 5.16/2.06  tff(c_219, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_215])).
% 5.16/2.06  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.16/2.06  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.16/2.06  tff(c_212, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_200])).
% 5.16/2.06  tff(c_218, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_212])).
% 5.16/2.06  tff(c_58, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.16/2.06  tff(c_209, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_200])).
% 5.16/2.06  tff(c_338, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_218, c_209])).
% 5.16/2.06  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.16/2.06  tff(c_342, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_338, c_12])).
% 5.16/2.06  tff(c_345, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_342])).
% 5.16/2.06  tff(c_569, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_560, c_345])).
% 5.16/2.06  tff(c_495, plain, (![A_25, B_26, D_98]: (k2_xboole_0(k2_tarski(A_25, B_26), k1_tarski(D_98))=k1_enumset1(A_25, B_26, D_98))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_492])).
% 5.16/2.06  tff(c_592, plain, (![D_98]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_98))=k1_enumset1('#skF_4', '#skF_3', D_98))), inference(superposition, [status(thm), theory('equality')], [c_569, c_495])).
% 5.16/2.06  tff(c_660, plain, (![D_112]: (k1_enumset1('#skF_4', '#skF_3', D_112)=k2_tarski('#skF_4', D_112))), inference(demodulation, [status(thm), theory('equality')], [c_559, c_592])).
% 5.16/2.06  tff(c_20, plain, (![E_19, A_13, C_15]: (r2_hidden(E_19, k1_enumset1(A_13, E_19, C_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.16/2.06  tff(c_675, plain, (![D_112]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_112)))), inference(superposition, [status(thm), theory('equality')], [c_660, c_20])).
% 5.16/2.06  tff(c_604, plain, (![E_105, C_106, B_107, A_108]: (E_105=C_106 | E_105=B_107 | E_105=A_108 | ~r2_hidden(E_105, k1_enumset1(A_108, B_107, C_106)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.16/2.06  tff(c_4226, plain, (![E_279, B_280, A_281]: (E_279=B_280 | E_279=A_281 | E_279=A_281 | ~r2_hidden(E_279, k2_tarski(A_281, B_280)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_604])).
% 5.16/2.06  tff(c_4243, plain, (![D_112]: (D_112='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_675, c_4226])).
% 5.16/2.06  tff(c_4275, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_4243])).
% 5.16/2.06  tff(c_4269, plain, (![D_112]: (D_112='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_4243])).
% 5.16/2.06  tff(c_4756, plain, (![D_5650]: (D_5650='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4275, c_4269])).
% 5.16/2.06  tff(c_5220, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4756, c_56])).
% 5.16/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.06  
% 5.16/2.06  Inference rules
% 5.16/2.06  ----------------------
% 5.16/2.06  #Ref     : 0
% 5.16/2.06  #Sup     : 1464
% 5.16/2.06  #Fact    : 1
% 5.16/2.06  #Define  : 0
% 5.16/2.06  #Split   : 0
% 5.16/2.06  #Chain   : 0
% 5.16/2.06  #Close   : 0
% 5.16/2.06  
% 5.16/2.06  Ordering : KBO
% 5.16/2.06  
% 5.16/2.06  Simplification rules
% 5.16/2.06  ----------------------
% 5.16/2.06  #Subsume      : 223
% 5.16/2.06  #Demod        : 1322
% 5.16/2.06  #Tautology    : 825
% 5.16/2.06  #SimpNegUnit  : 12
% 5.16/2.06  #BackRed      : 2
% 5.16/2.06  
% 5.16/2.06  #Partial instantiations: 103
% 5.16/2.06  #Strategies tried      : 1
% 5.16/2.06  
% 5.16/2.06  Timing (in seconds)
% 5.16/2.06  ----------------------
% 5.49/2.07  Preprocessing        : 0.32
% 5.49/2.07  Parsing              : 0.17
% 5.49/2.07  CNF conversion       : 0.02
% 5.49/2.07  Main loop            : 0.99
% 5.49/2.07  Inferencing          : 0.34
% 5.49/2.07  Reduction            : 0.42
% 5.49/2.07  Demodulation         : 0.35
% 5.49/2.07  BG Simplification    : 0.03
% 5.49/2.07  Subsumption          : 0.15
% 5.49/2.07  Abstraction          : 0.05
% 5.49/2.07  MUC search           : 0.00
% 5.49/2.07  Cooper               : 0.00
% 5.49/2.07  Total                : 1.34
% 5.49/2.07  Index Insertion      : 0.00
% 5.49/2.07  Index Deletion       : 0.00
% 5.49/2.07  Index Matching       : 0.00
% 5.49/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:56 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 367 expanded)
%              Number of leaves         :   35 ( 138 expanded)
%              Depth                    :   22
%              Number of atoms          :   64 ( 393 expanded)
%              Number of equality atoms :   48 ( 308 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_46,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_82,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,(
    ! [C_35] : r2_hidden(C_35,k1_tarski(C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_164,plain,(
    ! [B_66,A_67] : k3_xboole_0(B_66,A_67) = k3_xboole_0(A_67,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),A_51) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_122,plain,(
    ! [B_52] : k3_xboole_0(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_114,c_28])).

tff(c_180,plain,(
    ! [B_66] : k3_xboole_0(B_66,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_122])).

tff(c_390,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_399,plain,(
    ! [B_66] : k5_xboole_0(B_66,k1_xboole_0) = k4_xboole_0(B_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_390])).

tff(c_441,plain,(
    ! [B_93] : k4_xboole_0(B_93,k1_xboole_0) = B_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_399])).

tff(c_30,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_451,plain,(
    ! [B_93] : k4_xboole_0(B_93,B_93) = k3_xboole_0(B_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_30])).

tff(c_464,plain,(
    ! [B_93] : k4_xboole_0(B_93,B_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_451])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_411,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_390])).

tff(c_537,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_411])).

tff(c_84,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_454,plain,(
    ! [B_93] : k5_xboole_0(k1_xboole_0,B_93) = k2_xboole_0(k1_xboole_0,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_36])).

tff(c_555,plain,(
    ! [A_101,B_102,C_103] : k5_xboole_0(k5_xboole_0(A_101,B_102),C_103) = k5_xboole_0(A_101,k5_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_586,plain,(
    ! [A_9,C_103] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_103)) = k5_xboole_0(k1_xboole_0,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_555])).

tff(c_858,plain,(
    ! [A_117,C_118] : k5_xboole_0(A_117,k5_xboole_0(A_117,C_118)) = k2_xboole_0(k1_xboole_0,C_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_586])).

tff(c_907,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_858])).

tff(c_928,plain,(
    ! [A_9] : k2_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_907])).

tff(c_857,plain,(
    ! [A_9,C_103] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_103)) = k2_xboole_0(k1_xboole_0,C_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_586])).

tff(c_1027,plain,(
    ! [A_121,C_122] : k5_xboole_0(A_121,k5_xboole_0(A_121,C_122)) = C_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_857])).

tff(c_1800,plain,(
    ! [A_150,B_151] : k5_xboole_0(A_150,k2_xboole_0(A_150,B_151)) = k4_xboole_0(B_151,A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1027])).

tff(c_1849,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1800])).

tff(c_1858,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_1849])).

tff(c_24,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1073,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1027])).

tff(c_1862,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k5_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1858,c_1073])).

tff(c_1871,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1862])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2515,plain,(
    ! [D_174] :
      ( r2_hidden(D_174,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_174,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1871,c_6])).

tff(c_62,plain,(
    ! [C_35,A_31] :
      ( C_35 = A_31
      | ~ r2_hidden(C_35,k1_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2531,plain,(
    ! [D_175] :
      ( D_175 = '#skF_7'
      | ~ r2_hidden(D_175,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2515,c_62])).

tff(c_2559,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_64,c_2531])).

tff(c_2569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:50:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.85  
% 4.13/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.85  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 4.13/1.85  
% 4.13/1.85  %Foreground sorts:
% 4.13/1.85  
% 4.13/1.85  
% 4.13/1.85  %Background operators:
% 4.13/1.85  
% 4.13/1.85  
% 4.13/1.85  %Foreground operators:
% 4.13/1.85  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.13/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.13/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.13/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.13/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.13/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.13/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.13/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.13/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.13/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.13/1.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.13/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.13/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.13/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.13/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.13/1.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.13/1.85  
% 4.13/1.86  tff(f_89, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 4.13/1.86  tff(f_76, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.13/1.86  tff(f_50, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.13/1.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.13/1.86  tff(f_42, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.13/1.86  tff(f_46, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.13/1.86  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.13/1.86  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.13/1.86  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.13/1.86  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.13/1.86  tff(f_52, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.13/1.86  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.13/1.86  tff(c_82, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.13/1.86  tff(c_64, plain, (![C_35]: (r2_hidden(C_35, k1_tarski(C_35)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.13/1.86  tff(c_32, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.13/1.86  tff(c_164, plain, (![B_66, A_67]: (k3_xboole_0(B_66, A_67)=k3_xboole_0(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.13/1.86  tff(c_114, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), A_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.13/1.86  tff(c_28, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.13/1.86  tff(c_122, plain, (![B_52]: (k3_xboole_0(k1_xboole_0, B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_28])).
% 4.13/1.86  tff(c_180, plain, (![B_66]: (k3_xboole_0(B_66, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_164, c_122])).
% 4.13/1.86  tff(c_390, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.13/1.86  tff(c_399, plain, (![B_66]: (k5_xboole_0(B_66, k1_xboole_0)=k4_xboole_0(B_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_180, c_390])).
% 4.13/1.86  tff(c_441, plain, (![B_93]: (k4_xboole_0(B_93, k1_xboole_0)=B_93)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_399])).
% 4.13/1.86  tff(c_30, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.13/1.86  tff(c_451, plain, (![B_93]: (k4_xboole_0(B_93, B_93)=k3_xboole_0(B_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_441, c_30])).
% 4.13/1.86  tff(c_464, plain, (![B_93]: (k4_xboole_0(B_93, B_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_180, c_451])).
% 4.13/1.86  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.13/1.86  tff(c_411, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_390])).
% 4.13/1.86  tff(c_537, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_464, c_411])).
% 4.13/1.86  tff(c_84, plain, (k2_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.13/1.86  tff(c_36, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.13/1.86  tff(c_454, plain, (![B_93]: (k5_xboole_0(k1_xboole_0, B_93)=k2_xboole_0(k1_xboole_0, B_93))), inference(superposition, [status(thm), theory('equality')], [c_441, c_36])).
% 4.13/1.86  tff(c_555, plain, (![A_101, B_102, C_103]: (k5_xboole_0(k5_xboole_0(A_101, B_102), C_103)=k5_xboole_0(A_101, k5_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.13/1.86  tff(c_586, plain, (![A_9, C_103]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_103))=k5_xboole_0(k1_xboole_0, C_103))), inference(superposition, [status(thm), theory('equality')], [c_537, c_555])).
% 4.13/1.86  tff(c_858, plain, (![A_117, C_118]: (k5_xboole_0(A_117, k5_xboole_0(A_117, C_118))=k2_xboole_0(k1_xboole_0, C_118))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_586])).
% 4.13/1.86  tff(c_907, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_537, c_858])).
% 4.13/1.86  tff(c_928, plain, (![A_9]: (k2_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_907])).
% 4.13/1.86  tff(c_857, plain, (![A_9, C_103]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_103))=k2_xboole_0(k1_xboole_0, C_103))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_586])).
% 4.13/1.86  tff(c_1027, plain, (![A_121, C_122]: (k5_xboole_0(A_121, k5_xboole_0(A_121, C_122))=C_122)), inference(demodulation, [status(thm), theory('equality')], [c_928, c_857])).
% 4.13/1.86  tff(c_1800, plain, (![A_150, B_151]: (k5_xboole_0(A_150, k2_xboole_0(A_150, B_151))=k4_xboole_0(B_151, A_150))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1027])).
% 4.13/1.86  tff(c_1849, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_1800])).
% 4.13/1.86  tff(c_1858, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_537, c_1849])).
% 4.13/1.86  tff(c_24, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.13/1.86  tff(c_1073, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1027])).
% 4.13/1.86  tff(c_1862, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k5_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1858, c_1073])).
% 4.13/1.86  tff(c_1871, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1862])).
% 4.13/1.86  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.13/1.86  tff(c_2515, plain, (![D_174]: (r2_hidden(D_174, k1_tarski('#skF_7')) | ~r2_hidden(D_174, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1871, c_6])).
% 4.13/1.86  tff(c_62, plain, (![C_35, A_31]: (C_35=A_31 | ~r2_hidden(C_35, k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.13/1.86  tff(c_2531, plain, (![D_175]: (D_175='#skF_7' | ~r2_hidden(D_175, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_2515, c_62])).
% 4.13/1.86  tff(c_2559, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_64, c_2531])).
% 4.13/1.86  tff(c_2569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2559])).
% 4.13/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.86  
% 4.13/1.86  Inference rules
% 4.13/1.86  ----------------------
% 4.13/1.86  #Ref     : 0
% 4.13/1.86  #Sup     : 590
% 4.13/1.86  #Fact    : 0
% 4.13/1.86  #Define  : 0
% 4.13/1.86  #Split   : 0
% 4.13/1.86  #Chain   : 0
% 4.13/1.86  #Close   : 0
% 4.13/1.86  
% 4.13/1.86  Ordering : KBO
% 4.13/1.86  
% 4.13/1.86  Simplification rules
% 4.13/1.86  ----------------------
% 4.13/1.86  #Subsume      : 15
% 4.13/1.86  #Demod        : 394
% 4.13/1.86  #Tautology    : 404
% 4.13/1.86  #SimpNegUnit  : 1
% 4.13/1.86  #BackRed      : 4
% 4.13/1.86  
% 4.13/1.86  #Partial instantiations: 0
% 4.13/1.86  #Strategies tried      : 1
% 4.13/1.86  
% 4.13/1.86  Timing (in seconds)
% 4.13/1.86  ----------------------
% 4.13/1.87  Preprocessing        : 0.43
% 4.13/1.87  Parsing              : 0.22
% 4.13/1.87  CNF conversion       : 0.03
% 4.13/1.87  Main loop            : 0.60
% 4.13/1.87  Inferencing          : 0.21
% 4.13/1.87  Reduction            : 0.22
% 4.13/1.87  Demodulation         : 0.17
% 4.13/1.87  BG Simplification    : 0.03
% 4.13/1.87  Subsumption          : 0.09
% 4.13/1.87  Abstraction          : 0.03
% 4.13/1.87  MUC search           : 0.00
% 4.13/1.87  Cooper               : 0.00
% 4.13/1.87  Total                : 1.07
% 4.13/1.87  Index Insertion      : 0.00
% 4.13/1.87  Index Deletion       : 0.00
% 4.13/1.87  Index Matching       : 0.00
% 4.13/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------

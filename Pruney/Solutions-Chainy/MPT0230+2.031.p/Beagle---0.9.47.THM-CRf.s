%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:01 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   73 (  91 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   62 (  88 expanded)
%              Number of equality atoms :   50 (  68 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_82,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_80,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1367,plain,(
    ! [A_140,B_141,C_142,D_143] : k2_xboole_0(k1_enumset1(A_140,B_141,C_142),k1_tarski(D_143)) = k2_enumset1(A_140,B_141,C_142,D_143) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1406,plain,(
    ! [A_36,B_37,D_143] : k2_xboole_0(k2_tarski(A_36,B_37),k1_tarski(D_143)) = k2_enumset1(A_36,A_36,B_37,D_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1367])).

tff(c_1430,plain,(
    ! [A_144,B_145,D_146] : k2_xboole_0(k2_tarski(A_144,B_145),k1_tarski(D_146)) = k1_enumset1(A_144,B_145,D_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1406])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [A_90] : k3_xboole_0(k1_xboole_0,A_90) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_194,plain,(
    ! [A_90] : k3_xboole_0(A_90,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_2])).

tff(c_270,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_282,plain,(
    ! [A_90] : k5_xboole_0(A_90,k1_xboole_0) = k4_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_270])).

tff(c_297,plain,(
    ! [A_90] : k4_xboole_0(A_90,k1_xboole_0) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_282])).

tff(c_426,plain,(
    ! [A_101,B_102] : k4_xboole_0(A_101,k4_xboole_0(A_101,B_102)) = k3_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_451,plain,(
    ! [A_90] : k4_xboole_0(A_90,A_90) = k3_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_426])).

tff(c_463,plain,(
    ! [A_90] : k4_xboole_0(A_90,A_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_451])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_294,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_270])).

tff(c_84,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_166,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_159])).

tff(c_279,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_270])).

tff(c_418,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_279])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_422,plain,(
    k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5'))) = k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_16])).

tff(c_733,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_463,c_422])).

tff(c_1436,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_733])).

tff(c_20,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1464,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_20])).

tff(c_42,plain,(
    ! [D_27,B_23,A_22] :
      ( D_27 = B_23
      | D_27 = A_22
      | ~ r2_hidden(D_27,k2_tarski(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1482,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1464,c_42])).

tff(c_1486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_1482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.49  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 3.34/1.49  
% 3.34/1.49  %Foreground sorts:
% 3.34/1.49  
% 3.34/1.49  
% 3.34/1.49  %Background operators:
% 3.34/1.49  
% 3.34/1.49  
% 3.34/1.49  %Foreground operators:
% 3.34/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.34/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.34/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.34/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.34/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.34/1.49  
% 3.34/1.50  tff(f_97, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.34/1.50  tff(f_77, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.34/1.50  tff(f_75, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.34/1.50  tff(f_71, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.34/1.50  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.34/1.50  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.34/1.50  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.34/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.34/1.50  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.50  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.34/1.50  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.34/1.50  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.34/1.50  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.34/1.50  tff(f_67, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.34/1.50  tff(c_82, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.34/1.50  tff(c_80, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.34/1.50  tff(c_68, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.34/1.50  tff(c_66, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.34/1.50  tff(c_1367, plain, (![A_140, B_141, C_142, D_143]: (k2_xboole_0(k1_enumset1(A_140, B_141, C_142), k1_tarski(D_143))=k2_enumset1(A_140, B_141, C_142, D_143))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.50  tff(c_1406, plain, (![A_36, B_37, D_143]: (k2_xboole_0(k2_tarski(A_36, B_37), k1_tarski(D_143))=k2_enumset1(A_36, A_36, B_37, D_143))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1367])).
% 3.34/1.50  tff(c_1430, plain, (![A_144, B_145, D_146]: (k2_xboole_0(k2_tarski(A_144, B_145), k1_tarski(D_146))=k1_enumset1(A_144, B_145, D_146))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1406])).
% 3.34/1.50  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.50  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.50  tff(c_159, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.50  tff(c_189, plain, (![A_90]: (k3_xboole_0(k1_xboole_0, A_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_159])).
% 3.34/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.50  tff(c_194, plain, (![A_90]: (k3_xboole_0(A_90, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_189, c_2])).
% 3.34/1.50  tff(c_270, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.50  tff(c_282, plain, (![A_90]: (k5_xboole_0(A_90, k1_xboole_0)=k4_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_270])).
% 3.34/1.50  tff(c_297, plain, (![A_90]: (k4_xboole_0(A_90, k1_xboole_0)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_282])).
% 3.34/1.50  tff(c_426, plain, (![A_101, B_102]: (k4_xboole_0(A_101, k4_xboole_0(A_101, B_102))=k3_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.50  tff(c_451, plain, (![A_90]: (k4_xboole_0(A_90, A_90)=k3_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_297, c_426])).
% 3.34/1.50  tff(c_463, plain, (![A_90]: (k4_xboole_0(A_90, A_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_451])).
% 3.34/1.50  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.50  tff(c_294, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_270])).
% 3.34/1.50  tff(c_84, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.34/1.50  tff(c_166, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_84, c_159])).
% 3.34/1.50  tff(c_279, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_270])).
% 3.34/1.50  tff(c_418, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_279])).
% 3.34/1.50  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.50  tff(c_422, plain, (k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5')))=k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_418, c_16])).
% 3.34/1.50  tff(c_733, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_463, c_422])).
% 3.34/1.50  tff(c_1436, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1430, c_733])).
% 3.34/1.50  tff(c_20, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.34/1.50  tff(c_1464, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1436, c_20])).
% 3.34/1.50  tff(c_42, plain, (![D_27, B_23, A_22]: (D_27=B_23 | D_27=A_22 | ~r2_hidden(D_27, k2_tarski(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.34/1.50  tff(c_1482, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1464, c_42])).
% 3.34/1.50  tff(c_1486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_1482])).
% 3.34/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.50  
% 3.34/1.50  Inference rules
% 3.34/1.50  ----------------------
% 3.34/1.50  #Ref     : 0
% 3.34/1.50  #Sup     : 353
% 3.34/1.50  #Fact    : 0
% 3.34/1.50  #Define  : 0
% 3.34/1.50  #Split   : 0
% 3.34/1.50  #Chain   : 0
% 3.34/1.50  #Close   : 0
% 3.34/1.50  
% 3.34/1.50  Ordering : KBO
% 3.34/1.50  
% 3.34/1.50  Simplification rules
% 3.34/1.50  ----------------------
% 3.34/1.50  #Subsume      : 50
% 3.34/1.50  #Demod        : 201
% 3.34/1.50  #Tautology    : 251
% 3.34/1.50  #SimpNegUnit  : 1
% 3.34/1.50  #BackRed      : 2
% 3.34/1.50  
% 3.34/1.50  #Partial instantiations: 0
% 3.34/1.50  #Strategies tried      : 1
% 3.34/1.50  
% 3.34/1.50  Timing (in seconds)
% 3.34/1.50  ----------------------
% 3.34/1.50  Preprocessing        : 0.35
% 3.34/1.50  Parsing              : 0.17
% 3.34/1.50  CNF conversion       : 0.03
% 3.34/1.50  Main loop            : 0.40
% 3.34/1.50  Inferencing          : 0.13
% 3.34/1.50  Reduction            : 0.16
% 3.34/1.50  Demodulation         : 0.13
% 3.34/1.50  BG Simplification    : 0.02
% 3.34/1.50  Subsumption          : 0.06
% 3.34/1.50  Abstraction          : 0.02
% 3.34/1.50  MUC search           : 0.00
% 3.34/1.50  Cooper               : 0.00
% 3.34/1.50  Total                : 0.78
% 3.34/1.50  Index Insertion      : 0.00
% 3.34/1.50  Index Deletion       : 0.00
% 3.34/1.50  Index Matching       : 0.00
% 3.34/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

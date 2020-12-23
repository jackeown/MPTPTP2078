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

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   74 (  92 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 (  89 expanded)
%              Number of equality atoms :   51 (  69 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_73,axiom,(
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

tff(c_84,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_82,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_70,plain,(
    ! [A_42,B_43,C_44] : k2_enumset1(A_42,A_42,B_43,C_44) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_983,plain,(
    ! [A_142,B_143,C_144,D_145] : k2_xboole_0(k1_enumset1(A_142,B_143,C_144),k1_tarski(D_145)) = k2_enumset1(A_142,B_143,C_144,D_145) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1004,plain,(
    ! [A_40,B_41,D_145] : k2_xboole_0(k2_tarski(A_40,B_41),k1_tarski(D_145)) = k2_enumset1(A_40,A_40,B_41,D_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_983])).

tff(c_1008,plain,(
    ! [A_146,B_147,D_148] : k2_xboole_0(k2_tarski(A_146,B_147),k1_tarski(D_148)) = k1_enumset1(A_146,B_147,D_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1004])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_161,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(A_90,B_91) = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_191,plain,(
    ! [A_94] : k3_xboole_0(k1_xboole_0,A_94) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_161])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_196,plain,(
    ! [A_94] : k3_xboole_0(A_94,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_2])).

tff(c_393,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_405,plain,(
    ! [A_94] : k5_xboole_0(A_94,k1_xboole_0) = k4_xboole_0(A_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_393])).

tff(c_420,plain,(
    ! [A_94] : k4_xboole_0(A_94,k1_xboole_0) = A_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_405])).

tff(c_551,plain,(
    ! [A_110,B_111] : k4_xboole_0(A_110,k4_xboole_0(A_110,B_111)) = k3_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_576,plain,(
    ! [A_94] : k4_xboole_0(A_94,A_94) = k3_xboole_0(A_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_551])).

tff(c_588,plain,(
    ! [A_94] : k4_xboole_0(A_94,A_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_576])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_417,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_393])).

tff(c_86,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_168,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_161])).

tff(c_402,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_393])).

tff(c_467,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_402])).

tff(c_591,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_467])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_678,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_16])).

tff(c_682,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_678])).

tff(c_1014,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_682])).

tff(c_20,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1071,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_20])).

tff(c_42,plain,(
    ! [D_27,B_23,A_22] :
      ( D_27 = B_23
      | D_27 = A_22
      | ~ r2_hidden(D_27,k2_tarski(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1089,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1071,c_42])).

tff(c_1093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_82,c_1089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:28:23 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.40  
% 2.88/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.40  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.88/1.40  
% 2.88/1.40  %Foreground sorts:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Background operators:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Foreground operators:
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.88/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.88/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.88/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.88/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.88/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.88/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.88/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.88/1.40  
% 2.88/1.41  tff(f_99, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.88/1.41  tff(f_79, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.88/1.41  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.88/1.41  tff(f_73, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.88/1.41  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.88/1.41  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.88/1.41  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.88/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.88/1.41  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.88/1.41  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.88/1.41  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.88/1.41  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.88/1.41  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.88/1.41  tff(f_67, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.88/1.41  tff(c_84, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_82, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_70, plain, (![A_42, B_43, C_44]: (k2_enumset1(A_42, A_42, B_43, C_44)=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.41  tff(c_68, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.88/1.41  tff(c_983, plain, (![A_142, B_143, C_144, D_145]: (k2_xboole_0(k1_enumset1(A_142, B_143, C_144), k1_tarski(D_145))=k2_enumset1(A_142, B_143, C_144, D_145))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.88/1.41  tff(c_1004, plain, (![A_40, B_41, D_145]: (k2_xboole_0(k2_tarski(A_40, B_41), k1_tarski(D_145))=k2_enumset1(A_40, A_40, B_41, D_145))), inference(superposition, [status(thm), theory('equality')], [c_68, c_983])).
% 2.88/1.41  tff(c_1008, plain, (![A_146, B_147, D_148]: (k2_xboole_0(k2_tarski(A_146, B_147), k1_tarski(D_148))=k1_enumset1(A_146, B_147, D_148))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1004])).
% 2.88/1.41  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.88/1.41  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.41  tff(c_161, plain, (![A_90, B_91]: (k3_xboole_0(A_90, B_91)=A_90 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.41  tff(c_191, plain, (![A_94]: (k3_xboole_0(k1_xboole_0, A_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_161])).
% 2.88/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.88/1.41  tff(c_196, plain, (![A_94]: (k3_xboole_0(A_94, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_2])).
% 2.88/1.41  tff(c_393, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.41  tff(c_405, plain, (![A_94]: (k5_xboole_0(A_94, k1_xboole_0)=k4_xboole_0(A_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_196, c_393])).
% 2.88/1.41  tff(c_420, plain, (![A_94]: (k4_xboole_0(A_94, k1_xboole_0)=A_94)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_405])).
% 2.88/1.41  tff(c_551, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k4_xboole_0(A_110, B_111))=k3_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.41  tff(c_576, plain, (![A_94]: (k4_xboole_0(A_94, A_94)=k3_xboole_0(A_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_420, c_551])).
% 2.88/1.41  tff(c_588, plain, (![A_94]: (k4_xboole_0(A_94, A_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_576])).
% 2.88/1.41  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.41  tff(c_417, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_393])).
% 2.88/1.41  tff(c_86, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_168, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_86, c_161])).
% 2.88/1.41  tff(c_402, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_393])).
% 2.88/1.41  tff(c_467, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_402])).
% 2.88/1.41  tff(c_591, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_588, c_467])).
% 2.88/1.41  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.88/1.41  tff(c_678, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_591, c_16])).
% 2.88/1.41  tff(c_682, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_678])).
% 2.88/1.41  tff(c_1014, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1008, c_682])).
% 2.88/1.41  tff(c_20, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.88/1.41  tff(c_1071, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1014, c_20])).
% 2.88/1.41  tff(c_42, plain, (![D_27, B_23, A_22]: (D_27=B_23 | D_27=A_22 | ~r2_hidden(D_27, k2_tarski(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.41  tff(c_1089, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1071, c_42])).
% 2.88/1.41  tff(c_1093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_82, c_1089])).
% 2.88/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  Inference rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Ref     : 0
% 2.88/1.41  #Sup     : 243
% 2.88/1.41  #Fact    : 0
% 2.88/1.41  #Define  : 0
% 2.88/1.41  #Split   : 0
% 2.88/1.41  #Chain   : 0
% 2.88/1.41  #Close   : 0
% 2.88/1.41  
% 2.88/1.41  Ordering : KBO
% 2.88/1.41  
% 2.88/1.41  Simplification rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Subsume      : 0
% 2.88/1.41  #Demod        : 162
% 2.88/1.41  #Tautology    : 196
% 2.88/1.41  #SimpNegUnit  : 1
% 2.88/1.41  #BackRed      : 2
% 2.88/1.41  
% 2.88/1.41  #Partial instantiations: 0
% 2.88/1.41  #Strategies tried      : 1
% 2.88/1.41  
% 2.88/1.41  Timing (in seconds)
% 2.88/1.41  ----------------------
% 2.88/1.42  Preprocessing        : 0.34
% 2.88/1.42  Parsing              : 0.18
% 2.88/1.42  CNF conversion       : 0.03
% 2.88/1.42  Main loop            : 0.33
% 2.88/1.42  Inferencing          : 0.11
% 2.88/1.42  Reduction            : 0.13
% 2.88/1.42  Demodulation         : 0.10
% 2.88/1.42  BG Simplification    : 0.02
% 2.88/1.42  Subsumption          : 0.05
% 2.88/1.42  Abstraction          : 0.02
% 2.88/1.42  MUC search           : 0.00
% 2.88/1.42  Cooper               : 0.00
% 2.88/1.42  Total                : 0.71
% 2.88/1.42  Index Insertion      : 0.00
% 2.88/1.42  Index Deletion       : 0.00
% 2.88/1.42  Index Matching       : 0.00
% 2.88/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

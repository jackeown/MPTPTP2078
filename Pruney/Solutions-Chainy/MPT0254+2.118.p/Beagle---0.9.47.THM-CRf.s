%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:34 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  68 expanded)
%              Number of equality atoms :   37 (  51 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_91,plain,(
    ! [A_61] : k2_tarski(A_61,A_61) = k1_tarski(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [D_22,A_17] : r2_hidden(D_22,k2_tarski(A_17,D_22)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    ! [A_61] : r2_hidden(A_61,k1_tarski(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_22])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_206,plain,(
    ! [A_67,B_68] : r1_tarski(k4_xboole_0(A_67,B_68),k5_xboole_0(A_67,B_68)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_266,plain,(
    ! [A_74] : r1_tarski(k4_xboole_0(A_74,A_74),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_206])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_272,plain,(
    ! [A_74] : k4_xboole_0(A_74,A_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_266,c_8])).

tff(c_833,plain,(
    ! [A_109,B_110] :
      ( ~ r2_hidden(A_109,B_110)
      | k4_xboole_0(k1_tarski(A_109),B_110) != k1_tarski(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_844,plain,(
    ! [A_109] :
      ( ~ r2_hidden(A_109,k1_tarski(A_109))
      | k1_tarski(A_109) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_833])).

tff(c_847,plain,(
    ! [A_109] : k1_tarski(A_109) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_844])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_322,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k4_xboole_0(B_79,A_78)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_338,plain,(
    ! [A_74] : k5_xboole_0(A_74,k1_xboole_0) = k2_xboole_0(A_74,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_322])).

tff(c_345,plain,(
    ! [A_74] : k2_xboole_0(A_74,A_74) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_338])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_109,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,A_65) = k5_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_125,plain,(
    ! [A_65] : k5_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_10])).

tff(c_1062,plain,(
    ! [A_119,B_120,C_121] : k5_xboole_0(k5_xboole_0(A_119,B_120),C_121) = k5_xboole_0(A_119,k5_xboole_0(B_120,C_121)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1154,plain,(
    ! [A_12,C_121] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_121)) = k5_xboole_0(k1_xboole_0,C_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1062])).

tff(c_1168,plain,(
    ! [A_122,C_123] : k5_xboole_0(A_122,k5_xboole_0(A_122,C_123)) = C_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_1154])).

tff(c_2092,plain,(
    ! [A_165,B_166] : k5_xboole_0(A_165,k2_xboole_0(A_165,B_166)) = k4_xboole_0(B_166,A_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1168])).

tff(c_2165,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k4_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2092])).

tff(c_2177,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2165])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2201,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2177,c_6])).

tff(c_2212,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_58,c_2201])).

tff(c_2214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_847,c_2212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.54  
% 3.38/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.54  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.38/1.54  
% 3.38/1.54  %Foreground sorts:
% 3.38/1.54  
% 3.38/1.54  
% 3.38/1.54  %Background operators:
% 3.38/1.54  
% 3.38/1.54  
% 3.38/1.54  %Foreground operators:
% 3.38/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.38/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.38/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.38/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.54  
% 3.38/1.55  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.38/1.55  tff(f_54, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.38/1.55  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.38/1.55  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 3.38/1.55  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.38/1.55  tff(f_73, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.38/1.55  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.38/1.55  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.38/1.55  tff(f_79, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.38/1.55  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.38/1.55  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.38/1.55  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.38/1.55  tff(c_91, plain, (![A_61]: (k2_tarski(A_61, A_61)=k1_tarski(A_61))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.55  tff(c_22, plain, (![D_22, A_17]: (r2_hidden(D_22, k2_tarski(A_17, D_22)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.38/1.55  tff(c_97, plain, (![A_61]: (r2_hidden(A_61, k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_22])).
% 3.38/1.55  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.55  tff(c_206, plain, (![A_67, B_68]: (r1_tarski(k4_xboole_0(A_67, B_68), k5_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.38/1.55  tff(c_266, plain, (![A_74]: (r1_tarski(k4_xboole_0(A_74, A_74), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_206])).
% 3.38/1.55  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.38/1.55  tff(c_272, plain, (![A_74]: (k4_xboole_0(A_74, A_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_266, c_8])).
% 3.38/1.55  tff(c_833, plain, (![A_109, B_110]: (~r2_hidden(A_109, B_110) | k4_xboole_0(k1_tarski(A_109), B_110)!=k1_tarski(A_109))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.38/1.55  tff(c_844, plain, (![A_109]: (~r2_hidden(A_109, k1_tarski(A_109)) | k1_tarski(A_109)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_272, c_833])).
% 3.38/1.55  tff(c_847, plain, (![A_109]: (k1_tarski(A_109)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_844])).
% 3.38/1.55  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.38/1.55  tff(c_322, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k4_xboole_0(B_79, A_78))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.38/1.55  tff(c_338, plain, (![A_74]: (k5_xboole_0(A_74, k1_xboole_0)=k2_xboole_0(A_74, A_74))), inference(superposition, [status(thm), theory('equality')], [c_272, c_322])).
% 3.38/1.55  tff(c_345, plain, (![A_74]: (k2_xboole_0(A_74, A_74)=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_338])).
% 3.38/1.55  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.38/1.55  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.38/1.55  tff(c_109, plain, (![B_64, A_65]: (k5_xboole_0(B_64, A_65)=k5_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.55  tff(c_125, plain, (![A_65]: (k5_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_109, c_10])).
% 3.38/1.55  tff(c_1062, plain, (![A_119, B_120, C_121]: (k5_xboole_0(k5_xboole_0(A_119, B_120), C_121)=k5_xboole_0(A_119, k5_xboole_0(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.38/1.55  tff(c_1154, plain, (![A_12, C_121]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_121))=k5_xboole_0(k1_xboole_0, C_121))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1062])).
% 3.38/1.55  tff(c_1168, plain, (![A_122, C_123]: (k5_xboole_0(A_122, k5_xboole_0(A_122, C_123))=C_123)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_1154])).
% 3.38/1.55  tff(c_2092, plain, (![A_165, B_166]: (k5_xboole_0(A_165, k2_xboole_0(A_165, B_166))=k4_xboole_0(B_166, A_165))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1168])).
% 3.38/1.55  tff(c_2165, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k4_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2092])).
% 3.38/1.55  tff(c_2177, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2165])).
% 3.38/1.55  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.55  tff(c_2201, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2177, c_6])).
% 3.38/1.55  tff(c_2212, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_345, c_58, c_2201])).
% 3.38/1.55  tff(c_2214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_847, c_2212])).
% 3.38/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.55  
% 3.38/1.55  Inference rules
% 3.38/1.55  ----------------------
% 3.38/1.55  #Ref     : 0
% 3.38/1.55  #Sup     : 514
% 3.38/1.55  #Fact    : 0
% 3.38/1.55  #Define  : 0
% 3.38/1.55  #Split   : 1
% 3.38/1.55  #Chain   : 0
% 3.38/1.55  #Close   : 0
% 3.38/1.55  
% 3.38/1.55  Ordering : KBO
% 3.38/1.55  
% 3.38/1.55  Simplification rules
% 3.38/1.55  ----------------------
% 3.38/1.55  #Subsume      : 6
% 3.38/1.55  #Demod        : 426
% 3.38/1.55  #Tautology    : 372
% 3.38/1.55  #SimpNegUnit  : 5
% 3.38/1.55  #BackRed      : 18
% 3.38/1.55  
% 3.38/1.55  #Partial instantiations: 0
% 3.38/1.55  #Strategies tried      : 1
% 3.38/1.55  
% 3.38/1.55  Timing (in seconds)
% 3.38/1.55  ----------------------
% 3.38/1.56  Preprocessing        : 0.32
% 3.38/1.56  Parsing              : 0.17
% 3.38/1.56  CNF conversion       : 0.02
% 3.38/1.56  Main loop            : 0.48
% 3.38/1.56  Inferencing          : 0.16
% 3.38/1.56  Reduction            : 0.19
% 3.38/1.56  Demodulation         : 0.16
% 3.38/1.56  BG Simplification    : 0.02
% 3.38/1.56  Subsumption          : 0.07
% 3.38/1.56  Abstraction          : 0.03
% 3.38/1.56  MUC search           : 0.00
% 3.38/1.56  Cooper               : 0.00
% 3.38/1.56  Total                : 0.82
% 3.38/1.56  Index Insertion      : 0.00
% 3.38/1.56  Index Deletion       : 0.00
% 3.38/1.56  Index Matching       : 0.00
% 3.38/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------

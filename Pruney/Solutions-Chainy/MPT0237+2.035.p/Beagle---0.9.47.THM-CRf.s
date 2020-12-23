%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:49 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 117 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 125 expanded)
%              Number of equality atoms :   50 (  99 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_108])).

tff(c_286,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k4_xboole_0(B_77,A_76)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_301,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k2_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_286])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_183,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_200,plain,(
    ! [A_69] : k3_xboole_0(k1_xboole_0,A_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_183])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_205,plain,(
    ! [A_69] : k3_xboole_0(A_69,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_2])).

tff(c_345,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_365,plain,(
    ! [A_69] : k5_xboole_0(A_69,k1_xboole_0) = k4_xboole_0(A_69,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_345])).

tff(c_380,plain,(
    ! [A_69] : k2_xboole_0(A_69,k1_xboole_0) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_14,c_365])).

tff(c_398,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_301])).

tff(c_22,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_47,B_48] : r1_tarski(k1_tarski(A_47),k2_tarski(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_66,plain,(
    ! [A_15] : r1_tarski(k1_tarski(A_15),k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_122,plain,(
    ! [A_15] : k4_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_108])).

tff(c_298,plain,(
    ! [A_15] : k2_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k5_xboole_0(k1_tarski(A_15),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_286])).

tff(c_579,plain,(
    ! [A_102] : k2_xboole_0(k1_tarski(A_102),k1_tarski(A_102)) = k1_tarski(A_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_298])).

tff(c_149,plain,(
    ! [A_62,B_63] : k3_tarski(k2_tarski(A_62,B_63)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_158,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_149])).

tff(c_585,plain,(
    ! [A_102] : k3_tarski(k1_tarski(k1_tarski(A_102))) = k1_tarski(A_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_158])).

tff(c_178,plain,(
    ! [A_65,B_66] :
      ( r1_xboole_0(k1_tarski(A_65),k1_tarski(B_66))
      | B_66 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_554,plain,(
    ! [A_100,B_101] :
      ( k4_xboole_0(k1_tarski(A_100),k1_tarski(B_101)) = k1_tarski(A_100)
      | B_101 = A_100 ) ),
    inference(resolution,[status(thm)],[c_178,c_16])).

tff(c_20,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_627,plain,(
    ! [B_111,A_112] :
      ( k5_xboole_0(k1_tarski(B_111),k1_tarski(A_112)) = k2_xboole_0(k1_tarski(B_111),k1_tarski(A_112))
      | B_111 = A_112 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_20])).

tff(c_40,plain,(
    ! [A_42,B_43] :
      ( k5_xboole_0(k1_tarski(A_42),k1_tarski(B_43)) = k2_tarski(A_42,B_43)
      | B_43 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_791,plain,(
    ! [B_127,A_128] :
      ( k2_xboole_0(k1_tarski(B_127),k1_tarski(A_128)) = k2_tarski(B_127,A_128)
      | B_127 = A_128
      | B_127 = A_128 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_40])).

tff(c_34,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_821,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_43])).

tff(c_827,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_821,c_43])).

tff(c_830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_158,c_22,c_827])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:18:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.36  %$ r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.65/1.36  
% 2.65/1.36  %Foreground sorts:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Background operators:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Foreground operators:
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.36  
% 2.65/1.38  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.65/1.38  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.65/1.38  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.65/1.38  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.65/1.38  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.65/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.65/1.38  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.65/1.38  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.65/1.38  tff(f_63, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.65/1.38  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.65/1.38  tff(f_68, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.65/1.38  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.65/1.38  tff(f_73, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.65/1.38  tff(f_76, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.65/1.38  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.38  tff(c_108, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.38  tff(c_124, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_108])).
% 2.65/1.38  tff(c_286, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k4_xboole_0(B_77, A_76))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.38  tff(c_301, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k2_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_124, c_286])).
% 2.65/1.38  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.38  tff(c_183, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.38  tff(c_200, plain, (![A_69]: (k3_xboole_0(k1_xboole_0, A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_183])).
% 2.65/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.38  tff(c_205, plain, (![A_69]: (k3_xboole_0(A_69, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_200, c_2])).
% 2.65/1.38  tff(c_345, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.38  tff(c_365, plain, (![A_69]: (k5_xboole_0(A_69, k1_xboole_0)=k4_xboole_0(A_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_205, c_345])).
% 2.65/1.38  tff(c_380, plain, (![A_69]: (k2_xboole_0(A_69, k1_xboole_0)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_14, c_365])).
% 2.65/1.38  tff(c_398, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_380, c_301])).
% 2.65/1.38  tff(c_22, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.38  tff(c_63, plain, (![A_47, B_48]: (r1_tarski(k1_tarski(A_47), k2_tarski(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.38  tff(c_66, plain, (![A_15]: (r1_tarski(k1_tarski(A_15), k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_63])).
% 2.65/1.38  tff(c_122, plain, (![A_15]: (k4_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_108])).
% 2.65/1.38  tff(c_298, plain, (![A_15]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k5_xboole_0(k1_tarski(A_15), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_122, c_286])).
% 2.65/1.38  tff(c_579, plain, (![A_102]: (k2_xboole_0(k1_tarski(A_102), k1_tarski(A_102))=k1_tarski(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_298])).
% 2.65/1.38  tff(c_149, plain, (![A_62, B_63]: (k3_tarski(k2_tarski(A_62, B_63))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.38  tff(c_158, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_22, c_149])).
% 2.65/1.38  tff(c_585, plain, (![A_102]: (k3_tarski(k1_tarski(k1_tarski(A_102)))=k1_tarski(A_102))), inference(superposition, [status(thm), theory('equality')], [c_579, c_158])).
% 2.65/1.38  tff(c_178, plain, (![A_65, B_66]: (r1_xboole_0(k1_tarski(A_65), k1_tarski(B_66)) | B_66=A_65)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.65/1.38  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.65/1.38  tff(c_554, plain, (![A_100, B_101]: (k4_xboole_0(k1_tarski(A_100), k1_tarski(B_101))=k1_tarski(A_100) | B_101=A_100)), inference(resolution, [status(thm)], [c_178, c_16])).
% 2.65/1.38  tff(c_20, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.38  tff(c_627, plain, (![B_111, A_112]: (k5_xboole_0(k1_tarski(B_111), k1_tarski(A_112))=k2_xboole_0(k1_tarski(B_111), k1_tarski(A_112)) | B_111=A_112)), inference(superposition, [status(thm), theory('equality')], [c_554, c_20])).
% 2.65/1.38  tff(c_40, plain, (![A_42, B_43]: (k5_xboole_0(k1_tarski(A_42), k1_tarski(B_43))=k2_tarski(A_42, B_43) | B_43=A_42)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.65/1.38  tff(c_791, plain, (![B_127, A_128]: (k2_xboole_0(k1_tarski(B_127), k1_tarski(A_128))=k2_tarski(B_127, A_128) | B_127=A_128 | B_127=A_128)), inference(superposition, [status(thm), theory('equality')], [c_627, c_40])).
% 2.65/1.38  tff(c_34, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.38  tff(c_42, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.65/1.38  tff(c_43, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 2.65/1.38  tff(c_821, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_791, c_43])).
% 2.65/1.38  tff(c_827, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_821, c_821, c_43])).
% 2.65/1.38  tff(c_830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_585, c_158, c_22, c_827])).
% 2.65/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.38  
% 2.65/1.38  Inference rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Ref     : 0
% 2.65/1.38  #Sup     : 183
% 2.65/1.38  #Fact    : 0
% 2.65/1.38  #Define  : 0
% 2.65/1.38  #Split   : 0
% 2.65/1.38  #Chain   : 0
% 2.65/1.38  #Close   : 0
% 2.65/1.38  
% 2.65/1.38  Ordering : KBO
% 2.65/1.38  
% 2.65/1.38  Simplification rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Subsume      : 7
% 2.65/1.38  #Demod        : 77
% 2.65/1.38  #Tautology    : 142
% 2.65/1.38  #SimpNegUnit  : 0
% 2.65/1.38  #BackRed      : 2
% 2.65/1.38  
% 2.65/1.38  #Partial instantiations: 0
% 2.65/1.38  #Strategies tried      : 1
% 2.65/1.38  
% 2.65/1.38  Timing (in seconds)
% 2.65/1.38  ----------------------
% 2.65/1.38  Preprocessing        : 0.30
% 2.65/1.38  Parsing              : 0.16
% 2.65/1.38  CNF conversion       : 0.02
% 2.65/1.38  Main loop            : 0.30
% 2.65/1.38  Inferencing          : 0.12
% 2.65/1.38  Reduction            : 0.10
% 2.65/1.38  Demodulation         : 0.08
% 2.65/1.38  BG Simplification    : 0.02
% 2.65/1.38  Subsumption          : 0.04
% 2.65/1.38  Abstraction          : 0.02
% 2.65/1.38  MUC search           : 0.00
% 2.65/1.38  Cooper               : 0.00
% 2.65/1.38  Total                : 0.63
% 2.65/1.38  Index Insertion      : 0.00
% 2.65/1.38  Index Deletion       : 0.00
% 2.65/1.38  Index Matching       : 0.00
% 2.65/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:24 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 209 expanded)
%              Number of leaves         :   33 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :   65 ( 276 expanded)
%              Number of equality atoms :   53 ( 234 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_56,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_26])).

tff(c_959,plain,(
    ! [B_119,A_120] :
      ( k1_tarski(B_119) = A_120
      | k1_xboole_0 = A_120
      | ~ r1_tarski(A_120,k1_tarski(B_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_980,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_92,c_959])).

tff(c_992,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_980])).

tff(c_458,plain,(
    ! [A_87,B_88,C_89] : r1_tarski(k3_xboole_0(A_87,B_88),k2_xboole_0(A_87,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_495,plain,(
    ! [B_90] : r1_tarski(k3_xboole_0('#skF_2',B_90),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_458])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_645,plain,(
    ! [B_99] : k3_xboole_0(k3_xboole_0('#skF_2',B_99),k1_tarski('#skF_1')) = k3_xboole_0('#skF_2',B_99) ),
    inference(resolution,[status(thm)],[c_495,c_20])).

tff(c_698,plain,(
    ! [A_1] : k3_xboole_0(k3_xboole_0(A_1,'#skF_2'),k1_tarski('#skF_1')) = k3_xboole_0('#skF_2',A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_645])).

tff(c_3441,plain,(
    ! [A_1] : k3_xboole_0('#skF_2',k3_xboole_0(A_1,'#skF_2')) = k3_xboole_0('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_992,c_698])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [B_68,A_69] : k5_xboole_0(B_68,A_69) = k5_xboole_0(A_69,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_172,plain,(
    ! [A_69] : k5_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_24])).

tff(c_30,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1256,plain,(
    ! [A_125,B_126,C_127] : k5_xboole_0(k5_xboole_0(A_125,B_126),C_127) = k5_xboole_0(A_125,k5_xboole_0(B_126,C_127)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1313,plain,(
    ! [A_26,C_127] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_127)) = k5_xboole_0(k1_xboole_0,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1256])).

tff(c_1429,plain,(
    ! [A_131,C_132] : k5_xboole_0(A_131,k5_xboole_0(A_131,C_132)) = C_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_1313])).

tff(c_1472,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1429])).

tff(c_1004,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_58])).

tff(c_1373,plain,(
    ! [A_129,B_130] : k4_xboole_0(k2_xboole_0(A_129,B_130),k3_xboole_0(A_129,B_130)) = k5_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1394,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1004,c_1373])).

tff(c_1421,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) = k5_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_1394])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4738,plain,(
    ! [A_212,B_213] : k5_xboole_0(A_212,k4_xboole_0(A_212,B_213)) = k3_xboole_0(A_212,B_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1429])).

tff(c_4779,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1421,c_4738])).

tff(c_4838,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3441,c_1472,c_4779])).

tff(c_516,plain,(
    ! [B_2] : r1_tarski(k3_xboole_0(B_2,'#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_495])).

tff(c_984,plain,(
    ! [B_2] :
      ( k3_xboole_0(B_2,'#skF_2') = k1_tarski('#skF_1')
      | k3_xboole_0(B_2,'#skF_2') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_516,c_959])).

tff(c_3172,plain,(
    ! [B_2] :
      ( k3_xboole_0(B_2,'#skF_2') = '#skF_2'
      | k3_xboole_0(B_2,'#skF_2') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_984])).

tff(c_4875,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4838,c_3172])).

tff(c_4917,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4838,c_4875])).

tff(c_4919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_56,c_4917])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.94  
% 4.88/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.94  %$ r2_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.88/1.94  
% 4.88/1.94  %Foreground sorts:
% 4.88/1.94  
% 4.88/1.94  
% 4.88/1.94  %Background operators:
% 4.88/1.94  
% 4.88/1.94  
% 4.88/1.94  %Foreground operators:
% 4.88/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.88/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.88/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/1.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.88/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.88/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.88/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.88/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.88/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.88/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.88/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.88/1.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.88/1.94  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.88/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.88/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.88/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.88/1.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.88/1.94  
% 4.88/1.95  tff(f_94, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 4.88/1.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.88/1.95  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.88/1.95  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.88/1.95  tff(f_53, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 4.88/1.95  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.88/1.95  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.88/1.95  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.88/1.95  tff(f_61, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.88/1.95  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.88/1.95  tff(f_38, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 4.88/1.95  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.88/1.95  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.95  tff(c_56, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.88/1.95  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.95  tff(c_58, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.95  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.88/1.95  tff(c_92, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_26])).
% 4.88/1.95  tff(c_959, plain, (![B_119, A_120]: (k1_tarski(B_119)=A_120 | k1_xboole_0=A_120 | ~r1_tarski(A_120, k1_tarski(B_119)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.88/1.95  tff(c_980, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_92, c_959])).
% 4.88/1.95  tff(c_992, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_980])).
% 4.88/1.95  tff(c_458, plain, (![A_87, B_88, C_89]: (r1_tarski(k3_xboole_0(A_87, B_88), k2_xboole_0(A_87, C_89)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.88/1.95  tff(c_495, plain, (![B_90]: (r1_tarski(k3_xboole_0('#skF_2', B_90), k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_458])).
% 4.88/1.95  tff(c_20, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.88/1.95  tff(c_645, plain, (![B_99]: (k3_xboole_0(k3_xboole_0('#skF_2', B_99), k1_tarski('#skF_1'))=k3_xboole_0('#skF_2', B_99))), inference(resolution, [status(thm)], [c_495, c_20])).
% 4.88/1.95  tff(c_698, plain, (![A_1]: (k3_xboole_0(k3_xboole_0(A_1, '#skF_2'), k1_tarski('#skF_1'))=k3_xboole_0('#skF_2', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_645])).
% 4.88/1.95  tff(c_3441, plain, (![A_1]: (k3_xboole_0('#skF_2', k3_xboole_0(A_1, '#skF_2'))=k3_xboole_0('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_992, c_698])).
% 4.88/1.95  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.88/1.95  tff(c_156, plain, (![B_68, A_69]: (k5_xboole_0(B_68, A_69)=k5_xboole_0(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.88/1.95  tff(c_24, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.88/1.95  tff(c_172, plain, (![A_69]: (k5_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_156, c_24])).
% 4.88/1.95  tff(c_30, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.88/1.95  tff(c_1256, plain, (![A_125, B_126, C_127]: (k5_xboole_0(k5_xboole_0(A_125, B_126), C_127)=k5_xboole_0(A_125, k5_xboole_0(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.88/1.95  tff(c_1313, plain, (![A_26, C_127]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_127))=k5_xboole_0(k1_xboole_0, C_127))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1256])).
% 4.88/1.95  tff(c_1429, plain, (![A_131, C_132]: (k5_xboole_0(A_131, k5_xboole_0(A_131, C_132))=C_132)), inference(demodulation, [status(thm), theory('equality')], [c_172, c_1313])).
% 4.88/1.95  tff(c_1472, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1429])).
% 4.88/1.95  tff(c_1004, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_992, c_58])).
% 4.88/1.95  tff(c_1373, plain, (![A_129, B_130]: (k4_xboole_0(k2_xboole_0(A_129, B_130), k3_xboole_0(A_129, B_130))=k5_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.88/1.95  tff(c_1394, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1004, c_1373])).
% 4.88/1.95  tff(c_1421, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))=k5_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_1394])).
% 4.88/1.95  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.88/1.95  tff(c_4738, plain, (![A_212, B_213]: (k5_xboole_0(A_212, k4_xboole_0(A_212, B_213))=k3_xboole_0(A_212, B_213))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1429])).
% 4.88/1.95  tff(c_4779, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1421, c_4738])).
% 4.88/1.95  tff(c_4838, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3441, c_1472, c_4779])).
% 4.88/1.95  tff(c_516, plain, (![B_2]: (r1_tarski(k3_xboole_0(B_2, '#skF_2'), k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_495])).
% 4.88/1.95  tff(c_984, plain, (![B_2]: (k3_xboole_0(B_2, '#skF_2')=k1_tarski('#skF_1') | k3_xboole_0(B_2, '#skF_2')=k1_xboole_0)), inference(resolution, [status(thm)], [c_516, c_959])).
% 4.88/1.95  tff(c_3172, plain, (![B_2]: (k3_xboole_0(B_2, '#skF_2')='#skF_2' | k3_xboole_0(B_2, '#skF_2')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_992, c_984])).
% 4.88/1.95  tff(c_4875, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4838, c_3172])).
% 4.88/1.95  tff(c_4917, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4838, c_4875])).
% 4.88/1.95  tff(c_4919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_56, c_4917])).
% 4.88/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.95  
% 4.88/1.95  Inference rules
% 4.88/1.95  ----------------------
% 4.88/1.95  #Ref     : 0
% 4.88/1.95  #Sup     : 1187
% 4.88/1.95  #Fact    : 2
% 4.88/1.95  #Define  : 0
% 4.88/1.95  #Split   : 0
% 4.88/1.95  #Chain   : 0
% 4.88/1.95  #Close   : 0
% 4.88/1.95  
% 4.88/1.95  Ordering : KBO
% 4.88/1.95  
% 4.88/1.95  Simplification rules
% 4.88/1.95  ----------------------
% 4.88/1.95  #Subsume      : 34
% 4.88/1.95  #Demod        : 1077
% 4.88/1.95  #Tautology    : 858
% 4.88/1.95  #SimpNegUnit  : 21
% 4.88/1.95  #BackRed      : 34
% 4.88/1.95  
% 4.88/1.95  #Partial instantiations: 0
% 4.88/1.95  #Strategies tried      : 1
% 4.88/1.95  
% 4.88/1.95  Timing (in seconds)
% 4.88/1.95  ----------------------
% 4.88/1.95  Preprocessing        : 0.33
% 4.88/1.95  Parsing              : 0.18
% 4.88/1.95  CNF conversion       : 0.02
% 4.88/1.95  Main loop            : 0.83
% 4.88/1.95  Inferencing          : 0.25
% 4.88/1.95  Reduction            : 0.38
% 4.88/1.95  Demodulation         : 0.31
% 4.88/1.95  BG Simplification    : 0.03
% 4.88/1.95  Subsumption          : 0.11
% 4.88/1.95  Abstraction          : 0.04
% 4.88/1.95  MUC search           : 0.00
% 4.88/1.95  Cooper               : 0.00
% 4.88/1.96  Total                : 1.19
% 4.88/1.96  Index Insertion      : 0.00
% 4.88/1.96  Index Deletion       : 0.00
% 4.88/1.96  Index Matching       : 0.00
% 4.88/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------

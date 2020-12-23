%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:18 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 110 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 128 expanded)
%              Number of equality atoms :   44 (  66 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_71,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_144,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | k4_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_148,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_59])).

tff(c_24,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_49,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    ! [A_22] : r1_tarski(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_49])).

tff(c_149,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_163,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_149])).

tff(c_256,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_275,plain,(
    ! [A_22] : k3_xboole_0(A_22,A_22) = A_22 ),
    inference(resolution,[status(thm)],[c_52,c_256])).

tff(c_312,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_324,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k4_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_312])).

tff(c_340,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_324])).

tff(c_32,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_277,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_256])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2373,plain,(
    ! [A_110,B_111] : k3_xboole_0(k4_xboole_0(A_110,B_111),A_110) = k4_xboole_0(A_110,B_111) ),
    inference(resolution,[status(thm)],[c_22,c_256])).

tff(c_954,plain,(
    ! [A_82,B_83,C_84] : k3_xboole_0(k3_xboole_0(A_82,B_83),C_84) = k3_xboole_0(A_82,k3_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1018,plain,(
    ! [C_84] : k3_xboole_0('#skF_3',k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),C_84)) = k3_xboole_0('#skF_3',C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_954])).

tff(c_2413,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2373,c_1018])).

tff(c_2513,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_2,c_2413])).

tff(c_330,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_312])).

tff(c_2547,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2513,c_330])).

tff(c_2579,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_2547])).

tff(c_2581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_2579])).

tff(c_2582,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_20,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3258,plain,(
    ! [A_145,B_146] : k5_xboole_0(A_145,k3_xboole_0(A_145,B_146)) = k4_xboole_0(A_145,B_146) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3288,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3258])).

tff(c_3295,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3288])).

tff(c_28,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2874,plain,(
    ! [A_127,B_128,C_129] :
      ( ~ r1_xboole_0(A_127,B_128)
      | ~ r2_hidden(C_129,k3_xboole_0(A_127,B_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3334,plain,(
    ! [A_149,B_150] :
      ( ~ r1_xboole_0(A_149,B_150)
      | k3_xboole_0(A_149,B_150) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_2874])).

tff(c_3348,plain,(
    ! [A_25,B_26] : k3_xboole_0(k4_xboole_0(A_25,B_26),B_26) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_3334])).

tff(c_2746,plain,(
    ! [A_123,B_124] :
      ( k3_xboole_0(A_123,B_124) = A_123
      | ~ r1_tarski(A_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2771,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_2746])).

tff(c_3438,plain,(
    ! [A_153,B_154,C_155] : k3_xboole_0(k3_xboole_0(A_153,B_154),C_155) = k3_xboole_0(A_153,k3_xboole_0(B_154,C_155)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3622,plain,(
    ! [C_158] : k3_xboole_0('#skF_3',k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),C_158)) = k3_xboole_0('#skF_3',C_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_2771,c_3438])).

tff(c_3657,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3348,c_3622])).

tff(c_3681,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3657])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3690,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3681,c_14])).

tff(c_3709,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3295,c_3690])).

tff(c_3730,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3709,c_28])).

tff(c_3740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2582,c_3730])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:29:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.75  
% 3.78/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.75  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.78/1.75  
% 3.78/1.75  %Foreground sorts:
% 3.78/1.75  
% 3.78/1.75  
% 3.78/1.75  %Background operators:
% 3.78/1.75  
% 3.78/1.75  
% 3.78/1.75  %Foreground operators:
% 3.78/1.75  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.78/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.78/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.78/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.75  tff('#skF_5', type, '#skF_5': $i).
% 3.78/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.78/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.78/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.78/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.78/1.75  
% 4.14/1.77  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.14/1.77  tff(f_78, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.14/1.77  tff(f_67, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.14/1.77  tff(f_65, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.14/1.77  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.14/1.77  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.14/1.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.14/1.77  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.14/1.77  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.14/1.77  tff(f_71, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.14/1.77  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.14/1.77  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.14/1.77  tff(c_144, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | k4_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.14/1.77  tff(c_30, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.14/1.77  tff(c_59, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 4.14/1.77  tff(c_148, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_59])).
% 4.14/1.77  tff(c_24, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.14/1.77  tff(c_49, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.14/1.77  tff(c_52, plain, (![A_22]: (r1_tarski(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_24, c_49])).
% 4.14/1.77  tff(c_149, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.14/1.77  tff(c_163, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_149])).
% 4.14/1.77  tff(c_256, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.14/1.77  tff(c_275, plain, (![A_22]: (k3_xboole_0(A_22, A_22)=A_22)), inference(resolution, [status(thm)], [c_52, c_256])).
% 4.14/1.77  tff(c_312, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.14/1.77  tff(c_324, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k4_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_275, c_312])).
% 4.14/1.77  tff(c_340, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_324])).
% 4.14/1.77  tff(c_32, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.14/1.77  tff(c_277, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_256])).
% 4.14/1.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.14/1.77  tff(c_22, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.14/1.77  tff(c_2373, plain, (![A_110, B_111]: (k3_xboole_0(k4_xboole_0(A_110, B_111), A_110)=k4_xboole_0(A_110, B_111))), inference(resolution, [status(thm)], [c_22, c_256])).
% 4.14/1.77  tff(c_954, plain, (![A_82, B_83, C_84]: (k3_xboole_0(k3_xboole_0(A_82, B_83), C_84)=k3_xboole_0(A_82, k3_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.14/1.77  tff(c_1018, plain, (![C_84]: (k3_xboole_0('#skF_3', k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), C_84))=k3_xboole_0('#skF_3', C_84))), inference(superposition, [status(thm), theory('equality')], [c_277, c_954])).
% 4.14/1.77  tff(c_2413, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2373, c_1018])).
% 4.14/1.77  tff(c_2513, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_277, c_2, c_2413])).
% 4.14/1.77  tff(c_330, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_312])).
% 4.14/1.77  tff(c_2547, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2513, c_330])).
% 4.14/1.77  tff(c_2579, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_340, c_2547])).
% 4.14/1.77  tff(c_2581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_2579])).
% 4.14/1.77  tff(c_2582, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 4.14/1.77  tff(c_20, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.14/1.77  tff(c_3258, plain, (![A_145, B_146]: (k5_xboole_0(A_145, k3_xboole_0(A_145, B_146))=k4_xboole_0(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.14/1.77  tff(c_3288, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3258])).
% 4.14/1.77  tff(c_3295, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3288])).
% 4.14/1.77  tff(c_28, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.14/1.77  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/1.77  tff(c_2874, plain, (![A_127, B_128, C_129]: (~r1_xboole_0(A_127, B_128) | ~r2_hidden(C_129, k3_xboole_0(A_127, B_128)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.14/1.77  tff(c_3334, plain, (![A_149, B_150]: (~r1_xboole_0(A_149, B_150) | k3_xboole_0(A_149, B_150)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2874])).
% 4.14/1.77  tff(c_3348, plain, (![A_25, B_26]: (k3_xboole_0(k4_xboole_0(A_25, B_26), B_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_3334])).
% 4.14/1.77  tff(c_2746, plain, (![A_123, B_124]: (k3_xboole_0(A_123, B_124)=A_123 | ~r1_tarski(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.14/1.77  tff(c_2771, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_2746])).
% 4.14/1.77  tff(c_3438, plain, (![A_153, B_154, C_155]: (k3_xboole_0(k3_xboole_0(A_153, B_154), C_155)=k3_xboole_0(A_153, k3_xboole_0(B_154, C_155)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.14/1.77  tff(c_3622, plain, (![C_158]: (k3_xboole_0('#skF_3', k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), C_158))=k3_xboole_0('#skF_3', C_158))), inference(superposition, [status(thm), theory('equality')], [c_2771, c_3438])).
% 4.14/1.77  tff(c_3657, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3348, c_3622])).
% 4.14/1.77  tff(c_3681, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3657])).
% 4.14/1.77  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.14/1.77  tff(c_3690, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3681, c_14])).
% 4.14/1.77  tff(c_3709, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3295, c_3690])).
% 4.14/1.77  tff(c_3730, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3709, c_28])).
% 4.14/1.77  tff(c_3740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2582, c_3730])).
% 4.14/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.77  
% 4.14/1.77  Inference rules
% 4.14/1.77  ----------------------
% 4.14/1.77  #Ref     : 0
% 4.14/1.77  #Sup     : 939
% 4.14/1.77  #Fact    : 0
% 4.14/1.77  #Define  : 0
% 4.14/1.77  #Split   : 6
% 4.14/1.77  #Chain   : 0
% 4.14/1.77  #Close   : 0
% 4.14/1.77  
% 4.14/1.77  Ordering : KBO
% 4.14/1.77  
% 4.14/1.77  Simplification rules
% 4.14/1.77  ----------------------
% 4.14/1.77  #Subsume      : 28
% 4.14/1.77  #Demod        : 621
% 4.14/1.77  #Tautology    : 660
% 4.14/1.77  #SimpNegUnit  : 12
% 4.14/1.77  #BackRed      : 0
% 4.14/1.77  
% 4.14/1.77  #Partial instantiations: 0
% 4.14/1.77  #Strategies tried      : 1
% 4.14/1.77  
% 4.14/1.77  Timing (in seconds)
% 4.14/1.77  ----------------------
% 4.14/1.77  Preprocessing        : 0.29
% 4.14/1.77  Parsing              : 0.17
% 4.14/1.77  CNF conversion       : 0.02
% 4.14/1.77  Main loop            : 0.64
% 4.14/1.77  Inferencing          : 0.22
% 4.14/1.77  Reduction            : 0.27
% 4.14/1.77  Demodulation         : 0.21
% 4.14/1.77  BG Simplification    : 0.02
% 4.14/1.77  Subsumption          : 0.09
% 4.14/1.77  Abstraction          : 0.03
% 4.14/1.77  MUC search           : 0.00
% 4.14/1.77  Cooper               : 0.00
% 4.14/1.77  Total                : 0.97
% 4.14/1.77  Index Insertion      : 0.00
% 4.14/1.77  Index Deletion       : 0.00
% 4.14/1.77  Index Matching       : 0.00
% 4.14/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------

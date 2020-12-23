%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:12 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   62 (  72 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 (  81 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_117,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_65,plain,(
    ! [A_33,B_34] : r1_xboole_0(k4_xboole_0(A_33,B_34),B_34) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_65])).

tff(c_177,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_177])).

tff(c_505,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_532,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_505])).

tff(c_536,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_532])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_358,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_379,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_358])).

tff(c_537,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_379])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_159,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_159])).

tff(c_376,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_358])).

tff(c_597,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_376])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_607,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_20])).

tff(c_618,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14,c_607])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(k2_xboole_0(A_9,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1449,plain,(
    ! [C_108] :
      ( r1_tarski('#skF_1',C_108)
      | ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),C_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_12])).

tff(c_1489,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_1449])).

tff(c_1507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_1489])).

tff(c_1508,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2278,plain,(
    ! [A_149,C_150,B_151] :
      ( r1_xboole_0(A_149,C_150)
      | ~ r1_xboole_0(B_151,C_150)
      | ~ r1_tarski(A_149,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2782,plain,(
    ! [A_164,B_165,A_166] :
      ( r1_xboole_0(A_164,B_165)
      | ~ r1_tarski(A_164,k4_xboole_0(A_166,B_165)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2278])).

tff(c_2820,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2782])).

tff(c_2838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1508,c_2820])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.64  
% 3.40/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.64  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.40/1.64  
% 3.40/1.64  %Foreground sorts:
% 3.40/1.64  
% 3.40/1.64  
% 3.40/1.64  %Background operators:
% 3.40/1.64  
% 3.40/1.64  
% 3.40/1.64  %Foreground operators:
% 3.40/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.40/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.40/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.64  
% 3.40/1.66  tff(f_68, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.40/1.66  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.40/1.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.40/1.66  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.40/1.66  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.40/1.66  tff(f_61, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.40/1.66  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.40/1.66  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.40/1.66  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.40/1.66  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.40/1.66  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.40/1.66  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.40/1.66  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.40/1.66  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.40/1.66  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.66  tff(c_117, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 3.40/1.66  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.66  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.66  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.66  tff(c_22, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.40/1.66  tff(c_65, plain, (![A_33, B_34]: (r1_xboole_0(k4_xboole_0(A_33, B_34), B_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.66  tff(c_68, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_65])).
% 3.40/1.66  tff(c_177, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.66  tff(c_188, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_177])).
% 3.40/1.66  tff(c_505, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.66  tff(c_532, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_505])).
% 3.40/1.66  tff(c_536, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_532])).
% 3.40/1.66  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.66  tff(c_358, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.66  tff(c_379, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_358])).
% 3.40/1.66  tff(c_537, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_536, c_379])).
% 3.40/1.66  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.66  tff(c_159, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.66  tff(c_169, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_159])).
% 3.40/1.66  tff(c_376, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_169, c_358])).
% 3.40/1.66  tff(c_597, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_537, c_376])).
% 3.40/1.66  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.66  tff(c_607, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_597, c_20])).
% 3.40/1.66  tff(c_618, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14, c_607])).
% 3.40/1.66  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(k2_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.40/1.66  tff(c_1449, plain, (![C_108]: (r1_tarski('#skF_1', C_108) | ~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), C_108))), inference(superposition, [status(thm), theory('equality')], [c_618, c_12])).
% 3.40/1.66  tff(c_1489, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_1449])).
% 3.40/1.66  tff(c_1507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_1489])).
% 3.40/1.66  tff(c_1508, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 3.40/1.66  tff(c_28, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.66  tff(c_2278, plain, (![A_149, C_150, B_151]: (r1_xboole_0(A_149, C_150) | ~r1_xboole_0(B_151, C_150) | ~r1_tarski(A_149, B_151))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.40/1.66  tff(c_2782, plain, (![A_164, B_165, A_166]: (r1_xboole_0(A_164, B_165) | ~r1_tarski(A_164, k4_xboole_0(A_166, B_165)))), inference(resolution, [status(thm)], [c_28, c_2278])).
% 3.40/1.66  tff(c_2820, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_2782])).
% 3.40/1.66  tff(c_2838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1508, c_2820])).
% 3.40/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.66  
% 3.40/1.66  Inference rules
% 3.40/1.66  ----------------------
% 3.40/1.66  #Ref     : 0
% 3.40/1.66  #Sup     : 680
% 3.40/1.66  #Fact    : 0
% 3.40/1.66  #Define  : 0
% 3.40/1.66  #Split   : 1
% 3.40/1.66  #Chain   : 0
% 3.40/1.66  #Close   : 0
% 3.40/1.66  
% 3.40/1.66  Ordering : KBO
% 3.40/1.66  
% 3.40/1.66  Simplification rules
% 3.40/1.66  ----------------------
% 3.40/1.66  #Subsume      : 13
% 3.40/1.66  #Demod        : 414
% 3.40/1.66  #Tautology    : 506
% 3.40/1.66  #SimpNegUnit  : 2
% 3.40/1.66  #BackRed      : 4
% 3.40/1.66  
% 3.40/1.66  #Partial instantiations: 0
% 3.40/1.66  #Strategies tried      : 1
% 3.40/1.66  
% 3.40/1.66  Timing (in seconds)
% 3.77/1.66  ----------------------
% 3.77/1.66  Preprocessing        : 0.29
% 3.77/1.66  Parsing              : 0.17
% 3.77/1.66  CNF conversion       : 0.02
% 3.77/1.66  Main loop            : 0.57
% 3.77/1.66  Inferencing          : 0.20
% 3.77/1.66  Reduction            : 0.22
% 3.77/1.66  Demodulation         : 0.17
% 3.77/1.66  BG Simplification    : 0.02
% 3.77/1.66  Subsumption          : 0.08
% 3.77/1.66  Abstraction          : 0.02
% 3.77/1.66  MUC search           : 0.00
% 3.77/1.66  Cooper               : 0.00
% 3.77/1.66  Total                : 0.89
% 3.77/1.66  Index Insertion      : 0.00
% 3.77/1.66  Index Deletion       : 0.00
% 3.77/1.66  Index Matching       : 0.00
% 3.77/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------

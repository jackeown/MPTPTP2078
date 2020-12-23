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
% DateTime   : Thu Dec  3 09:45:30 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 109 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :   50 ( 117 expanded)
%              Number of equality atoms :   35 (  80 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_39,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_22,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_141,plain,(
    ! [A_9] : k3_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_127])).

tff(c_231,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_249,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_231])).

tff(c_270,plain,(
    ! [A_38] : k4_xboole_0(k1_xboole_0,A_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_249])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_275,plain,(
    ! [A_38] : k5_xboole_0(A_38,k1_xboole_0) = k2_xboole_0(A_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_18])).

tff(c_279,plain,(
    ! [A_38] : k2_xboole_0(A_38,k1_xboole_0) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_275])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_142,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_246,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_231])).

tff(c_260,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_246])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_143,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_127])).

tff(c_243,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_231])).

tff(c_259,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_243])).

tff(c_265,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_18])).

tff(c_268,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_265])).

tff(c_284,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_18])).

tff(c_287,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_284])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k4_xboole_0(A_16,k2_xboole_0(B_17,C_18)),k4_xboole_0(B_17,k2_xboole_0(A_16,C_18))) = k4_xboole_0(k5_xboole_0(A_16,B_17),C_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_432,plain,(
    ! [A_44] : k2_xboole_0(k4_xboole_0(A_44,'#skF_2'),k4_xboole_0('#skF_3',k2_xboole_0(A_44,'#skF_2'))) = k4_xboole_0(k5_xboole_0(A_44,'#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_20])).

tff(c_466,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) = k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_432])).

tff(c_481,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_260,c_268,c_466])).

tff(c_626,plain,(
    k2_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_3')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_18])).

tff(c_630,plain,(
    k2_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_626])).

tff(c_88,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [A_27,B_26] : r1_tarski(A_27,k2_xboole_0(B_26,A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_14])).

tff(c_1276,plain,(
    r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_103])).

tff(c_1286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.41  
% 2.67/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.42  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.67/1.42  
% 2.67/1.42  %Foreground sorts:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Background operators:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Foreground operators:
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.42  
% 2.67/1.43  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.67/1.43  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.67/1.43  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.67/1.43  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.67/1.43  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.67/1.43  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.67/1.43  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.67/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.67/1.43  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k5_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k4_xboole_0(B, k2_xboole_0(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_xboole_1)).
% 2.67/1.43  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.67/1.43  tff(c_22, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.43  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.67/1.43  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.43  tff(c_127, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.43  tff(c_141, plain, (![A_9]: (k3_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_127])).
% 2.67/1.43  tff(c_231, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.43  tff(c_249, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_141, c_231])).
% 2.67/1.43  tff(c_270, plain, (![A_38]: (k4_xboole_0(k1_xboole_0, A_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_249])).
% 2.67/1.43  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.43  tff(c_275, plain, (![A_38]: (k5_xboole_0(A_38, k1_xboole_0)=k2_xboole_0(A_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_270, c_18])).
% 2.67/1.43  tff(c_279, plain, (![A_38]: (k2_xboole_0(A_38, k1_xboole_0)=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_275])).
% 2.67/1.43  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.67/1.43  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.43  tff(c_142, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_24, c_127])).
% 2.67/1.43  tff(c_246, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_142, c_231])).
% 2.67/1.43  tff(c_260, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_246])).
% 2.67/1.43  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.43  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.43  tff(c_143, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_26, c_127])).
% 2.67/1.43  tff(c_243, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_143, c_231])).
% 2.67/1.43  tff(c_259, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_243])).
% 2.67/1.43  tff(c_265, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_259, c_18])).
% 2.67/1.43  tff(c_268, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_265])).
% 2.67/1.43  tff(c_284, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_260, c_18])).
% 2.67/1.43  tff(c_287, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_284])).
% 2.67/1.43  tff(c_20, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k4_xboole_0(A_16, k2_xboole_0(B_17, C_18)), k4_xboole_0(B_17, k2_xboole_0(A_16, C_18)))=k4_xboole_0(k5_xboole_0(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.43  tff(c_432, plain, (![A_44]: (k2_xboole_0(k4_xboole_0(A_44, '#skF_2'), k4_xboole_0('#skF_3', k2_xboole_0(A_44, '#skF_2')))=k4_xboole_0(k5_xboole_0(A_44, '#skF_3'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_20])).
% 2.67/1.43  tff(c_466, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_259, c_432])).
% 2.67/1.43  tff(c_481, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_279, c_260, c_268, c_466])).
% 2.67/1.43  tff(c_626, plain, (k2_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_3'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_481, c_18])).
% 2.67/1.43  tff(c_630, plain, (k2_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_626])).
% 2.67/1.43  tff(c_88, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.43  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.43  tff(c_103, plain, (![A_27, B_26]: (r1_tarski(A_27, k2_xboole_0(B_26, A_27)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_14])).
% 2.67/1.43  tff(c_1276, plain, (r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_630, c_103])).
% 2.67/1.43  tff(c_1286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_1276])).
% 2.67/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.43  
% 2.67/1.43  Inference rules
% 2.67/1.43  ----------------------
% 2.67/1.43  #Ref     : 0
% 2.67/1.43  #Sup     : 324
% 2.67/1.43  #Fact    : 0
% 2.67/1.43  #Define  : 0
% 2.67/1.43  #Split   : 0
% 2.67/1.43  #Chain   : 0
% 2.67/1.43  #Close   : 0
% 2.67/1.43  
% 2.67/1.43  Ordering : KBO
% 2.67/1.43  
% 2.67/1.43  Simplification rules
% 2.67/1.43  ----------------------
% 2.67/1.43  #Subsume      : 0
% 2.67/1.43  #Demod        : 232
% 2.67/1.43  #Tautology    : 214
% 2.67/1.43  #SimpNegUnit  : 1
% 2.67/1.43  #BackRed      : 0
% 2.67/1.43  
% 2.67/1.43  #Partial instantiations: 0
% 2.67/1.43  #Strategies tried      : 1
% 2.67/1.43  
% 2.67/1.43  Timing (in seconds)
% 2.67/1.43  ----------------------
% 2.67/1.43  Preprocessing        : 0.26
% 2.67/1.43  Parsing              : 0.14
% 2.67/1.43  CNF conversion       : 0.02
% 2.67/1.43  Main loop            : 0.39
% 2.67/1.43  Inferencing          : 0.14
% 2.67/1.43  Reduction            : 0.16
% 2.67/1.43  Demodulation         : 0.13
% 2.67/1.43  BG Simplification    : 0.02
% 2.67/1.43  Subsumption          : 0.05
% 2.67/1.43  Abstraction          : 0.02
% 2.67/1.43  MUC search           : 0.00
% 2.67/1.43  Cooper               : 0.00
% 2.67/1.43  Total                : 0.68
% 2.67/1.43  Index Insertion      : 0.00
% 2.67/1.43  Index Deletion       : 0.00
% 2.67/1.43  Index Matching       : 0.00
% 2.67/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

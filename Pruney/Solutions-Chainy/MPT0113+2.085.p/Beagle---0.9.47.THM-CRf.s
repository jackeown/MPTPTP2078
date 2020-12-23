%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:22 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  70 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_44,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_43,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_48,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_43])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_49,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_49])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_400,plain,(
    ! [A_49,B_50] : k3_xboole_0(k4_xboole_0(A_49,B_50),A_49) = k4_xboole_0(A_49,B_50) ),
    inference(resolution,[status(thm)],[c_14,c_49])).

tff(c_214,plain,(
    ! [A_39,B_40,C_41] : k3_xboole_0(k3_xboole_0(A_39,B_40),C_41) = k3_xboole_0(A_39,k3_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_239,plain,(
    ! [C_41] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_41)) = k3_xboole_0('#skF_1',C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_214])).

tff(c_407,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_239])).

tff(c_433,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_407])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_450,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_8])).

tff(c_454,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_450])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_454])).

tff(c_457,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_460,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_475,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_460])).

tff(c_653,plain,(
    ! [A_64,B_65,C_66] : k4_xboole_0(k3_xboole_0(A_64,B_65),C_66) = k3_xboole_0(A_64,k4_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_775,plain,(
    ! [A_70,B_71,C_72] : r1_xboole_0(k3_xboole_0(A_70,k4_xboole_0(B_71,C_72)),C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_18])).

tff(c_802,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_775])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:07:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.33  
% 2.48/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.33  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.48/1.33  
% 2.48/1.33  %Foreground sorts:
% 2.48/1.33  
% 2.48/1.33  
% 2.48/1.33  %Background operators:
% 2.48/1.33  
% 2.48/1.33  
% 2.48/1.33  %Foreground operators:
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.48/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.33  
% 2.48/1.34  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.48/1.34  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.48/1.34  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.48/1.34  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.48/1.34  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.48/1.34  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.48/1.34  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.48/1.34  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.48/1.34  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.48/1.34  tff(c_44, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | k4_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.34  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.48/1.34  tff(c_43, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 2.48/1.34  tff(c_48, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_43])).
% 2.48/1.34  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.34  tff(c_24, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.48/1.34  tff(c_49, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.48/1.34  tff(c_60, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_49])).
% 2.48/1.34  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.34  tff(c_400, plain, (![A_49, B_50]: (k3_xboole_0(k4_xboole_0(A_49, B_50), A_49)=k4_xboole_0(A_49, B_50))), inference(resolution, [status(thm)], [c_14, c_49])).
% 2.48/1.34  tff(c_214, plain, (![A_39, B_40, C_41]: (k3_xboole_0(k3_xboole_0(A_39, B_40), C_41)=k3_xboole_0(A_39, k3_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.34  tff(c_239, plain, (![C_41]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_41))=k3_xboole_0('#skF_1', C_41))), inference(superposition, [status(thm), theory('equality')], [c_60, c_214])).
% 2.48/1.34  tff(c_407, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_400, c_239])).
% 2.48/1.34  tff(c_433, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_407])).
% 2.48/1.34  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.48/1.34  tff(c_450, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_433, c_8])).
% 2.48/1.34  tff(c_454, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_450])).
% 2.48/1.34  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_454])).
% 2.48/1.34  tff(c_457, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.48/1.34  tff(c_460, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.48/1.34  tff(c_475, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_460])).
% 2.48/1.34  tff(c_653, plain, (![A_64, B_65, C_66]: (k4_xboole_0(k3_xboole_0(A_64, B_65), C_66)=k3_xboole_0(A_64, k4_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.48/1.34  tff(c_18, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.48/1.34  tff(c_775, plain, (![A_70, B_71, C_72]: (r1_xboole_0(k3_xboole_0(A_70, k4_xboole_0(B_71, C_72)), C_72))), inference(superposition, [status(thm), theory('equality')], [c_653, c_18])).
% 2.48/1.34  tff(c_802, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_475, c_775])).
% 2.48/1.34  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_457, c_802])).
% 2.48/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.34  
% 2.48/1.34  Inference rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Ref     : 0
% 2.48/1.34  #Sup     : 204
% 2.48/1.34  #Fact    : 0
% 2.48/1.34  #Define  : 0
% 2.48/1.34  #Split   : 1
% 2.48/1.34  #Chain   : 0
% 2.48/1.34  #Close   : 0
% 2.48/1.34  
% 2.48/1.34  Ordering : KBO
% 2.48/1.34  
% 2.48/1.34  Simplification rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Subsume      : 0
% 2.48/1.34  #Demod        : 121
% 2.48/1.34  #Tautology    : 145
% 2.48/1.34  #SimpNegUnit  : 2
% 2.48/1.34  #BackRed      : 0
% 2.48/1.34  
% 2.48/1.34  #Partial instantiations: 0
% 2.48/1.34  #Strategies tried      : 1
% 2.48/1.34  
% 2.48/1.34  Timing (in seconds)
% 2.48/1.34  ----------------------
% 2.48/1.34  Preprocessing        : 0.28
% 2.48/1.34  Parsing              : 0.15
% 2.48/1.34  CNF conversion       : 0.02
% 2.48/1.34  Main loop            : 0.31
% 2.48/1.34  Inferencing          : 0.12
% 2.48/1.34  Reduction            : 0.11
% 2.48/1.34  Demodulation         : 0.08
% 2.48/1.34  BG Simplification    : 0.01
% 2.48/1.34  Subsumption          : 0.04
% 2.48/1.34  Abstraction          : 0.02
% 2.48/1.34  MUC search           : 0.00
% 2.48/1.34  Cooper               : 0.00
% 2.48/1.34  Total                : 0.61
% 2.48/1.34  Index Insertion      : 0.00
% 2.48/1.34  Index Deletion       : 0.00
% 2.48/1.34  Index Matching       : 0.00
% 2.48/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

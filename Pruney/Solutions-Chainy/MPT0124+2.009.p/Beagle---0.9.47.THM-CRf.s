%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:36 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 (  68 expanded)
%              Number of equality atoms :   24 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(C,B)
       => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_18,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_67,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_67])).

tff(c_12,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_12])).

tff(c_631,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(k4_xboole_0(A_71,B_72),C_73)
      | ~ r1_tarski(A_71,k2_xboole_0(B_72,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_651,plain,(
    ! [C_73] :
      ( r1_tarski(k4_xboole_0('#skF_3','#skF_2'),C_73)
      | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',C_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_631])).

tff(c_660,plain,(
    ! [C_73] : r1_tarski(k4_xboole_0('#skF_3','#skF_2'),C_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_651])).

tff(c_662,plain,(
    ! [C_74] : r1_tarski(k4_xboole_0('#skF_3','#skF_2'),C_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_651])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_680,plain,(
    ! [C_75] : k2_xboole_0(k4_xboole_0('#skF_3','#skF_2'),C_75) = C_75 ),
    inference(resolution,[status(thm)],[c_662,c_4])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_691,plain,(
    ! [B_19] :
      ( k4_xboole_0(B_19,k4_xboole_0('#skF_3','#skF_2')) = B_19
      | ~ r1_tarski(k4_xboole_0('#skF_3','#skF_2'),B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_16])).

tff(c_732,plain,(
    ! [B_76] : k4_xboole_0(B_76,k4_xboole_0('#skF_3','#skF_2')) = B_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_691])).

tff(c_783,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_732])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k4_xboole_0(A_22,B_23),k3_xboole_0(A_22,C_24)) = k4_xboole_0(A_22,k4_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26])).

tff(c_30,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_29])).

tff(c_31,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.39  
% 2.65/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.40  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.65/1.40  
% 2.65/1.40  %Foreground sorts:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Background operators:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Foreground operators:
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.40  
% 2.65/1.41  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.65/1.41  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.65/1.41  tff(f_70, negated_conjecture, ~(![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 2.65/1.41  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.65/1.41  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.65/1.41  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.65/1.41  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.65/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.65/1.41  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.65/1.41  tff(c_18, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.41  tff(c_22, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.41  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.65/1.41  tff(c_67, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.41  tff(c_79, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_28, c_67])).
% 2.65/1.41  tff(c_12, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.41  tff(c_95, plain, (k4_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_79, c_12])).
% 2.65/1.41  tff(c_631, plain, (![A_71, B_72, C_73]: (r1_tarski(k4_xboole_0(A_71, B_72), C_73) | ~r1_tarski(A_71, k2_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.41  tff(c_651, plain, (![C_73]: (r1_tarski(k4_xboole_0('#skF_3', '#skF_2'), C_73) | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', C_73)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_631])).
% 2.65/1.41  tff(c_660, plain, (![C_73]: (r1_tarski(k4_xboole_0('#skF_3', '#skF_2'), C_73))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_651])).
% 2.65/1.41  tff(c_662, plain, (![C_74]: (r1_tarski(k4_xboole_0('#skF_3', '#skF_2'), C_74))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_651])).
% 2.65/1.41  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.41  tff(c_680, plain, (![C_75]: (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), C_75)=C_75)), inference(resolution, [status(thm)], [c_662, c_4])).
% 2.65/1.41  tff(c_16, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.41  tff(c_691, plain, (![B_19]: (k4_xboole_0(B_19, k4_xboole_0('#skF_3', '#skF_2'))=B_19 | ~r1_tarski(k4_xboole_0('#skF_3', '#skF_2'), B_19))), inference(superposition, [status(thm), theory('equality')], [c_680, c_16])).
% 2.65/1.41  tff(c_732, plain, (![B_76]: (k4_xboole_0(B_76, k4_xboole_0('#skF_3', '#skF_2'))=B_76)), inference(demodulation, [status(thm), theory('equality')], [c_660, c_691])).
% 2.65/1.41  tff(c_783, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_18, c_732])).
% 2.65/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.41  tff(c_20, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k4_xboole_0(A_22, B_23), k3_xboole_0(A_22, C_24))=k4_xboole_0(A_22, k4_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.41  tff(c_26, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.65/1.41  tff(c_29, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26])).
% 2.65/1.41  tff(c_30, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_29])).
% 2.65/1.41  tff(c_31, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 2.65/1.41  tff(c_858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_783, c_31])).
% 2.65/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.41  
% 2.65/1.41  Inference rules
% 2.65/1.41  ----------------------
% 2.65/1.41  #Ref     : 0
% 2.65/1.41  #Sup     : 212
% 2.65/1.41  #Fact    : 0
% 2.65/1.41  #Define  : 0
% 2.65/1.41  #Split   : 0
% 2.65/1.41  #Chain   : 0
% 2.65/1.41  #Close   : 0
% 2.65/1.41  
% 2.65/1.41  Ordering : KBO
% 2.65/1.41  
% 2.65/1.41  Simplification rules
% 2.65/1.41  ----------------------
% 2.65/1.41  #Subsume      : 5
% 2.65/1.41  #Demod        : 72
% 2.65/1.41  #Tautology    : 105
% 2.65/1.41  #SimpNegUnit  : 0
% 2.65/1.41  #BackRed      : 2
% 2.65/1.41  
% 2.65/1.41  #Partial instantiations: 0
% 2.65/1.41  #Strategies tried      : 1
% 2.65/1.41  
% 2.65/1.41  Timing (in seconds)
% 2.65/1.41  ----------------------
% 2.65/1.41  Preprocessing        : 0.29
% 2.65/1.41  Parsing              : 0.16
% 2.65/1.41  CNF conversion       : 0.02
% 2.65/1.41  Main loop            : 0.35
% 2.65/1.41  Inferencing          : 0.12
% 2.65/1.41  Reduction            : 0.13
% 2.65/1.41  Demodulation         : 0.10
% 2.65/1.41  BG Simplification    : 0.02
% 2.65/1.41  Subsumption          : 0.06
% 2.65/1.41  Abstraction          : 0.02
% 2.65/1.41  MUC search           : 0.00
% 2.65/1.41  Cooper               : 0.00
% 2.65/1.41  Total                : 0.67
% 2.65/1.41  Index Insertion      : 0.00
% 2.65/1.41  Index Deletion       : 0.00
% 2.65/1.41  Index Matching       : 0.00
% 2.65/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

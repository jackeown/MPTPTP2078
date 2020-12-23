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
% DateTime   : Thu Dec  3 09:42:37 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  47 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_196,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_217,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_196])).

tff(c_12,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_221,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_12])).

tff(c_37,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,k3_xboole_0(A_27,B_26)) = B_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_14])).

tff(c_232,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_55])).

tff(c_260,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,k2_xboole_0(C_39,B_40))
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_266,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_2')
      | ~ r1_tarski(A_38,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_260])).

tff(c_58,plain,(
    ! [B_26,A_27] : r1_tarski(k3_xboole_0(B_26,A_27),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_8])).

tff(c_372,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(A_46,k3_xboole_0(B_47,C_48))
      | ~ r1_tarski(A_46,C_48)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_21,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_378,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_21])).

tff(c_397,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_378])).

tff(c_400,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_266,c_397])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.26  
% 2.01/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.26  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.01/1.26  
% 2.01/1.26  %Foreground sorts:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Background operators:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Foreground operators:
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.26  
% 2.01/1.27  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.01/1.27  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_xboole_1)).
% 2.01/1.27  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.01/1.27  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.01/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.01/1.27  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.01/1.27  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.01/1.27  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.01/1.27  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.01/1.27  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.01/1.27  tff(c_196, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.27  tff(c_217, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_196])).
% 2.01/1.27  tff(c_12, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.01/1.27  tff(c_221, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_217, c_12])).
% 2.01/1.27  tff(c_37, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.27  tff(c_14, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k3_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.01/1.27  tff(c_55, plain, (![B_26, A_27]: (k2_xboole_0(B_26, k3_xboole_0(A_27, B_26))=B_26)), inference(superposition, [status(thm), theory('equality')], [c_37, c_14])).
% 2.01/1.27  tff(c_232, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_221, c_55])).
% 2.01/1.27  tff(c_260, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, k2_xboole_0(C_39, B_40)) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.27  tff(c_266, plain, (![A_38]: (r1_tarski(A_38, '#skF_2') | ~r1_tarski(A_38, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_232, c_260])).
% 2.01/1.27  tff(c_58, plain, (![B_26, A_27]: (r1_tarski(k3_xboole_0(B_26, A_27), A_27))), inference(superposition, [status(thm), theory('equality')], [c_37, c_8])).
% 2.01/1.27  tff(c_372, plain, (![A_46, B_47, C_48]: (r1_tarski(A_46, k3_xboole_0(B_47, C_48)) | ~r1_tarski(A_46, C_48) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.27  tff(c_18, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.01/1.27  tff(c_21, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 2.01/1.27  tff(c_378, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_372, c_21])).
% 2.01/1.27  tff(c_397, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_378])).
% 2.01/1.27  tff(c_400, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_266, c_397])).
% 2.01/1.27  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_400])).
% 2.01/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.27  
% 2.01/1.27  Inference rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Ref     : 0
% 2.01/1.27  #Sup     : 98
% 2.01/1.27  #Fact    : 0
% 2.01/1.27  #Define  : 0
% 2.01/1.27  #Split   : 0
% 2.01/1.27  #Chain   : 0
% 2.01/1.27  #Close   : 0
% 2.01/1.27  
% 2.01/1.27  Ordering : KBO
% 2.01/1.27  
% 2.01/1.27  Simplification rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Subsume      : 2
% 2.01/1.27  #Demod        : 37
% 2.01/1.27  #Tautology    : 73
% 2.01/1.27  #SimpNegUnit  : 0
% 2.01/1.27  #BackRed      : 0
% 2.01/1.27  
% 2.01/1.27  #Partial instantiations: 0
% 2.01/1.27  #Strategies tried      : 1
% 2.01/1.27  
% 2.01/1.27  Timing (in seconds)
% 2.01/1.27  ----------------------
% 2.01/1.27  Preprocessing        : 0.26
% 2.01/1.27  Parsing              : 0.15
% 2.01/1.27  CNF conversion       : 0.01
% 2.01/1.27  Main loop            : 0.25
% 2.01/1.27  Inferencing          : 0.09
% 2.01/1.27  Reduction            : 0.09
% 2.01/1.27  Demodulation         : 0.07
% 2.01/1.27  BG Simplification    : 0.01
% 2.01/1.27  Subsumption          : 0.04
% 2.01/1.27  Abstraction          : 0.01
% 2.01/1.27  MUC search           : 0.00
% 2.01/1.27  Cooper               : 0.00
% 2.01/1.28  Total                : 0.54
% 2.01/1.28  Index Insertion      : 0.00
% 2.01/1.28  Index Deletion       : 0.00
% 2.01/1.28  Index Matching       : 0.00
% 2.01/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:38 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  74 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_197,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_222,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_197])).

tff(c_12,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_237,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_30,B_31] : k2_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_92])).

tff(c_279,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_113])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_355,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,'#skF_2')
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_4])).

tff(c_26,plain,(
    ! [B_23,A_24] : k3_xboole_0(B_23,A_24) = k3_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_41,plain,(
    ! [B_23,A_24] : r1_tarski(k3_xboole_0(B_23,A_24),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_221,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_197])).

tff(c_226,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_12])).

tff(c_248,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_113])).

tff(c_329,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,k2_xboole_0(C_39,B_40))
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_477,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,'#skF_4')
      | ~ r1_tarski(A_46,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_329])).

tff(c_490,plain,(
    ! [B_23] : r1_tarski(k3_xboole_0(B_23,'#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_41,c_477])).

tff(c_494,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(A_47,k3_xboole_0(B_48,C_49))
      | ~ r1_tarski(A_47,C_49)
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_23,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_523,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_494,c_23])).

tff(c_575,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_523])).

tff(c_578,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_355,c_575])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:35:57 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.29  
% 2.08/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.30  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.08/1.30  
% 2.08/1.30  %Foreground sorts:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Background operators:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Foreground operators:
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.30  
% 2.08/1.31  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.08/1.31  tff(f_56, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 2.08/1.31  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.08/1.31  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.08/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.08/1.31  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.08/1.31  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.08/1.31  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.08/1.31  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.31  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.31  tff(c_197, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.31  tff(c_222, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_197])).
% 2.08/1.31  tff(c_12, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.31  tff(c_237, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_222, c_12])).
% 2.08/1.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.31  tff(c_92, plain, (![A_30, B_31]: (k2_xboole_0(A_30, k3_xboole_0(A_30, B_31))=A_30)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.31  tff(c_113, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k3_xboole_0(A_1, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_92])).
% 2.08/1.31  tff(c_279, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_237, c_113])).
% 2.08/1.31  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.31  tff(c_355, plain, (![A_3]: (r1_tarski(A_3, '#skF_2') | ~r1_tarski(A_3, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_279, c_4])).
% 2.08/1.31  tff(c_26, plain, (![B_23, A_24]: (k3_xboole_0(B_23, A_24)=k3_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.31  tff(c_41, plain, (![B_23, A_24]: (r1_tarski(k3_xboole_0(B_23, A_24), A_24))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8])).
% 2.08/1.31  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.31  tff(c_221, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_197])).
% 2.08/1.31  tff(c_226, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_221, c_12])).
% 2.08/1.31  tff(c_248, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_226, c_113])).
% 2.08/1.31  tff(c_329, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, k2_xboole_0(C_39, B_40)) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.31  tff(c_477, plain, (![A_46]: (r1_tarski(A_46, '#skF_4') | ~r1_tarski(A_46, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_329])).
% 2.08/1.31  tff(c_490, plain, (![B_23]: (r1_tarski(k3_xboole_0(B_23, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_41, c_477])).
% 2.08/1.31  tff(c_494, plain, (![A_47, B_48, C_49]: (r1_tarski(A_47, k3_xboole_0(B_48, C_49)) | ~r1_tarski(A_47, C_49) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.31  tff(c_18, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.31  tff(c_23, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 2.08/1.31  tff(c_523, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_494, c_23])).
% 2.08/1.31  tff(c_575, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_523])).
% 2.08/1.31  tff(c_578, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_355, c_575])).
% 2.08/1.31  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_578])).
% 2.08/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.31  
% 2.08/1.31  Inference rules
% 2.08/1.31  ----------------------
% 2.08/1.31  #Ref     : 0
% 2.08/1.31  #Sup     : 145
% 2.08/1.31  #Fact    : 0
% 2.08/1.31  #Define  : 0
% 2.08/1.31  #Split   : 0
% 2.08/1.31  #Chain   : 0
% 2.08/1.31  #Close   : 0
% 2.08/1.31  
% 2.08/1.31  Ordering : KBO
% 2.08/1.31  
% 2.08/1.31  Simplification rules
% 2.08/1.31  ----------------------
% 2.08/1.31  #Subsume      : 2
% 2.08/1.31  #Demod        : 63
% 2.08/1.31  #Tautology    : 110
% 2.08/1.31  #SimpNegUnit  : 0
% 2.08/1.31  #BackRed      : 0
% 2.08/1.31  
% 2.08/1.31  #Partial instantiations: 0
% 2.08/1.31  #Strategies tried      : 1
% 2.08/1.31  
% 2.08/1.31  Timing (in seconds)
% 2.08/1.31  ----------------------
% 2.08/1.31  Preprocessing        : 0.27
% 2.08/1.31  Parsing              : 0.15
% 2.08/1.31  CNF conversion       : 0.02
% 2.08/1.31  Main loop            : 0.27
% 2.08/1.31  Inferencing          : 0.10
% 2.08/1.31  Reduction            : 0.10
% 2.08/1.31  Demodulation         : 0.08
% 2.08/1.31  BG Simplification    : 0.01
% 2.08/1.31  Subsumption          : 0.04
% 2.08/1.31  Abstraction          : 0.01
% 2.08/1.31  MUC search           : 0.00
% 2.08/1.31  Cooper               : 0.00
% 2.08/1.31  Total                : 0.58
% 2.08/1.31  Index Insertion      : 0.00
% 2.08/1.31  Index Deletion       : 0.00
% 2.08/1.31  Index Matching       : 0.00
% 2.08/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

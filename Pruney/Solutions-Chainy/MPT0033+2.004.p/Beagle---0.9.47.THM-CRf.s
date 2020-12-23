%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:37 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  43 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_31,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_85])).

tff(c_12,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_196,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(A_32,B_33)
      | ~ r1_tarski(A_32,k3_xboole_0(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_305,plain,(
    ! [B_40,C_41,B_42] : r1_tarski(k3_xboole_0(k3_xboole_0(B_40,C_41),B_42),B_40) ),
    inference(resolution,[status(thm)],[c_6,c_196])).

tff(c_394,plain,(
    ! [B_46,A_47,B_48] : r1_tarski(k3_xboole_0(k3_xboole_0(B_46,A_47),B_48),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_305])).

tff(c_411,plain,(
    ! [B_48] : r1_tarski(k3_xboole_0('#skF_1',B_48),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_394])).

tff(c_32,plain,(
    ! [B_20,A_21] : k3_xboole_0(B_20,A_21) = k3_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_47,plain,(
    ! [B_20,A_21] : r1_tarski(k3_xboole_0(B_20,A_21),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_275,plain,(
    ! [A_37,B_38,C_39] :
      ( r1_tarski(A_37,k3_xboole_0(B_38,C_39))
      | ~ r1_tarski(A_37,C_39)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_17,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_284,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_275,c_17])).

tff(c_304,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_284])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:59:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.11/1.24  
% 2.11/1.24  %Foreground sorts:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Background operators:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Foreground operators:
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.24  
% 2.11/1.25  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 2.11/1.25  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.11/1.25  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.11/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.11/1.25  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.11/1.25  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.11/1.25  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.11/1.25  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.25  tff(c_85, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.25  tff(c_105, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_85])).
% 2.11/1.25  tff(c_12, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.25  tff(c_112, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_105, c_12])).
% 2.11/1.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.25  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.25  tff(c_196, plain, (![A_32, B_33, C_34]: (r1_tarski(A_32, B_33) | ~r1_tarski(A_32, k3_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.25  tff(c_305, plain, (![B_40, C_41, B_42]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_40, C_41), B_42), B_40))), inference(resolution, [status(thm)], [c_6, c_196])).
% 2.11/1.25  tff(c_394, plain, (![B_46, A_47, B_48]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_46, A_47), B_48), A_47))), inference(superposition, [status(thm), theory('equality')], [c_2, c_305])).
% 2.11/1.25  tff(c_411, plain, (![B_48]: (r1_tarski(k3_xboole_0('#skF_1', B_48), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_394])).
% 2.11/1.25  tff(c_32, plain, (![B_20, A_21]: (k3_xboole_0(B_20, A_21)=k3_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.25  tff(c_47, plain, (![B_20, A_21]: (r1_tarski(k3_xboole_0(B_20, A_21), A_21))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6])).
% 2.11/1.25  tff(c_275, plain, (![A_37, B_38, C_39]: (r1_tarski(A_37, k3_xboole_0(B_38, C_39)) | ~r1_tarski(A_37, C_39) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.25  tff(c_14, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.25  tff(c_17, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.11/1.25  tff(c_284, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_275, c_17])).
% 2.11/1.25  tff(c_304, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_284])).
% 2.11/1.25  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_411, c_304])).
% 2.11/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  Inference rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Ref     : 0
% 2.11/1.25  #Sup     : 105
% 2.11/1.25  #Fact    : 0
% 2.11/1.25  #Define  : 0
% 2.11/1.25  #Split   : 0
% 2.11/1.25  #Chain   : 0
% 2.11/1.25  #Close   : 0
% 2.11/1.25  
% 2.11/1.25  Ordering : KBO
% 2.11/1.25  
% 2.11/1.25  Simplification rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Subsume      : 2
% 2.11/1.25  #Demod        : 40
% 2.11/1.25  #Tautology    : 68
% 2.11/1.25  #SimpNegUnit  : 0
% 2.11/1.25  #BackRed      : 1
% 2.11/1.25  
% 2.11/1.25  #Partial instantiations: 0
% 2.11/1.25  #Strategies tried      : 1
% 2.11/1.25  
% 2.11/1.25  Timing (in seconds)
% 2.11/1.25  ----------------------
% 2.11/1.25  Preprocessing        : 0.26
% 2.11/1.25  Parsing              : 0.14
% 2.11/1.25  CNF conversion       : 0.02
% 2.11/1.25  Main loop            : 0.23
% 2.11/1.25  Inferencing          : 0.08
% 2.11/1.25  Reduction            : 0.09
% 2.11/1.25  Demodulation         : 0.07
% 2.11/1.25  BG Simplification    : 0.01
% 2.11/1.25  Subsumption          : 0.04
% 2.11/1.25  Abstraction          : 0.01
% 2.11/1.25  MUC search           : 0.00
% 2.11/1.25  Cooper               : 0.00
% 2.11/1.25  Total                : 0.51
% 2.11/1.25  Index Insertion      : 0.00
% 2.11/1.25  Index Deletion       : 0.00
% 2.11/1.25  Index Matching       : 0.00
% 2.11/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

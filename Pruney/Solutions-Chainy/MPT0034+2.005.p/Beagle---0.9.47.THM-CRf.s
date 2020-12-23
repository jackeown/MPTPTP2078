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
% DateTime   : Thu Dec  3 09:42:38 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  67 expanded)
%              Number of equality atoms :   12 (  21 expanded)
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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

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

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_87,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_87])).

tff(c_12,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_129,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_170,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(A_28,B_29)
      | ~ r1_tarski(A_28,k3_xboole_0(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_552,plain,(
    ! [B_45,C_46,B_47] : r1_tarski(k3_xboole_0(k3_xboole_0(B_45,C_46),B_47),B_45) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_708,plain,(
    ! [B_53,A_54,B_55] : r1_tarski(k3_xboole_0(k3_xboole_0(B_53,A_54),B_55),A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_552])).

tff(c_732,plain,(
    ! [B_55] : r1_tarski(k3_xboole_0('#skF_1',B_55),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_708])).

tff(c_34,plain,(
    ! [B_20,A_21] : k3_xboole_0(B_20,A_21) = k3_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [B_20,A_21] : r1_tarski(k3_xboole_0(B_20,A_21),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_110,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16,c_87])).

tff(c_118,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_143,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_2])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_tarski(A_7,k3_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_387,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_4')
      | ~ r1_tarski(A_40,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_8])).

tff(c_400,plain,(
    ! [B_20] : r1_tarski(k3_xboole_0(B_20,'#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_387])).

tff(c_352,plain,(
    ! [A_37,B_38,C_39] :
      ( r1_tarski(A_37,k3_xboole_0(B_38,C_39))
      | ~ r1_tarski(A_37,C_39)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_385,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_352,c_19])).

tff(c_426,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_385])).

tff(c_769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n008.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:20:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.29  
% 2.15/1.29  %Foreground sorts:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Background operators:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Foreground operators:
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.29  
% 2.46/1.30  tff(f_52, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 2.46/1.30  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.46/1.30  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.46/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.46/1.30  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.46/1.30  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.46/1.30  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.46/1.30  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.30  tff(c_87, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.30  tff(c_111, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_18, c_87])).
% 2.46/1.30  tff(c_12, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.46/1.30  tff(c_129, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_111, c_12])).
% 2.46/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.30  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.30  tff(c_170, plain, (![A_28, B_29, C_30]: (r1_tarski(A_28, B_29) | ~r1_tarski(A_28, k3_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.30  tff(c_552, plain, (![B_45, C_46, B_47]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_45, C_46), B_47), B_45))), inference(resolution, [status(thm)], [c_6, c_170])).
% 2.46/1.30  tff(c_708, plain, (![B_53, A_54, B_55]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_53, A_54), B_55), A_54))), inference(superposition, [status(thm), theory('equality')], [c_2, c_552])).
% 2.46/1.30  tff(c_732, plain, (![B_55]: (r1_tarski(k3_xboole_0('#skF_1', B_55), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_708])).
% 2.46/1.30  tff(c_34, plain, (![B_20, A_21]: (k3_xboole_0(B_20, A_21)=k3_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.30  tff(c_49, plain, (![B_20, A_21]: (r1_tarski(k3_xboole_0(B_20, A_21), A_21))), inference(superposition, [status(thm), theory('equality')], [c_34, c_6])).
% 2.46/1.30  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.30  tff(c_110, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_16, c_87])).
% 2.46/1.30  tff(c_118, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_110, c_12])).
% 2.46/1.30  tff(c_143, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_118, c_2])).
% 2.46/1.30  tff(c_8, plain, (![A_7, B_8, C_9]: (r1_tarski(A_7, B_8) | ~r1_tarski(A_7, k3_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.30  tff(c_387, plain, (![A_40]: (r1_tarski(A_40, '#skF_4') | ~r1_tarski(A_40, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_8])).
% 2.46/1.30  tff(c_400, plain, (![B_20]: (r1_tarski(k3_xboole_0(B_20, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_49, c_387])).
% 2.46/1.30  tff(c_352, plain, (![A_37, B_38, C_39]: (r1_tarski(A_37, k3_xboole_0(B_38, C_39)) | ~r1_tarski(A_37, C_39) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.30  tff(c_14, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.30  tff(c_19, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.46/1.30  tff(c_385, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_352, c_19])).
% 2.46/1.30  tff(c_426, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_385])).
% 2.46/1.30  tff(c_769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_732, c_426])).
% 2.46/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.30  
% 2.46/1.30  Inference rules
% 2.46/1.30  ----------------------
% 2.46/1.30  #Ref     : 0
% 2.46/1.30  #Sup     : 185
% 2.46/1.30  #Fact    : 0
% 2.46/1.30  #Define  : 0
% 2.46/1.30  #Split   : 0
% 2.46/1.31  #Chain   : 0
% 2.46/1.31  #Close   : 0
% 2.46/1.31  
% 2.46/1.31  Ordering : KBO
% 2.46/1.31  
% 2.46/1.31  Simplification rules
% 2.46/1.31  ----------------------
% 2.46/1.31  #Subsume      : 2
% 2.46/1.31  #Demod        : 83
% 2.46/1.31  #Tautology    : 130
% 2.46/1.31  #SimpNegUnit  : 0
% 2.46/1.31  #BackRed      : 1
% 2.46/1.31  
% 2.46/1.31  #Partial instantiations: 0
% 2.46/1.31  #Strategies tried      : 1
% 2.46/1.31  
% 2.46/1.31  Timing (in seconds)
% 2.46/1.31  ----------------------
% 2.46/1.31  Preprocessing        : 0.27
% 2.46/1.31  Parsing              : 0.15
% 2.46/1.31  CNF conversion       : 0.02
% 2.46/1.31  Main loop            : 0.31
% 2.46/1.31  Inferencing          : 0.11
% 2.46/1.31  Reduction            : 0.12
% 2.46/1.31  Demodulation         : 0.10
% 2.46/1.31  BG Simplification    : 0.01
% 2.46/1.31  Subsumption          : 0.05
% 2.46/1.31  Abstraction          : 0.01
% 2.46/1.31  MUC search           : 0.00
% 2.46/1.31  Cooper               : 0.00
% 2.46/1.31  Total                : 0.61
% 2.46/1.31  Index Insertion      : 0.00
% 2.46/1.31  Index Deletion       : 0.00
% 2.46/1.31  Index Matching       : 0.00
% 2.46/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

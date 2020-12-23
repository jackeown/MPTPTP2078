%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:32 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  81 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B)
          & ! [D] :
              ( ( r1_tarski(A,D)
                & r1_tarski(C,D) )
             => r1_tarski(B,D) ) )
       => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_10,plain,(
    k2_xboole_0('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_57,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_57])).

tff(c_170,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(k2_xboole_0(A_23,C_24),k2_xboole_0(B_25,C_24))
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_959,plain,(
    ! [A_51,B_52,A_53] :
      ( r1_tarski(k2_xboole_0(A_51,B_52),k2_xboole_0(B_52,A_53))
      | ~ r1_tarski(A_51,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_170])).

tff(c_1037,plain,(
    ! [A_55] :
      ( r1_tarski(k2_xboole_0(A_55,'#skF_3'),'#skF_2')
      | ~ r1_tarski(A_55,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_959])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1040,plain,(
    ! [A_55] :
      ( k2_xboole_0(k2_xboole_0(A_55,'#skF_3'),'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_55,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1037,c_4])).

tff(c_2420,plain,(
    ! [A_74] :
      ( k2_xboole_0('#skF_2',k2_xboole_0(A_74,'#skF_3')) = '#skF_2'
      | ~ r1_tarski(A_74,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1040])).

tff(c_18,plain,(
    ! [B_14,A_15] : k2_xboole_0(B_14,A_15) = k2_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [B_14,A_15] : r1_tarski(B_14,k2_xboole_0(A_15,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_105,plain,(
    ! [D_20] :
      ( r1_tarski('#skF_2',D_20)
      | ~ r1_tarski('#skF_3',D_20)
      | ~ r1_tarski('#skF_1',D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_318,plain,(
    ! [D_30] :
      ( k2_xboole_0('#skF_2',D_30) = D_30
      | ~ r1_tarski('#skF_3',D_30)
      | ~ r1_tarski('#skF_1',D_30) ) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_884,plain,(
    ! [B_49] :
      ( k2_xboole_0('#skF_2',k2_xboole_0('#skF_3',B_49)) = k2_xboole_0('#skF_3',B_49)
      | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',B_49)) ) ),
    inference(resolution,[status(thm)],[c_6,c_318])).

tff(c_904,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_884])).

tff(c_921,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_904])).

tff(c_2447,plain,
    ( k2_xboole_0('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2420,c_921])).

tff(c_2550,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2447])).

tff(c_2552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_2550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.64  
% 3.87/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.64  %$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.87/1.64  
% 3.87/1.64  %Foreground sorts:
% 3.87/1.64  
% 3.87/1.64  
% 3.87/1.64  %Background operators:
% 3.87/1.64  
% 3.87/1.64  
% 3.87/1.64  %Foreground operators:
% 3.87/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.87/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.87/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.87/1.64  
% 3.87/1.65  tff(f_51, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 3.87/1.65  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.87/1.65  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.87/1.65  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 3.87/1.65  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.87/1.65  tff(c_10, plain, (k2_xboole_0('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.65  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.65  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.65  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.65  tff(c_57, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.65  tff(c_68, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_57])).
% 3.87/1.65  tff(c_170, plain, (![A_23, C_24, B_25]: (r1_tarski(k2_xboole_0(A_23, C_24), k2_xboole_0(B_25, C_24)) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.65  tff(c_959, plain, (![A_51, B_52, A_53]: (r1_tarski(k2_xboole_0(A_51, B_52), k2_xboole_0(B_52, A_53)) | ~r1_tarski(A_51, A_53))), inference(superposition, [status(thm), theory('equality')], [c_2, c_170])).
% 3.87/1.65  tff(c_1037, plain, (![A_55]: (r1_tarski(k2_xboole_0(A_55, '#skF_3'), '#skF_2') | ~r1_tarski(A_55, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_959])).
% 3.87/1.65  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.65  tff(c_1040, plain, (![A_55]: (k2_xboole_0(k2_xboole_0(A_55, '#skF_3'), '#skF_2')='#skF_2' | ~r1_tarski(A_55, '#skF_2'))), inference(resolution, [status(thm)], [c_1037, c_4])).
% 3.87/1.65  tff(c_2420, plain, (![A_74]: (k2_xboole_0('#skF_2', k2_xboole_0(A_74, '#skF_3'))='#skF_2' | ~r1_tarski(A_74, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1040])).
% 3.87/1.65  tff(c_18, plain, (![B_14, A_15]: (k2_xboole_0(B_14, A_15)=k2_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.65  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.65  tff(c_36, plain, (![B_14, A_15]: (r1_tarski(B_14, k2_xboole_0(A_15, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6])).
% 3.87/1.65  tff(c_105, plain, (![D_20]: (r1_tarski('#skF_2', D_20) | ~r1_tarski('#skF_3', D_20) | ~r1_tarski('#skF_1', D_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.65  tff(c_318, plain, (![D_30]: (k2_xboole_0('#skF_2', D_30)=D_30 | ~r1_tarski('#skF_3', D_30) | ~r1_tarski('#skF_1', D_30))), inference(resolution, [status(thm)], [c_105, c_4])).
% 3.87/1.65  tff(c_884, plain, (![B_49]: (k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', B_49))=k2_xboole_0('#skF_3', B_49) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', B_49)))), inference(resolution, [status(thm)], [c_6, c_318])).
% 3.87/1.65  tff(c_904, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_884])).
% 3.87/1.65  tff(c_921, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_3'))=k2_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_904])).
% 3.87/1.65  tff(c_2447, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_2' | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2420, c_921])).
% 3.87/1.65  tff(c_2550, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2447])).
% 3.87/1.65  tff(c_2552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_2550])).
% 3.87/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.65  
% 3.87/1.65  Inference rules
% 3.87/1.65  ----------------------
% 3.87/1.65  #Ref     : 0
% 3.87/1.65  #Sup     : 652
% 3.87/1.65  #Fact    : 0
% 3.87/1.65  #Define  : 0
% 3.87/1.65  #Split   : 0
% 3.87/1.65  #Chain   : 0
% 3.87/1.65  #Close   : 0
% 3.87/1.65  
% 3.87/1.65  Ordering : KBO
% 3.87/1.65  
% 3.87/1.65  Simplification rules
% 3.87/1.65  ----------------------
% 3.87/1.65  #Subsume      : 100
% 3.87/1.65  #Demod        : 521
% 3.87/1.65  #Tautology    : 295
% 3.87/1.65  #SimpNegUnit  : 1
% 3.87/1.65  #BackRed      : 0
% 3.87/1.65  
% 3.87/1.65  #Partial instantiations: 0
% 3.87/1.65  #Strategies tried      : 1
% 3.87/1.65  
% 3.87/1.65  Timing (in seconds)
% 3.87/1.65  ----------------------
% 3.87/1.66  Preprocessing        : 0.26
% 3.87/1.66  Parsing              : 0.14
% 3.87/1.66  CNF conversion       : 0.02
% 3.87/1.66  Main loop            : 0.63
% 3.87/1.66  Inferencing          : 0.20
% 3.87/1.66  Reduction            : 0.27
% 3.87/1.66  Demodulation         : 0.22
% 3.87/1.66  BG Simplification    : 0.03
% 3.87/1.66  Subsumption          : 0.11
% 3.87/1.66  Abstraction          : 0.03
% 3.87/1.66  MUC search           : 0.00
% 3.87/1.66  Cooper               : 0.00
% 3.87/1.66  Total                : 0.92
% 3.87/1.66  Index Insertion      : 0.00
% 3.87/1.66  Index Deletion       : 0.00
% 3.87/1.66  Index Matching       : 0.00
% 3.87/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------

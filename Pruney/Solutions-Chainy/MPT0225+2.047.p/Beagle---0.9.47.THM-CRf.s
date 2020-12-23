%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:37 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   48 (  76 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   48 ( 102 expanded)
%              Number of equality atoms :   32 (  81 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_156,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_162,plain,(
    ! [A_37] : r2_hidden(A_37,k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_4])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    ! [D_16,B_17] : r2_hidden(D_16,k2_tarski(D_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_47])).

tff(c_32,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_37,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_77,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(k1_tarski(A_28),B_29) = k1_tarski(A_28)
      | r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_91,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_67])).

tff(c_94,plain,(
    ! [D_30,B_31,A_32] :
      ( D_30 = B_31
      | D_30 = A_32
      | ~ r2_hidden(D_30,k2_tarski(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [D_33,A_34] :
      ( D_33 = A_34
      | D_33 = A_34
      | ~ r2_hidden(D_33,k1_tarski(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_111,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_91,c_108])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_37,c_111])).

tff(c_119,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_120,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_134,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_119,c_120,c_34])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden(A_13,B_14)
      | k4_xboole_0(k1_tarski(A_13),B_14) != k1_tarski(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_138,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_26])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_138])).

tff(c_145,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_146,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_185,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_145,c_146,c_36])).

tff(c_189,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_26])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.85/1.19  
% 1.85/1.19  %Foreground sorts:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Background operators:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Foreground operators:
% 1.85/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.85/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.19  
% 1.92/1.20  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.20  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.92/1.20  tff(f_51, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.92/1.20  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.92/1.20  tff(c_156, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.20  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.92/1.20  tff(c_162, plain, (![A_37]: (r2_hidden(A_37, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_4])).
% 1.92/1.20  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.20  tff(c_47, plain, (![D_16, B_17]: (r2_hidden(D_16, k2_tarski(D_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.92/1.20  tff(c_50, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_47])).
% 1.92/1.20  tff(c_32, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.20  tff(c_37, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 1.92/1.20  tff(c_77, plain, (![A_28, B_29]: (k4_xboole_0(k1_tarski(A_28), B_29)=k1_tarski(A_28) | r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.20  tff(c_30, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.20  tff(c_67, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 1.92/1.20  tff(c_91, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_67])).
% 1.92/1.20  tff(c_94, plain, (![D_30, B_31, A_32]: (D_30=B_31 | D_30=A_32 | ~r2_hidden(D_30, k2_tarski(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.92/1.20  tff(c_108, plain, (![D_33, A_34]: (D_33=A_34 | D_33=A_34 | ~r2_hidden(D_33, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 1.92/1.20  tff(c_111, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_91, c_108])).
% 1.92/1.20  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_37, c_111])).
% 1.92/1.20  tff(c_119, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_30])).
% 1.92/1.20  tff(c_120, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 1.92/1.20  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.20  tff(c_134, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_119, c_120, c_34])).
% 1.92/1.20  tff(c_26, plain, (![A_13, B_14]: (~r2_hidden(A_13, B_14) | k4_xboole_0(k1_tarski(A_13), B_14)!=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.20  tff(c_138, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_26])).
% 1.92/1.20  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_138])).
% 1.92/1.20  tff(c_145, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 1.92/1.20  tff(c_146, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 1.92/1.20  tff(c_36, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.20  tff(c_185, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_145, c_146, c_36])).
% 1.92/1.20  tff(c_189, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_26])).
% 1.92/1.20  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_189])).
% 1.92/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  Inference rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Ref     : 0
% 1.92/1.20  #Sup     : 38
% 1.92/1.20  #Fact    : 0
% 1.92/1.20  #Define  : 0
% 1.92/1.20  #Split   : 2
% 1.92/1.20  #Chain   : 0
% 1.92/1.20  #Close   : 0
% 1.92/1.20  
% 1.92/1.20  Ordering : KBO
% 1.92/1.20  
% 1.92/1.20  Simplification rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Subsume      : 2
% 1.92/1.20  #Demod        : 10
% 1.92/1.20  #Tautology    : 27
% 1.92/1.20  #SimpNegUnit  : 1
% 1.92/1.20  #BackRed      : 0
% 1.92/1.20  
% 1.92/1.20  #Partial instantiations: 0
% 1.92/1.20  #Strategies tried      : 1
% 1.92/1.20  
% 1.92/1.20  Timing (in seconds)
% 1.92/1.20  ----------------------
% 1.92/1.21  Preprocessing        : 0.30
% 1.92/1.21  Parsing              : 0.15
% 1.92/1.21  CNF conversion       : 0.02
% 1.92/1.21  Main loop            : 0.14
% 1.92/1.21  Inferencing          : 0.05
% 1.92/1.21  Reduction            : 0.04
% 1.92/1.21  Demodulation         : 0.03
% 1.92/1.21  BG Simplification    : 0.01
% 1.92/1.21  Subsumption          : 0.02
% 1.92/1.21  Abstraction          : 0.01
% 1.92/1.21  MUC search           : 0.00
% 1.92/1.21  Cooper               : 0.00
% 1.92/1.21  Total                : 0.46
% 1.92/1.21  Index Insertion      : 0.00
% 1.92/1.21  Index Deletion       : 0.00
% 1.92/1.21  Index Matching       : 0.00
% 1.92/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

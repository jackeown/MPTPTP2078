%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:43 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   34 (  86 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 177 expanded)
%              Number of equality atoms :   14 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_28,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [D_17,A_18,B_19] :
      ( r2_hidden(D_17,k4_xboole_0(A_18,B_19))
      | r2_hidden(D_17,B_19)
      | ~ r2_hidden(D_17,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k4_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    ! [D_10,A_11,B_12] :
      ( r2_hidden(D_10,A_11)
      | ~ r2_hidden(D_10,k4_xboole_0(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [D_10] :
      ( r2_hidden(D_10,'#skF_5')
      | ~ r2_hidden(D_10,k4_xboole_0('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_35])).

tff(c_58,plain,(
    ! [D_17] :
      ( r2_hidden(D_17,'#skF_5')
      | ~ r2_hidden(D_17,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_38])).

tff(c_169,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_3'(A_30,B_31),B_31)
      | ~ r2_hidden('#skF_4'(A_30,B_31),B_31)
      | B_31 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,k4_xboole_0('#skF_6','#skF_5'))
      | r2_hidden(D_22,'#skF_6')
      | ~ r2_hidden(D_22,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_44])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,'#skF_6')
      | ~ r2_hidden(D_22,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_228,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_3'(A_36,'#skF_5'),'#skF_6')
      | ~ r2_hidden('#skF_4'(A_36,'#skF_5'),'#skF_5')
      | A_36 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_169,c_83])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8),A_7)
      | ~ r2_hidden('#skF_4'(A_7,B_8),B_8)
      | B_8 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_235,plain,
    ( ~ r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_228,c_20])).

tff(c_240,plain,(
    ~ r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_235])).

tff(c_244,plain,(
    ~ r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_240])).

tff(c_99,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_3'(A_26,B_27),B_27)
      | r2_hidden('#skF_4'(A_26,B_27),A_26)
      | B_27 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_246,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_3'(A_37,'#skF_5'),'#skF_6')
      | r2_hidden('#skF_4'(A_37,'#skF_5'),A_37)
      | A_37 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_99,c_83])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r2_hidden('#skF_4'(A_7,B_8),A_7)
      | B_8 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_250,plain,
    ( r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_246,c_24])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_244,c_28,c_244,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:02:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.26  %$ r2_hidden > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.93/1.26  
% 1.93/1.26  %Foreground sorts:
% 1.93/1.26  
% 1.93/1.26  
% 1.93/1.26  %Background operators:
% 1.93/1.26  
% 1.93/1.26  
% 1.93/1.26  %Foreground operators:
% 1.93/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.93/1.26  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.26  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.93/1.26  
% 1.93/1.27  tff(f_47, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 1.93/1.27  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.93/1.27  tff(f_42, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.93/1.27  tff(c_28, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.27  tff(c_44, plain, (![D_17, A_18, B_19]: (r2_hidden(D_17, k4_xboole_0(A_18, B_19)) | r2_hidden(D_17, B_19) | ~r2_hidden(D_17, A_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.27  tff(c_30, plain, (k4_xboole_0('#skF_5', '#skF_6')=k4_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.27  tff(c_35, plain, (![D_10, A_11, B_12]: (r2_hidden(D_10, A_11) | ~r2_hidden(D_10, k4_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.27  tff(c_38, plain, (![D_10]: (r2_hidden(D_10, '#skF_5') | ~r2_hidden(D_10, k4_xboole_0('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_30, c_35])).
% 1.93/1.27  tff(c_58, plain, (![D_17]: (r2_hidden(D_17, '#skF_5') | ~r2_hidden(D_17, '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_38])).
% 1.93/1.27  tff(c_169, plain, (![A_30, B_31]: (r2_hidden('#skF_3'(A_30, B_31), B_31) | ~r2_hidden('#skF_4'(A_30, B_31), B_31) | B_31=A_30)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.27  tff(c_68, plain, (![D_22]: (r2_hidden(D_22, k4_xboole_0('#skF_6', '#skF_5')) | r2_hidden(D_22, '#skF_6') | ~r2_hidden(D_22, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_44])).
% 1.93/1.27  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.27  tff(c_83, plain, (![D_22]: (r2_hidden(D_22, '#skF_6') | ~r2_hidden(D_22, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_4])).
% 1.93/1.27  tff(c_228, plain, (![A_36]: (r2_hidden('#skF_3'(A_36, '#skF_5'), '#skF_6') | ~r2_hidden('#skF_4'(A_36, '#skF_5'), '#skF_5') | A_36='#skF_5')), inference(resolution, [status(thm)], [c_169, c_83])).
% 1.93/1.27  tff(c_20, plain, (![A_7, B_8]: (~r2_hidden('#skF_3'(A_7, B_8), A_7) | ~r2_hidden('#skF_4'(A_7, B_8), B_8) | B_8=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.27  tff(c_235, plain, (~r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_228, c_20])).
% 1.93/1.27  tff(c_240, plain, (~r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_235])).
% 1.93/1.27  tff(c_244, plain, (~r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_58, c_240])).
% 1.93/1.27  tff(c_99, plain, (![A_26, B_27]: (r2_hidden('#skF_3'(A_26, B_27), B_27) | r2_hidden('#skF_4'(A_26, B_27), A_26) | B_27=A_26)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.27  tff(c_246, plain, (![A_37]: (r2_hidden('#skF_3'(A_37, '#skF_5'), '#skF_6') | r2_hidden('#skF_4'(A_37, '#skF_5'), A_37) | A_37='#skF_5')), inference(resolution, [status(thm)], [c_99, c_83])).
% 1.93/1.27  tff(c_24, plain, (![A_7, B_8]: (~r2_hidden('#skF_3'(A_7, B_8), A_7) | r2_hidden('#skF_4'(A_7, B_8), A_7) | B_8=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.27  tff(c_250, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_246, c_24])).
% 1.93/1.27  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_244, c_28, c_244, c_250])).
% 1.93/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.27  
% 1.93/1.27  Inference rules
% 1.93/1.27  ----------------------
% 1.93/1.27  #Ref     : 0
% 1.93/1.27  #Sup     : 49
% 1.93/1.27  #Fact    : 0
% 1.93/1.27  #Define  : 0
% 1.93/1.27  #Split   : 0
% 1.93/1.27  #Chain   : 0
% 1.93/1.27  #Close   : 0
% 1.93/1.27  
% 1.93/1.27  Ordering : KBO
% 1.93/1.27  
% 1.93/1.27  Simplification rules
% 1.93/1.27  ----------------------
% 1.93/1.27  #Subsume      : 4
% 1.93/1.27  #Demod        : 0
% 1.93/1.27  #Tautology    : 12
% 1.93/1.27  #SimpNegUnit  : 3
% 1.93/1.27  #BackRed      : 0
% 1.93/1.27  
% 1.93/1.27  #Partial instantiations: 0
% 1.93/1.27  #Strategies tried      : 1
% 1.93/1.27  
% 1.93/1.27  Timing (in seconds)
% 1.93/1.27  ----------------------
% 1.93/1.28  Preprocessing        : 0.27
% 1.93/1.28  Parsing              : 0.14
% 1.93/1.28  CNF conversion       : 0.02
% 1.93/1.28  Main loop            : 0.19
% 1.93/1.28  Inferencing          : 0.07
% 1.93/1.28  Reduction            : 0.04
% 1.93/1.28  Demodulation         : 0.03
% 1.93/1.28  BG Simplification    : 0.02
% 1.93/1.28  Subsumption          : 0.05
% 1.93/1.28  Abstraction          : 0.01
% 1.93/1.28  MUC search           : 0.00
% 1.93/1.28  Cooper               : 0.00
% 1.93/1.28  Total                : 0.49
% 1.93/1.28  Index Insertion      : 0.00
% 1.93/1.28  Index Deletion       : 0.00
% 1.93/1.28  Index Matching       : 0.00
% 1.93/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

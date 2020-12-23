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
% DateTime   : Thu Dec  3 09:43:24 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_3'(A_22,B_23),B_23)
      | r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [D_14,B_15,A_16] :
      ( ~ r2_hidden(D_14,B_15)
      | ~ r2_hidden(D_14,k4_xboole_0(A_16,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [D_14,A_12] :
      ( ~ r2_hidden(D_14,A_12)
      | ~ r2_hidden(D_14,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_73,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden('#skF_3'(A_26,B_27),k1_xboole_0)
      | r1_xboole_0(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_45,c_39])).

tff(c_83,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.25  
% 1.73/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.26  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.73/1.26  
% 1.73/1.26  %Foreground sorts:
% 1.73/1.26  
% 1.73/1.26  
% 1.73/1.26  %Background operators:
% 1.73/1.26  
% 1.73/1.26  
% 1.73/1.26  %Foreground operators:
% 1.73/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.73/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.73/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.73/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.73/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.26  
% 1.73/1.27  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.73/1.27  tff(f_55, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.73/1.27  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.73/1.27  tff(f_58, negated_conjecture, ~(![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.73/1.27  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.73/1.27  tff(c_45, plain, (![A_22, B_23]: (r2_hidden('#skF_3'(A_22, B_23), B_23) | r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.73/1.27  tff(c_26, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.73/1.27  tff(c_36, plain, (![D_14, B_15, A_16]: (~r2_hidden(D_14, B_15) | ~r2_hidden(D_14, k4_xboole_0(A_16, B_15)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.27  tff(c_39, plain, (![D_14, A_12]: (~r2_hidden(D_14, A_12) | ~r2_hidden(D_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_36])).
% 1.73/1.27  tff(c_73, plain, (![A_26, B_27]: (~r2_hidden('#skF_3'(A_26, B_27), k1_xboole_0) | r1_xboole_0(A_26, B_27))), inference(resolution, [status(thm)], [c_45, c_39])).
% 1.73/1.27  tff(c_83, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_73])).
% 1.73/1.27  tff(c_28, plain, (~r1_xboole_0('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.73/1.27  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_28])).
% 1.73/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.27  
% 1.73/1.27  Inference rules
% 1.73/1.27  ----------------------
% 1.73/1.27  #Ref     : 0
% 1.73/1.27  #Sup     : 13
% 1.73/1.27  #Fact    : 0
% 1.73/1.27  #Define  : 0
% 1.73/1.27  #Split   : 0
% 1.73/1.27  #Chain   : 0
% 1.73/1.27  #Close   : 0
% 1.73/1.27  
% 1.73/1.27  Ordering : KBO
% 1.73/1.27  
% 1.73/1.27  Simplification rules
% 1.73/1.27  ----------------------
% 1.73/1.27  #Subsume      : 1
% 1.73/1.27  #Demod        : 1
% 1.73/1.27  #Tautology    : 3
% 1.73/1.27  #SimpNegUnit  : 0
% 1.73/1.27  #BackRed      : 1
% 1.73/1.27  
% 1.73/1.27  #Partial instantiations: 0
% 1.73/1.27  #Strategies tried      : 1
% 1.73/1.27  
% 1.73/1.27  Timing (in seconds)
% 1.73/1.27  ----------------------
% 1.73/1.27  Preprocessing        : 0.28
% 1.73/1.27  Parsing              : 0.14
% 1.73/1.27  CNF conversion       : 0.02
% 1.73/1.27  Main loop            : 0.10
% 1.73/1.27  Inferencing          : 0.04
% 1.73/1.27  Reduction            : 0.03
% 1.73/1.27  Demodulation         : 0.02
% 1.73/1.27  BG Simplification    : 0.01
% 1.73/1.27  Subsumption          : 0.02
% 1.73/1.27  Abstraction          : 0.00
% 1.73/1.27  MUC search           : 0.00
% 1.73/1.27  Cooper               : 0.00
% 1.73/1.27  Total                : 0.41
% 1.73/1.27  Index Insertion      : 0.00
% 1.73/1.27  Index Deletion       : 0.00
% 1.73/1.27  Index Matching       : 0.00
% 1.73/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

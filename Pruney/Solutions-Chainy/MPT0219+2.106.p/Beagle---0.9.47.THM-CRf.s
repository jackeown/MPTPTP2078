%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:03 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   41 (  44 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   30 (  34 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_140,plain,(
    ! [A_52,B_53,C_54,D_55] : k2_xboole_0(k1_enumset1(A_52,B_53,C_54),k1_tarski(D_55)) = k2_enumset1(A_52,B_53,C_54,D_55) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_149,plain,(
    ! [A_21,B_22,D_55] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(D_55)) = k2_enumset1(A_21,A_21,B_22,D_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_140])).

tff(c_153,plain,(
    ! [A_56,B_57,D_58] : k2_xboole_0(k2_tarski(A_56,B_57),k1_tarski(D_58)) = k1_enumset1(A_56,B_57,D_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_149])).

tff(c_162,plain,(
    ! [A_20,D_58] : k2_xboole_0(k1_tarski(A_20),k1_tarski(D_58)) = k1_enumset1(A_20,A_20,D_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_153])).

tff(c_166,plain,(
    ! [A_59,D_60] : k2_xboole_0(k1_tarski(A_59),k1_tarski(D_60)) = k2_tarski(A_59,D_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_162])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_172,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_46])).

tff(c_20,plain,(
    ! [D_15,A_10] : r2_hidden(D_15,k2_tarski(A_10,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_190,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_20])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_202,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_190,c_6])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:38:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.24  
% 2.00/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.24  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.00/1.24  
% 2.00/1.24  %Foreground sorts:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Background operators:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Foreground operators:
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.00/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.00/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.00/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.24  
% 2.00/1.25  tff(f_58, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.00/1.25  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.00/1.25  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.00/1.25  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.00/1.25  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.00/1.25  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.00/1.25  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.00/1.25  tff(c_44, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.00/1.25  tff(c_40, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.00/1.25  tff(c_38, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.00/1.25  tff(c_42, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.25  tff(c_140, plain, (![A_52, B_53, C_54, D_55]: (k2_xboole_0(k1_enumset1(A_52, B_53, C_54), k1_tarski(D_55))=k2_enumset1(A_52, B_53, C_54, D_55))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.25  tff(c_149, plain, (![A_21, B_22, D_55]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(D_55))=k2_enumset1(A_21, A_21, B_22, D_55))), inference(superposition, [status(thm), theory('equality')], [c_40, c_140])).
% 2.00/1.25  tff(c_153, plain, (![A_56, B_57, D_58]: (k2_xboole_0(k2_tarski(A_56, B_57), k1_tarski(D_58))=k1_enumset1(A_56, B_57, D_58))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_149])).
% 2.00/1.25  tff(c_162, plain, (![A_20, D_58]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(D_58))=k1_enumset1(A_20, A_20, D_58))), inference(superposition, [status(thm), theory('equality')], [c_38, c_153])).
% 2.00/1.25  tff(c_166, plain, (![A_59, D_60]: (k2_xboole_0(k1_tarski(A_59), k1_tarski(D_60))=k2_tarski(A_59, D_60))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_162])).
% 2.00/1.25  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.00/1.25  tff(c_172, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_166, c_46])).
% 2.00/1.25  tff(c_20, plain, (![D_15, A_10]: (r2_hidden(D_15, k2_tarski(A_10, D_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.25  tff(c_190, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_20])).
% 2.00/1.25  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.00/1.25  tff(c_202, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_190, c_6])).
% 2.00/1.25  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_202])).
% 2.00/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.25  
% 2.00/1.25  Inference rules
% 2.00/1.25  ----------------------
% 2.00/1.25  #Ref     : 0
% 2.00/1.25  #Sup     : 37
% 2.00/1.25  #Fact    : 0
% 2.00/1.25  #Define  : 0
% 2.00/1.25  #Split   : 0
% 2.00/1.25  #Chain   : 0
% 2.00/1.25  #Close   : 0
% 2.00/1.25  
% 2.00/1.25  Ordering : KBO
% 2.00/1.25  
% 2.00/1.25  Simplification rules
% 2.00/1.25  ----------------------
% 2.00/1.25  #Subsume      : 2
% 2.00/1.25  #Demod        : 7
% 2.00/1.25  #Tautology    : 27
% 2.00/1.25  #SimpNegUnit  : 1
% 2.00/1.25  #BackRed      : 0
% 2.00/1.25  
% 2.00/1.25  #Partial instantiations: 0
% 2.00/1.25  #Strategies tried      : 1
% 2.00/1.25  
% 2.00/1.25  Timing (in seconds)
% 2.00/1.25  ----------------------
% 2.00/1.25  Preprocessing        : 0.31
% 2.00/1.25  Parsing              : 0.16
% 2.00/1.25  CNF conversion       : 0.02
% 2.00/1.25  Main loop            : 0.14
% 2.00/1.25  Inferencing          : 0.05
% 2.00/1.25  Reduction            : 0.05
% 2.00/1.25  Demodulation         : 0.03
% 2.00/1.25  BG Simplification    : 0.01
% 2.00/1.25  Subsumption          : 0.03
% 2.00/1.25  Abstraction          : 0.01
% 2.00/1.25  MUC search           : 0.00
% 2.00/1.25  Cooper               : 0.00
% 2.00/1.25  Total                : 0.47
% 2.00/1.25  Index Insertion      : 0.00
% 2.00/1.25  Index Deletion       : 0.00
% 2.00/1.25  Index Matching       : 0.00
% 2.00/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

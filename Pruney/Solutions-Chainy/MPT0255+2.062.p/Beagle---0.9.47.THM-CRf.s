%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:47 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_42,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_297,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(k2_tarski(A_73,B_74),C_75)
      | ~ r2_hidden(B_74,C_75)
      | ~ r2_hidden(A_73,C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_313,plain,(
    ! [A_76,C_77] :
      ( r1_tarski(k1_tarski(A_76),C_77)
      | ~ r2_hidden(A_76,C_77)
      | ~ r2_hidden(A_76,C_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_297])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_322,plain,(
    ! [A_78,C_79] :
      ( k2_xboole_0(k1_tarski(A_78),C_79) = C_79
      | ~ r2_hidden(A_78,C_79) ) ),
    inference(resolution,[status(thm)],[c_313,c_22])).

tff(c_54,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_381,plain,(
    ! [A_78] : ~ r2_hidden(A_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_54])).

tff(c_26,plain,(
    ! [D_16,A_11] : r2_hidden(D_16,k2_tarski(A_11,D_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_196,plain,(
    ! [D_47,A_48,B_49] :
      ( ~ r2_hidden(D_47,A_48)
      | r2_hidden(D_47,k2_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_252,plain,(
    ! [D_65] :
      ( ~ r2_hidden(D_65,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_65,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_196])).

tff(c_262,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_252])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:56:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.32  
% 2.32/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.32  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.32/1.32  
% 2.32/1.32  %Foreground sorts:
% 2.32/1.32  
% 2.32/1.32  
% 2.32/1.32  %Background operators:
% 2.32/1.32  
% 2.32/1.32  
% 2.32/1.32  %Foreground operators:
% 2.32/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.32/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.32/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.32/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.32  
% 2.32/1.33  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.32/1.33  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.32/1.33  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.32/1.33  tff(f_64, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.32/1.33  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.32/1.33  tff(f_68, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.32/1.33  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.32/1.33  tff(c_42, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.32/1.33  tff(c_297, plain, (![A_73, B_74, C_75]: (r1_tarski(k2_tarski(A_73, B_74), C_75) | ~r2_hidden(B_74, C_75) | ~r2_hidden(A_73, C_75))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.32/1.33  tff(c_313, plain, (![A_76, C_77]: (r1_tarski(k1_tarski(A_76), C_77) | ~r2_hidden(A_76, C_77) | ~r2_hidden(A_76, C_77))), inference(superposition, [status(thm), theory('equality')], [c_42, c_297])).
% 2.32/1.33  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.32/1.33  tff(c_322, plain, (![A_78, C_79]: (k2_xboole_0(k1_tarski(A_78), C_79)=C_79 | ~r2_hidden(A_78, C_79))), inference(resolution, [status(thm)], [c_313, c_22])).
% 2.32/1.33  tff(c_54, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.33  tff(c_381, plain, (![A_78]: (~r2_hidden(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_322, c_54])).
% 2.32/1.33  tff(c_26, plain, (![D_16, A_11]: (r2_hidden(D_16, k2_tarski(A_11, D_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.33  tff(c_56, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.32/1.33  tff(c_196, plain, (![D_47, A_48, B_49]: (~r2_hidden(D_47, A_48) | r2_hidden(D_47, k2_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.32/1.33  tff(c_252, plain, (![D_65]: (~r2_hidden(D_65, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_56, c_196])).
% 2.32/1.33  tff(c_262, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_252])).
% 2.32/1.33  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_262])).
% 2.32/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.33  
% 2.32/1.33  Inference rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Ref     : 0
% 2.32/1.33  #Sup     : 82
% 2.32/1.33  #Fact    : 0
% 2.32/1.33  #Define  : 0
% 2.32/1.33  #Split   : 0
% 2.32/1.33  #Chain   : 0
% 2.32/1.33  #Close   : 0
% 2.32/1.33  
% 2.32/1.33  Ordering : KBO
% 2.32/1.33  
% 2.32/1.33  Simplification rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Subsume      : 15
% 2.32/1.33  #Demod        : 6
% 2.32/1.33  #Tautology    : 37
% 2.32/1.33  #SimpNegUnit  : 4
% 2.32/1.33  #BackRed      : 4
% 2.32/1.33  
% 2.32/1.33  #Partial instantiations: 0
% 2.32/1.33  #Strategies tried      : 1
% 2.32/1.33  
% 2.32/1.33  Timing (in seconds)
% 2.32/1.33  ----------------------
% 2.32/1.33  Preprocessing        : 0.32
% 2.32/1.33  Parsing              : 0.16
% 2.32/1.33  CNF conversion       : 0.02
% 2.32/1.33  Main loop            : 0.24
% 2.32/1.33  Inferencing          : 0.08
% 2.32/1.33  Reduction            : 0.08
% 2.32/1.33  Demodulation         : 0.06
% 2.32/1.33  BG Simplification    : 0.02
% 2.32/1.33  Subsumption          : 0.05
% 2.32/1.33  Abstraction          : 0.01
% 2.32/1.33  MUC search           : 0.00
% 2.32/1.33  Cooper               : 0.00
% 2.32/1.33  Total                : 0.59
% 2.32/1.34  Index Insertion      : 0.00
% 2.32/1.34  Index Deletion       : 0.00
% 2.32/1.34  Index Matching       : 0.00
% 2.32/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

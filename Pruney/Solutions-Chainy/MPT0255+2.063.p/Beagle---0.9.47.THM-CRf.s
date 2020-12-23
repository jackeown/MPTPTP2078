%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:47 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_44,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_257,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(k2_tarski(A_69,B_70),C_71)
      | ~ r2_hidden(B_70,C_71)
      | ~ r2_hidden(A_69,C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_273,plain,(
    ! [A_72,C_73] :
      ( r1_tarski(k1_tarski(A_72),C_73)
      | ~ r2_hidden(A_72,C_73)
      | ~ r2_hidden(A_72,C_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_257])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_282,plain,(
    ! [A_74,C_75] :
      ( k2_xboole_0(k1_tarski(A_74),C_75) = C_75
      | ~ r2_hidden(A_74,C_75) ) ),
    inference(resolution,[status(thm)],[c_273,c_22])).

tff(c_54,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_320,plain,(
    ! [A_74] : ~ r2_hidden(A_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_54])).

tff(c_30,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_165,plain,(
    ! [D_48,A_49,B_50] :
      ( ~ r2_hidden(D_48,A_49)
      | r2_hidden(D_48,k2_xboole_0(A_49,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_179,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_165])).

tff(c_189,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_179])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.42  
% 2.22/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.42  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.22/1.42  
% 2.22/1.42  %Foreground sorts:
% 2.22/1.42  
% 2.22/1.42  
% 2.22/1.42  %Background operators:
% 2.22/1.42  
% 2.22/1.42  
% 2.22/1.42  %Foreground operators:
% 2.22/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.22/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.22/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.22/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.22/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.42  
% 2.22/1.43  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/1.43  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.22/1.43  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.22/1.43  tff(f_64, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.22/1.43  tff(f_51, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.22/1.43  tff(f_68, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.22/1.43  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.22/1.43  tff(c_44, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.43  tff(c_257, plain, (![A_69, B_70, C_71]: (r1_tarski(k2_tarski(A_69, B_70), C_71) | ~r2_hidden(B_70, C_71) | ~r2_hidden(A_69, C_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.43  tff(c_273, plain, (![A_72, C_73]: (r1_tarski(k1_tarski(A_72), C_73) | ~r2_hidden(A_72, C_73) | ~r2_hidden(A_72, C_73))), inference(superposition, [status(thm), theory('equality')], [c_44, c_257])).
% 2.22/1.43  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.22/1.43  tff(c_282, plain, (![A_74, C_75]: (k2_xboole_0(k1_tarski(A_74), C_75)=C_75 | ~r2_hidden(A_74, C_75))), inference(resolution, [status(thm)], [c_273, c_22])).
% 2.22/1.43  tff(c_54, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.43  tff(c_320, plain, (![A_74]: (~r2_hidden(A_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_282, c_54])).
% 2.22/1.43  tff(c_30, plain, (![D_18, B_14]: (r2_hidden(D_18, k2_tarski(D_18, B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.22/1.43  tff(c_56, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.43  tff(c_165, plain, (![D_48, A_49, B_50]: (~r2_hidden(D_48, A_49) | r2_hidden(D_48, k2_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.22/1.43  tff(c_179, plain, (![D_52]: (~r2_hidden(D_52, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_56, c_165])).
% 2.22/1.43  tff(c_189, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_179])).
% 2.22/1.43  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_189])).
% 2.22/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.43  
% 2.22/1.43  Inference rules
% 2.22/1.43  ----------------------
% 2.22/1.43  #Ref     : 0
% 2.22/1.43  #Sup     : 67
% 2.22/1.43  #Fact    : 0
% 2.22/1.43  #Define  : 0
% 2.22/1.43  #Split   : 0
% 2.22/1.43  #Chain   : 0
% 2.22/1.43  #Close   : 0
% 2.22/1.43  
% 2.22/1.43  Ordering : KBO
% 2.22/1.43  
% 2.22/1.43  Simplification rules
% 2.22/1.43  ----------------------
% 2.22/1.43  #Subsume      : 10
% 2.22/1.43  #Demod        : 4
% 2.22/1.43  #Tautology    : 34
% 2.22/1.43  #SimpNegUnit  : 4
% 2.22/1.43  #BackRed      : 4
% 2.22/1.43  
% 2.22/1.43  #Partial instantiations: 0
% 2.22/1.43  #Strategies tried      : 1
% 2.22/1.43  
% 2.22/1.43  Timing (in seconds)
% 2.22/1.43  ----------------------
% 2.22/1.43  Preprocessing        : 0.40
% 2.22/1.43  Parsing              : 0.22
% 2.22/1.43  CNF conversion       : 0.03
% 2.22/1.43  Main loop            : 0.26
% 2.22/1.43  Inferencing          : 0.07
% 2.22/1.43  Reduction            : 0.09
% 2.22/1.43  Demodulation         : 0.07
% 2.22/1.44  BG Simplification    : 0.02
% 2.22/1.44  Subsumption          : 0.06
% 2.22/1.44  Abstraction          : 0.01
% 2.22/1.44  MUC search           : 0.00
% 2.22/1.44  Cooper               : 0.00
% 2.22/1.44  Total                : 0.69
% 2.22/1.44  Index Insertion      : 0.00
% 2.22/1.44  Index Deletion       : 0.00
% 2.22/1.44  Index Matching       : 0.00
% 2.22/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

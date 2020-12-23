%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:31 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(c_26,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_402,plain,(
    ! [A_92,B_93,C_94] : r1_tarski(k2_xboole_0(k3_xboole_0(A_92,B_93),k3_xboole_0(A_92,C_94)),k2_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_426,plain,(
    ! [A_95,B_96,C_97] : r1_tarski(k3_xboole_0(A_95,B_96),k2_xboole_0(B_96,C_97)) ),
    inference(resolution,[status(thm)],[c_402,c_2])).

tff(c_442,plain,(
    ! [A_98,A_99] : r1_tarski(k3_xboole_0(A_98,A_99),A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_426])).

tff(c_455,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_442])).

tff(c_16,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [A_19,C_40,B_20] :
      ( r1_tarski(k1_tarski(A_19),C_40)
      | ~ r1_tarski(k2_tarski(A_19,B_20),C_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_83])).

tff(c_464,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_86])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,B_24)
      | ~ r1_tarski(k1_tarski(A_23),B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_483,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_464,c_22])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.31  
% 2.22/1.32  tff(f_63, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 2.22/1.32  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.22/1.32  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.22/1.32  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.22/1.32  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.22/1.32  tff(f_58, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.22/1.32  tff(c_26, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.32  tff(c_28, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.32  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.32  tff(c_402, plain, (![A_92, B_93, C_94]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_92, B_93), k3_xboole_0(A_92, C_94)), k2_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.32  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.32  tff(c_426, plain, (![A_95, B_96, C_97]: (r1_tarski(k3_xboole_0(A_95, B_96), k2_xboole_0(B_96, C_97)))), inference(resolution, [status(thm)], [c_402, c_2])).
% 2.22/1.32  tff(c_442, plain, (![A_98, A_99]: (r1_tarski(k3_xboole_0(A_98, A_99), A_99))), inference(superposition, [status(thm), theory('equality')], [c_6, c_426])).
% 2.22/1.32  tff(c_455, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_442])).
% 2.22/1.32  tff(c_16, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.22/1.32  tff(c_83, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.32  tff(c_86, plain, (![A_19, C_40, B_20]: (r1_tarski(k1_tarski(A_19), C_40) | ~r1_tarski(k2_tarski(A_19, B_20), C_40))), inference(superposition, [status(thm), theory('equality')], [c_16, c_83])).
% 2.22/1.32  tff(c_464, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_455, c_86])).
% 2.22/1.32  tff(c_22, plain, (![A_23, B_24]: (r2_hidden(A_23, B_24) | ~r1_tarski(k1_tarski(A_23), B_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.22/1.32  tff(c_483, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_464, c_22])).
% 2.22/1.32  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_483])).
% 2.22/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.32  
% 2.22/1.32  Inference rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Ref     : 0
% 2.22/1.32  #Sup     : 109
% 2.22/1.32  #Fact    : 2
% 2.22/1.32  #Define  : 0
% 2.22/1.32  #Split   : 0
% 2.22/1.32  #Chain   : 0
% 2.22/1.32  #Close   : 0
% 2.22/1.32  
% 2.22/1.32  Ordering : KBO
% 2.22/1.32  
% 2.22/1.32  Simplification rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Subsume      : 4
% 2.22/1.32  #Demod        : 15
% 2.22/1.32  #Tautology    : 34
% 2.22/1.32  #SimpNegUnit  : 1
% 2.22/1.32  #BackRed      : 0
% 2.22/1.32  
% 2.22/1.32  #Partial instantiations: 0
% 2.22/1.32  #Strategies tried      : 1
% 2.22/1.32  
% 2.22/1.32  Timing (in seconds)
% 2.22/1.32  ----------------------
% 2.22/1.32  Preprocessing        : 0.28
% 2.22/1.32  Parsing              : 0.16
% 2.22/1.32  CNF conversion       : 0.02
% 2.22/1.32  Main loop            : 0.28
% 2.22/1.32  Inferencing          : 0.11
% 2.22/1.32  Reduction            : 0.08
% 2.22/1.32  Demodulation         : 0.06
% 2.22/1.32  BG Simplification    : 0.01
% 2.22/1.32  Subsumption          : 0.05
% 2.22/1.32  Abstraction          : 0.01
% 2.22/1.32  MUC search           : 0.00
% 2.22/1.32  Cooper               : 0.00
% 2.22/1.32  Total                : 0.58
% 2.22/1.32  Index Insertion      : 0.00
% 2.22/1.32  Index Deletion       : 0.00
% 2.22/1.32  Index Matching       : 0.00
% 2.22/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

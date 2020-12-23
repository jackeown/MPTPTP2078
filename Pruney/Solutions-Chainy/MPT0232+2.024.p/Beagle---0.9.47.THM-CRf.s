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
% DateTime   : Thu Dec  3 09:49:22 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  54 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_99,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_111,plain,(
    ! [B_51,A_50] : r2_hidden(B_51,k2_tarski(A_50,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_30])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_89])).

tff(c_122,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_140,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_122])).

tff(c_192,plain,(
    ! [D_68,B_69,A_70] :
      ( ~ r2_hidden(D_68,B_69)
      | ~ r2_hidden(D_68,k4_xboole_0(A_70,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_205,plain,(
    ! [D_71,A_72] :
      ( ~ r2_hidden(D_71,A_72)
      | ~ r2_hidden(D_71,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_192])).

tff(c_218,plain,(
    ! [B_51] : ~ r2_hidden(B_51,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_111,c_205])).

tff(c_66,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_68,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_234,plain,(
    ! [B_77,A_78] :
      ( k1_tarski(B_77) = A_78
      | k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,k1_tarski(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_241,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_234])).

tff(c_252,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_241])).

tff(c_265,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_111])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:54:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.93/1.23  
% 1.93/1.23  %Foreground sorts:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Background operators:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Foreground operators:
% 1.93/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.23  tff('#skF_7', type, '#skF_7': $i).
% 1.93/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.93/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.23  
% 2.18/1.24  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.18/1.24  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.18/1.24  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.18/1.24  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.18/1.24  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.18/1.24  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.18/1.24  tff(f_77, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.18/1.24  tff(f_72, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.18/1.24  tff(c_99, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.18/1.24  tff(c_30, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.24  tff(c_111, plain, (![B_51, A_50]: (r2_hidden(B_51, k2_tarski(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_30])).
% 2.18/1.24  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.24  tff(c_89, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.24  tff(c_92, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_89])).
% 2.18/1.24  tff(c_122, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.24  tff(c_140, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_92, c_122])).
% 2.18/1.24  tff(c_192, plain, (![D_68, B_69, A_70]: (~r2_hidden(D_68, B_69) | ~r2_hidden(D_68, k4_xboole_0(A_70, B_69)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.24  tff(c_205, plain, (![D_71, A_72]: (~r2_hidden(D_71, A_72) | ~r2_hidden(D_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_140, c_192])).
% 2.18/1.24  tff(c_218, plain, (![B_51]: (~r2_hidden(B_51, k1_xboole_0))), inference(resolution, [status(thm)], [c_111, c_205])).
% 2.18/1.24  tff(c_66, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.18/1.24  tff(c_68, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.18/1.24  tff(c_234, plain, (![B_77, A_78]: (k1_tarski(B_77)=A_78 | k1_xboole_0=A_78 | ~r1_tarski(A_78, k1_tarski(B_77)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.24  tff(c_241, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_234])).
% 2.18/1.24  tff(c_252, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_241])).
% 2.18/1.24  tff(c_265, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_252, c_111])).
% 2.18/1.24  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_265])).
% 2.18/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  Inference rules
% 2.18/1.24  ----------------------
% 2.18/1.24  #Ref     : 0
% 2.18/1.24  #Sup     : 50
% 2.18/1.24  #Fact    : 0
% 2.18/1.24  #Define  : 0
% 2.18/1.24  #Split   : 0
% 2.18/1.24  #Chain   : 0
% 2.18/1.24  #Close   : 0
% 2.18/1.24  
% 2.18/1.24  Ordering : KBO
% 2.18/1.24  
% 2.18/1.24  Simplification rules
% 2.18/1.24  ----------------------
% 2.18/1.24  #Subsume      : 12
% 2.18/1.24  #Demod        : 9
% 2.18/1.24  #Tautology    : 27
% 2.18/1.24  #SimpNegUnit  : 2
% 2.18/1.24  #BackRed      : 3
% 2.18/1.24  
% 2.18/1.24  #Partial instantiations: 0
% 2.18/1.24  #Strategies tried      : 1
% 2.18/1.24  
% 2.18/1.24  Timing (in seconds)
% 2.18/1.24  ----------------------
% 2.18/1.24  Preprocessing        : 0.31
% 2.18/1.24  Parsing              : 0.15
% 2.18/1.24  CNF conversion       : 0.03
% 2.18/1.24  Main loop            : 0.18
% 2.18/1.24  Inferencing          : 0.05
% 2.18/1.24  Reduction            : 0.06
% 2.18/1.24  Demodulation         : 0.05
% 2.18/1.24  BG Simplification    : 0.02
% 2.18/1.24  Subsumption          : 0.04
% 2.18/1.24  Abstraction          : 0.01
% 2.18/1.24  MUC search           : 0.00
% 2.18/1.24  Cooper               : 0.00
% 2.18/1.24  Total                : 0.51
% 2.18/1.24  Index Insertion      : 0.00
% 2.18/1.24  Index Deletion       : 0.00
% 2.18/1.24  Index Matching       : 0.00
% 2.18/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

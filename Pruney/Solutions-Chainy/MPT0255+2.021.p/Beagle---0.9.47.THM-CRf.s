%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:42 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_12,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_179,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,k3_xboole_0(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_182,plain,(
    ! [A_9,C_52] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_179])).

tff(c_184,plain,(
    ! [C_52] : ~ r2_hidden(C_52,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_182])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_121,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_149,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_152,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) = k2_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_121,c_149])).

tff(c_160,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_152])).

tff(c_20,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_172,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_20])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.30  
% 1.79/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.79/1.30  
% 1.79/1.30  %Foreground sorts:
% 1.79/1.30  
% 1.79/1.30  
% 1.79/1.30  %Background operators:
% 1.79/1.30  
% 1.79/1.30  
% 1.79/1.30  %Foreground operators:
% 1.79/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.79/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.79/1.30  tff('#skF_6', type, '#skF_6': $i).
% 1.79/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.79/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.79/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.79/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.30  
% 1.79/1.31  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.79/1.31  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.79/1.31  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.79/1.31  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.79/1.31  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.79/1.31  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.79/1.31  tff(f_62, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.79/1.31  tff(c_12, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.79/1.31  tff(c_10, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.79/1.31  tff(c_179, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, k3_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.31  tff(c_182, plain, (![A_9, C_52]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_179])).
% 1.79/1.31  tff(c_184, plain, (![C_52]: (~r2_hidden(C_52, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_182])).
% 1.79/1.31  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.79/1.31  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.79/1.31  tff(c_121, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_14])).
% 1.79/1.31  tff(c_149, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.31  tff(c_152, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)=k2_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_121, c_149])).
% 1.79/1.31  tff(c_160, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_152])).
% 1.79/1.31  tff(c_20, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.79/1.31  tff(c_172, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_160, c_20])).
% 1.79/1.31  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_172])).
% 1.79/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.31  
% 1.79/1.31  Inference rules
% 1.79/1.31  ----------------------
% 1.79/1.31  #Ref     : 0
% 1.79/1.31  #Sup     : 35
% 1.79/1.31  #Fact    : 0
% 1.79/1.31  #Define  : 0
% 1.79/1.31  #Split   : 0
% 1.79/1.31  #Chain   : 0
% 1.79/1.31  #Close   : 0
% 1.79/1.31  
% 1.79/1.31  Ordering : KBO
% 1.79/1.31  
% 1.79/1.31  Simplification rules
% 1.79/1.31  ----------------------
% 1.79/1.31  #Subsume      : 0
% 1.79/1.31  #Demod        : 9
% 1.79/1.31  #Tautology    : 25
% 1.79/1.31  #SimpNegUnit  : 1
% 1.79/1.31  #BackRed      : 3
% 1.79/1.31  
% 1.79/1.31  #Partial instantiations: 0
% 1.79/1.31  #Strategies tried      : 1
% 1.79/1.31  
% 1.79/1.31  Timing (in seconds)
% 1.79/1.31  ----------------------
% 1.79/1.31  Preprocessing        : 0.31
% 1.79/1.31  Parsing              : 0.16
% 1.79/1.31  CNF conversion       : 0.02
% 1.79/1.31  Main loop            : 0.13
% 1.79/1.31  Inferencing          : 0.04
% 1.79/1.31  Reduction            : 0.05
% 1.79/1.31  Demodulation         : 0.04
% 1.79/1.31  BG Simplification    : 0.01
% 1.79/1.31  Subsumption          : 0.03
% 1.79/1.31  Abstraction          : 0.01
% 1.79/1.32  MUC search           : 0.00
% 1.79/1.32  Cooper               : 0.00
% 1.79/1.32  Total                : 0.47
% 1.79/1.32  Index Insertion      : 0.00
% 1.79/1.32  Index Deletion       : 0.00
% 1.79/1.32  Index Matching       : 0.00
% 1.79/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:09 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   45 (  46 expanded)
%              Number of leaves         :   30 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_66,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_147,plain,(
    ! [A_64,B_65] : k1_enumset1(A_64,A_64,B_65) = k2_tarski(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [E_20,B_15,C_16] : r2_hidden(E_20,k1_enumset1(E_20,B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_159,plain,(
    ! [A_64,B_65] : r2_hidden(A_64,k2_tarski(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_36])).

tff(c_28,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,(
    r1_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_114,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = k1_xboole_0
      | ~ r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_114])).

tff(c_169,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_181,plain,(
    k5_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) = k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_169])).

tff(c_191,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_181])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_259,plain,(
    ! [D_83] :
      ( ~ r2_hidden(D_83,'#skF_7')
      | ~ r2_hidden(D_83,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_6])).

tff(c_263,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_159,c_259])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:42 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.35  
% 2.18/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.36  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.18/1.36  
% 2.18/1.36  %Foreground sorts:
% 2.18/1.36  
% 2.18/1.36  
% 2.18/1.36  %Background operators:
% 2.18/1.36  
% 2.18/1.36  
% 2.18/1.36  %Foreground operators:
% 2.18/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.18/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.18/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.18/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.36  
% 2.18/1.37  tff(f_78, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.18/1.37  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.18/1.37  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.18/1.37  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.18/1.37  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.18/1.37  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.18/1.37  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.18/1.37  tff(c_66, plain, (r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.37  tff(c_147, plain, (![A_64, B_65]: (k1_enumset1(A_64, A_64, B_65)=k2_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.18/1.37  tff(c_36, plain, (![E_20, B_15, C_16]: (r2_hidden(E_20, k1_enumset1(E_20, B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.37  tff(c_159, plain, (![A_64, B_65]: (r2_hidden(A_64, k2_tarski(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_36])).
% 2.18/1.37  tff(c_28, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.37  tff(c_68, plain, (r1_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.37  tff(c_114, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=k1_xboole_0 | ~r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.37  tff(c_118, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_114])).
% 2.18/1.37  tff(c_169, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.37  tff(c_181, plain, (k5_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)=k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_118, c_169])).
% 2.18/1.37  tff(c_191, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_181])).
% 2.18/1.37  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.37  tff(c_259, plain, (![D_83]: (~r2_hidden(D_83, '#skF_7') | ~r2_hidden(D_83, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_191, c_6])).
% 2.18/1.37  tff(c_263, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_159, c_259])).
% 2.18/1.37  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_263])).
% 2.18/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.37  
% 2.18/1.37  Inference rules
% 2.18/1.37  ----------------------
% 2.18/1.37  #Ref     : 0
% 2.18/1.37  #Sup     : 51
% 2.18/1.37  #Fact    : 0
% 2.18/1.37  #Define  : 0
% 2.18/1.37  #Split   : 0
% 2.18/1.37  #Chain   : 0
% 2.18/1.37  #Close   : 0
% 2.18/1.37  
% 2.18/1.37  Ordering : KBO
% 2.18/1.37  
% 2.18/1.37  Simplification rules
% 2.18/1.37  ----------------------
% 2.18/1.37  #Subsume      : 0
% 2.18/1.37  #Demod        : 14
% 2.18/1.37  #Tautology    : 40
% 2.18/1.37  #SimpNegUnit  : 0
% 2.18/1.37  #BackRed      : 0
% 2.18/1.37  
% 2.18/1.37  #Partial instantiations: 0
% 2.18/1.37  #Strategies tried      : 1
% 2.18/1.37  
% 2.18/1.37  Timing (in seconds)
% 2.18/1.37  ----------------------
% 2.18/1.37  Preprocessing        : 0.36
% 2.18/1.37  Parsing              : 0.18
% 2.18/1.37  CNF conversion       : 0.03
% 2.18/1.37  Main loop            : 0.19
% 2.18/1.37  Inferencing          : 0.05
% 2.18/1.37  Reduction            : 0.07
% 2.18/1.37  Demodulation         : 0.06
% 2.37/1.37  BG Simplification    : 0.02
% 2.37/1.37  Subsumption          : 0.04
% 2.37/1.37  Abstraction          : 0.02
% 2.37/1.37  MUC search           : 0.00
% 2.37/1.37  Cooper               : 0.00
% 2.37/1.37  Total                : 0.58
% 2.37/1.37  Index Insertion      : 0.00
% 2.37/1.37  Index Deletion       : 0.00
% 2.37/1.37  Index Matching       : 0.00
% 2.37/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

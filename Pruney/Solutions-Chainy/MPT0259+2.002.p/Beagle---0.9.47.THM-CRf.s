%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:08 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),B)
          & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_54,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_83,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    ! [A_38,B_39] : r2_hidden(A_38,k2_tarski(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_28])).

tff(c_104,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_101])).

tff(c_56,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_69,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_69])).

tff(c_116,plain,(
    ! [D_46,B_47,A_48] :
      ( ~ r2_hidden(D_46,B_47)
      | ~ r2_hidden(D_46,k4_xboole_0(A_48,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [D_49] :
      ( ~ r2_hidden(D_49,'#skF_6')
      | ~ r2_hidden(D_49,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_116])).

tff(c_124,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_120])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.15  
% 1.71/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.15  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.71/1.15  
% 1.71/1.15  %Foreground sorts:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Background operators:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Foreground operators:
% 1.71/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.71/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.71/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.71/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.71/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.71/1.15  
% 1.71/1.16  tff(f_66, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 1.71/1.16  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.71/1.16  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.71/1.16  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.71/1.16  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.71/1.16  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.71/1.16  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.71/1.16  tff(c_48, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.71/1.16  tff(c_83, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.16  tff(c_28, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.71/1.16  tff(c_101, plain, (![A_38, B_39]: (r2_hidden(A_38, k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_28])).
% 1.71/1.16  tff(c_104, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_101])).
% 1.71/1.16  tff(c_56, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.71/1.16  tff(c_69, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.16  tff(c_73, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_56, c_69])).
% 1.71/1.16  tff(c_116, plain, (![D_46, B_47, A_48]: (~r2_hidden(D_46, B_47) | ~r2_hidden(D_46, k4_xboole_0(A_48, B_47)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.16  tff(c_120, plain, (![D_49]: (~r2_hidden(D_49, '#skF_6') | ~r2_hidden(D_49, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_73, c_116])).
% 1.71/1.16  tff(c_124, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_104, c_120])).
% 1.71/1.16  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_124])).
% 1.71/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  Inference rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Ref     : 0
% 1.71/1.16  #Sup     : 16
% 1.71/1.16  #Fact    : 0
% 1.71/1.16  #Define  : 0
% 1.71/1.16  #Split   : 0
% 1.71/1.16  #Chain   : 0
% 1.71/1.16  #Close   : 0
% 1.71/1.16  
% 1.71/1.16  Ordering : KBO
% 1.71/1.16  
% 1.71/1.16  Simplification rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Subsume      : 0
% 1.71/1.16  #Demod        : 3
% 1.71/1.16  #Tautology    : 10
% 1.71/1.16  #SimpNegUnit  : 0
% 1.71/1.16  #BackRed      : 0
% 1.71/1.16  
% 1.71/1.16  #Partial instantiations: 0
% 1.71/1.16  #Strategies tried      : 1
% 1.71/1.16  
% 1.71/1.16  Timing (in seconds)
% 1.71/1.16  ----------------------
% 1.71/1.16  Preprocessing        : 0.29
% 1.71/1.16  Parsing              : 0.14
% 1.71/1.16  CNF conversion       : 0.02
% 1.71/1.16  Main loop            : 0.12
% 1.71/1.16  Inferencing          : 0.03
% 1.71/1.16  Reduction            : 0.04
% 1.71/1.16  Demodulation         : 0.03
% 1.71/1.16  BG Simplification    : 0.02
% 1.71/1.16  Subsumption          : 0.03
% 1.71/1.16  Abstraction          : 0.01
% 1.71/1.16  MUC search           : 0.00
% 1.71/1.16  Cooper               : 0.00
% 1.71/1.16  Total                : 0.43
% 1.71/1.16  Index Insertion      : 0.00
% 1.71/1.16  Index Deletion       : 0.00
% 1.71/1.16  Index Matching       : 0.00
% 1.71/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

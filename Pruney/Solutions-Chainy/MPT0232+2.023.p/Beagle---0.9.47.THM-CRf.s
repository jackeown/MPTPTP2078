%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:22 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 141 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 ( 249 expanded)
%              Number of equality atoms :   28 ( 152 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_69,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [B_37,A_36] : r2_hidden(B_37,k2_tarski(A_36,B_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_24])).

tff(c_56,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_124,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_54,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_6])).

tff(c_133,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_124])).

tff(c_46,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    ! [E_62,C_63,B_64,A_65] :
      ( E_62 = C_63
      | E_62 = B_64
      | E_62 = A_65
      | ~ r2_hidden(E_62,k1_enumset1(A_65,B_64,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_175,plain,(
    ! [E_66,B_67,A_68] :
      ( E_66 = B_67
      | E_66 = A_68
      | E_66 = A_68
      | ~ r2_hidden(E_66,k2_tarski(A_68,B_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_156])).

tff(c_189,plain,(
    ! [E_69,A_70] :
      ( E_69 = A_70
      | E_69 = A_70
      | E_69 = A_70
      | ~ r2_hidden(E_69,k1_tarski(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_175])).

tff(c_200,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_133,c_189])).

tff(c_28,plain,(
    ! [E_15,B_10,C_11] : r2_hidden(E_15,k1_enumset1(E_15,B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,(
    ! [A_36,B_37] : r2_hidden(A_36,k2_tarski(A_36,B_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_28])).

tff(c_134,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_75,c_124])).

tff(c_199,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_134,c_189])).

tff(c_225,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_199])).

tff(c_54,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_208,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_54])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_46,c_225,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.36  
% 2.09/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.37  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.09/1.37  
% 2.09/1.37  %Foreground sorts:
% 2.09/1.37  
% 2.09/1.37  
% 2.09/1.37  %Background operators:
% 2.09/1.37  
% 2.09/1.37  
% 2.09/1.37  %Foreground operators:
% 2.09/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.09/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.09/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.09/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.37  
% 2.09/1.38  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.38  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.09/1.38  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.09/1.38  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.09/1.38  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.09/1.38  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.38  tff(c_69, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.38  tff(c_24, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.38  tff(c_78, plain, (![B_37, A_36]: (r2_hidden(B_37, k2_tarski(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_24])).
% 2.09/1.38  tff(c_56, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.38  tff(c_92, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.09/1.38  tff(c_96, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_56, c_92])).
% 2.09/1.38  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.09/1.38  tff(c_124, plain, (![D_54]: (~r2_hidden(D_54, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_54, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_6])).
% 2.09/1.38  tff(c_133, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_124])).
% 2.09/1.38  tff(c_46, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.38  tff(c_48, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.38  tff(c_156, plain, (![E_62, C_63, B_64, A_65]: (E_62=C_63 | E_62=B_64 | E_62=A_65 | ~r2_hidden(E_62, k1_enumset1(A_65, B_64, C_63)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.38  tff(c_175, plain, (![E_66, B_67, A_68]: (E_66=B_67 | E_66=A_68 | E_66=A_68 | ~r2_hidden(E_66, k2_tarski(A_68, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_156])).
% 2.09/1.38  tff(c_189, plain, (![E_69, A_70]: (E_69=A_70 | E_69=A_70 | E_69=A_70 | ~r2_hidden(E_69, k1_tarski(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_175])).
% 2.09/1.38  tff(c_200, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_133, c_189])).
% 2.09/1.38  tff(c_28, plain, (![E_15, B_10, C_11]: (r2_hidden(E_15, k1_enumset1(E_15, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.38  tff(c_75, plain, (![A_36, B_37]: (r2_hidden(A_36, k2_tarski(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_28])).
% 2.09/1.38  tff(c_134, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_75, c_124])).
% 2.09/1.38  tff(c_199, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_134, c_189])).
% 2.09/1.38  tff(c_225, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_199])).
% 2.09/1.38  tff(c_54, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.38  tff(c_208, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_54])).
% 2.09/1.38  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_46, c_225, c_208])).
% 2.09/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.38  
% 2.09/1.38  Inference rules
% 2.09/1.38  ----------------------
% 2.09/1.38  #Ref     : 0
% 2.09/1.38  #Sup     : 41
% 2.09/1.38  #Fact    : 0
% 2.09/1.38  #Define  : 0
% 2.09/1.38  #Split   : 0
% 2.09/1.38  #Chain   : 0
% 2.09/1.38  #Close   : 0
% 2.09/1.38  
% 2.09/1.38  Ordering : KBO
% 2.09/1.38  
% 2.09/1.38  Simplification rules
% 2.09/1.38  ----------------------
% 2.09/1.38  #Subsume      : 0
% 2.09/1.38  #Demod        : 16
% 2.09/1.38  #Tautology    : 30
% 2.09/1.38  #SimpNegUnit  : 0
% 2.09/1.38  #BackRed      : 7
% 2.09/1.38  
% 2.09/1.38  #Partial instantiations: 0
% 2.09/1.38  #Strategies tried      : 1
% 2.09/1.38  
% 2.09/1.38  Timing (in seconds)
% 2.09/1.38  ----------------------
% 2.09/1.38  Preprocessing        : 0.35
% 2.09/1.38  Parsing              : 0.17
% 2.09/1.38  CNF conversion       : 0.03
% 2.09/1.38  Main loop            : 0.18
% 2.09/1.38  Inferencing          : 0.06
% 2.09/1.38  Reduction            : 0.06
% 2.09/1.38  Demodulation         : 0.05
% 2.09/1.38  BG Simplification    : 0.02
% 2.09/1.38  Subsumption          : 0.04
% 2.09/1.38  Abstraction          : 0.01
% 2.09/1.38  MUC search           : 0.00
% 2.09/1.38  Cooper               : 0.00
% 2.09/1.38  Total                : 0.56
% 2.26/1.38  Index Insertion      : 0.00
% 2.26/1.38  Index Deletion       : 0.00
% 2.26/1.38  Index Matching       : 0.00
% 2.26/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

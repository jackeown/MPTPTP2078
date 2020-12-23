%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:52 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  57 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    ! [A_27,B_28] : k1_enumset1(A_27,A_27,B_28) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [B_29,A_30] : r2_hidden(B_29,k2_tarski(A_30,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4])).

tff(c_77,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_74])).

tff(c_156,plain,(
    ! [B_56,C_57,A_58] :
      ( ~ r2_hidden(B_56,C_57)
      | k4_xboole_0(k2_tarski(A_58,B_56),C_57) = k1_tarski(A_58)
      | r2_hidden(A_58,C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_168,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_40])).

tff(c_180,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_168])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_112,plain,(
    ! [E_44,C_45,B_46,A_47] :
      ( E_44 = C_45
      | E_44 = B_46
      | E_44 = A_47
      | ~ r2_hidden(E_44,k1_enumset1(A_47,B_46,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_131,plain,(
    ! [E_48,B_49,A_50] :
      ( E_48 = B_49
      | E_48 = A_50
      | E_48 = A_50
      | ~ r2_hidden(E_48,k2_tarski(A_50,B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_112])).

tff(c_140,plain,(
    ! [E_48,A_8] :
      ( E_48 = A_8
      | E_48 = A_8
      | E_48 = A_8
      | ~ r2_hidden(E_48,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_131])).

tff(c_184,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_180,c_140])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_42,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.24  
% 1.96/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.24  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.96/1.24  
% 1.96/1.24  %Foreground sorts:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Background operators:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Foreground operators:
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.96/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.96/1.24  
% 2.03/1.25  tff(f_61, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 2.03/1.25  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.03/1.25  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.25  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.03/1.25  tff(f_55, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.03/1.25  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.25  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.25  tff(c_56, plain, (![A_27, B_28]: (k1_enumset1(A_27, A_27, B_28)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.03/1.25  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.25  tff(c_74, plain, (![B_29, A_30]: (r2_hidden(B_29, k2_tarski(A_30, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4])).
% 2.03/1.25  tff(c_77, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_74])).
% 2.03/1.25  tff(c_156, plain, (![B_56, C_57, A_58]: (~r2_hidden(B_56, C_57) | k4_xboole_0(k2_tarski(A_58, B_56), C_57)=k1_tarski(A_58) | r2_hidden(A_58, C_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.25  tff(c_40, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.25  tff(c_168, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_40])).
% 2.03/1.25  tff(c_180, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_168])).
% 2.03/1.25  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.03/1.25  tff(c_112, plain, (![E_44, C_45, B_46, A_47]: (E_44=C_45 | E_44=B_46 | E_44=A_47 | ~r2_hidden(E_44, k1_enumset1(A_47, B_46, C_45)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.25  tff(c_131, plain, (![E_48, B_49, A_50]: (E_48=B_49 | E_48=A_50 | E_48=A_50 | ~r2_hidden(E_48, k2_tarski(A_50, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_112])).
% 2.03/1.25  tff(c_140, plain, (![E_48, A_8]: (E_48=A_8 | E_48=A_8 | E_48=A_8 | ~r2_hidden(E_48, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_131])).
% 2.03/1.25  tff(c_184, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_180, c_140])).
% 2.03/1.25  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_42, c_184])).
% 2.03/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  Inference rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Ref     : 0
% 2.03/1.25  #Sup     : 31
% 2.03/1.25  #Fact    : 0
% 2.03/1.25  #Define  : 0
% 2.03/1.25  #Split   : 0
% 2.03/1.25  #Chain   : 0
% 2.03/1.25  #Close   : 0
% 2.03/1.25  
% 2.03/1.25  Ordering : KBO
% 2.03/1.25  
% 2.03/1.25  Simplification rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Subsume      : 1
% 2.03/1.25  #Demod        : 4
% 2.03/1.25  #Tautology    : 22
% 2.03/1.25  #SimpNegUnit  : 1
% 2.03/1.25  #BackRed      : 0
% 2.03/1.25  
% 2.03/1.25  #Partial instantiations: 0
% 2.03/1.25  #Strategies tried      : 1
% 2.03/1.25  
% 2.03/1.25  Timing (in seconds)
% 2.03/1.25  ----------------------
% 2.03/1.25  Preprocessing        : 0.31
% 2.03/1.25  Parsing              : 0.15
% 2.03/1.25  CNF conversion       : 0.02
% 2.03/1.25  Main loop            : 0.16
% 2.03/1.25  Inferencing          : 0.06
% 2.03/1.25  Reduction            : 0.05
% 2.03/1.25  Demodulation         : 0.04
% 2.03/1.25  BG Simplification    : 0.01
% 2.03/1.25  Subsumption          : 0.03
% 2.03/1.25  Abstraction          : 0.01
% 2.03/1.25  MUC search           : 0.00
% 2.03/1.25  Cooper               : 0.00
% 2.03/1.25  Total                : 0.50
% 2.03/1.25  Index Insertion      : 0.00
% 2.03/1.25  Index Deletion       : 0.00
% 2.03/1.25  Index Matching       : 0.00
% 2.03/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

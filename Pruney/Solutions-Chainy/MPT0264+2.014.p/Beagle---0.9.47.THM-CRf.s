%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:22 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_52,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_102,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_111,plain,(
    ! [B_35,A_34] : r2_hidden(B_35,k2_tarski(A_34,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_24])).

tff(c_56,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_196,plain,(
    ! [D_52,A_53,B_54] :
      ( r2_hidden(D_52,k3_xboole_0(A_53,B_54))
      | ~ r2_hidden(D_52,B_54)
      | ~ r2_hidden(D_52,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_254,plain,(
    ! [D_62] :
      ( r2_hidden(D_62,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_62,'#skF_7')
      | ~ r2_hidden(D_62,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_196])).

tff(c_261,plain,
    ( r2_hidden('#skF_6',k1_tarski('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_111,c_254])).

tff(c_269,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_261])).

tff(c_46,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_217,plain,(
    ! [E_55,C_56,B_57,A_58] :
      ( E_55 = C_56
      | E_55 = B_57
      | E_55 = A_58
      | ~ r2_hidden(E_55,k1_enumset1(A_58,B_57,C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_236,plain,(
    ! [E_59,B_60,A_61] :
      ( E_59 = B_60
      | E_59 = A_61
      | E_59 = A_61
      | ~ r2_hidden(E_59,k2_tarski(A_61,B_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_217])).

tff(c_294,plain,(
    ! [E_64,A_65] :
      ( E_64 = A_65
      | E_64 = A_65
      | E_64 = A_65
      | ~ r2_hidden(E_64,k1_tarski(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_236])).

tff(c_297,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_269,c_294])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_52,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:35:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.15/1.25  
% 2.15/1.25  %Foreground sorts:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Background operators:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Foreground operators:
% 2.15/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.15/1.25  
% 2.15/1.26  tff(f_66, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.15/1.26  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.15/1.26  tff(f_51, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.15/1.26  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.15/1.26  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.26  tff(c_52, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.26  tff(c_54, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.26  tff(c_102, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.15/1.26  tff(c_24, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.26  tff(c_111, plain, (![B_35, A_34]: (r2_hidden(B_35, k2_tarski(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_24])).
% 2.15/1.26  tff(c_56, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.26  tff(c_196, plain, (![D_52, A_53, B_54]: (r2_hidden(D_52, k3_xboole_0(A_53, B_54)) | ~r2_hidden(D_52, B_54) | ~r2_hidden(D_52, A_53))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.15/1.26  tff(c_254, plain, (![D_62]: (r2_hidden(D_62, k1_tarski('#skF_5')) | ~r2_hidden(D_62, '#skF_7') | ~r2_hidden(D_62, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_56, c_196])).
% 2.15/1.26  tff(c_261, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_111, c_254])).
% 2.15/1.26  tff(c_269, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_261])).
% 2.15/1.26  tff(c_46, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.26  tff(c_48, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.15/1.26  tff(c_217, plain, (![E_55, C_56, B_57, A_58]: (E_55=C_56 | E_55=B_57 | E_55=A_58 | ~r2_hidden(E_55, k1_enumset1(A_58, B_57, C_56)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.26  tff(c_236, plain, (![E_59, B_60, A_61]: (E_59=B_60 | E_59=A_61 | E_59=A_61 | ~r2_hidden(E_59, k2_tarski(A_61, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_217])).
% 2.15/1.26  tff(c_294, plain, (![E_64, A_65]: (E_64=A_65 | E_64=A_65 | E_64=A_65 | ~r2_hidden(E_64, k1_tarski(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_236])).
% 2.15/1.26  tff(c_297, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_269, c_294])).
% 2.15/1.26  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_52, c_297])).
% 2.15/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  Inference rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Ref     : 0
% 2.15/1.26  #Sup     : 58
% 2.15/1.26  #Fact    : 0
% 2.15/1.26  #Define  : 0
% 2.15/1.26  #Split   : 0
% 2.15/1.26  #Chain   : 0
% 2.15/1.26  #Close   : 0
% 2.15/1.26  
% 2.15/1.26  Ordering : KBO
% 2.15/1.26  
% 2.15/1.26  Simplification rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Subsume      : 8
% 2.15/1.26  #Demod        : 9
% 2.15/1.26  #Tautology    : 35
% 2.15/1.26  #SimpNegUnit  : 3
% 2.15/1.26  #BackRed      : 0
% 2.15/1.26  
% 2.15/1.26  #Partial instantiations: 0
% 2.15/1.26  #Strategies tried      : 1
% 2.15/1.26  
% 2.15/1.26  Timing (in seconds)
% 2.15/1.26  ----------------------
% 2.15/1.26  Preprocessing        : 0.29
% 2.15/1.26  Parsing              : 0.14
% 2.15/1.26  CNF conversion       : 0.02
% 2.15/1.26  Main loop            : 0.20
% 2.15/1.26  Inferencing          : 0.06
% 2.15/1.26  Reduction            : 0.07
% 2.15/1.26  Demodulation         : 0.06
% 2.15/1.26  BG Simplification    : 0.02
% 2.15/1.26  Subsumption          : 0.04
% 2.15/1.26  Abstraction          : 0.01
% 2.15/1.26  MUC search           : 0.00
% 2.15/1.26  Cooper               : 0.00
% 2.15/1.26  Total                : 0.52
% 2.15/1.26  Index Insertion      : 0.00
% 2.15/1.27  Index Deletion       : 0.00
% 2.15/1.27  Index Matching       : 0.00
% 2.15/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

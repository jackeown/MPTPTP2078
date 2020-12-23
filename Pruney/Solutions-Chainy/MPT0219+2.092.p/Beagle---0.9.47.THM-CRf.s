%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:01 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   33 (  38 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_48,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ! [A_22,B_23,C_24] : k2_enumset1(A_22,A_22,B_23,C_24) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_379,plain,(
    ! [A_656,B_657,C_658,D_659] : k2_xboole_0(k1_enumset1(A_656,B_657,C_658),k1_tarski(D_659)) = k2_enumset1(A_656,B_657,C_658,D_659) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_423,plain,(
    ! [A_20,B_21,D_659] : k2_xboole_0(k2_tarski(A_20,B_21),k1_tarski(D_659)) = k2_enumset1(A_20,A_20,B_21,D_659) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_379])).

tff(c_427,plain,(
    ! [A_688,B_689,D_690] : k2_xboole_0(k2_tarski(A_688,B_689),k1_tarski(D_690)) = k1_enumset1(A_688,B_689,D_690) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_423])).

tff(c_471,plain,(
    ! [A_19,D_690] : k2_xboole_0(k1_tarski(A_19),k1_tarski(D_690)) = k1_enumset1(A_19,A_19,D_690) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_427])).

tff(c_475,plain,(
    ! [A_719,D_720] : k2_xboole_0(k1_tarski(A_719),k1_tarski(D_720)) = k2_tarski(A_719,D_720) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_471])).

tff(c_50,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_481,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_50])).

tff(c_74,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_80,plain,(
    ! [B_39,A_38] : r2_hidden(B_39,k2_tarski(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_6])).

tff(c_566,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_80])).

tff(c_28,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_613,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_566,c_28])).

tff(c_644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:43:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.29  
% 2.24/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.29  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.24/1.29  
% 2.24/1.29  %Foreground sorts:
% 2.24/1.29  
% 2.24/1.29  
% 2.24/1.29  %Background operators:
% 2.24/1.29  
% 2.24/1.29  
% 2.24/1.29  %Foreground operators:
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.24/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.24/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.24/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.24/1.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.24/1.29  
% 2.24/1.30  tff(f_62, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.24/1.30  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/1.30  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.24/1.30  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.24/1.30  tff(f_51, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.24/1.30  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.24/1.30  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.24/1.30  tff(c_48, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.24/1.30  tff(c_44, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.30  tff(c_42, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.30  tff(c_46, plain, (![A_22, B_23, C_24]: (k2_enumset1(A_22, A_22, B_23, C_24)=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.24/1.30  tff(c_379, plain, (![A_656, B_657, C_658, D_659]: (k2_xboole_0(k1_enumset1(A_656, B_657, C_658), k1_tarski(D_659))=k2_enumset1(A_656, B_657, C_658, D_659))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.30  tff(c_423, plain, (![A_20, B_21, D_659]: (k2_xboole_0(k2_tarski(A_20, B_21), k1_tarski(D_659))=k2_enumset1(A_20, A_20, B_21, D_659))), inference(superposition, [status(thm), theory('equality')], [c_44, c_379])).
% 2.24/1.30  tff(c_427, plain, (![A_688, B_689, D_690]: (k2_xboole_0(k2_tarski(A_688, B_689), k1_tarski(D_690))=k1_enumset1(A_688, B_689, D_690))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_423])).
% 2.24/1.30  tff(c_471, plain, (![A_19, D_690]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(D_690))=k1_enumset1(A_19, A_19, D_690))), inference(superposition, [status(thm), theory('equality')], [c_42, c_427])).
% 2.24/1.30  tff(c_475, plain, (![A_719, D_720]: (k2_xboole_0(k1_tarski(A_719), k1_tarski(D_720))=k2_tarski(A_719, D_720))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_471])).
% 2.24/1.30  tff(c_50, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.24/1.30  tff(c_481, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_475, c_50])).
% 2.24/1.30  tff(c_74, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.30  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.30  tff(c_80, plain, (![B_39, A_38]: (r2_hidden(B_39, k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_6])).
% 2.24/1.30  tff(c_566, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_481, c_80])).
% 2.24/1.30  tff(c_28, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.30  tff(c_613, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_566, c_28])).
% 2.24/1.30  tff(c_644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_613])).
% 2.24/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  Inference rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Ref     : 0
% 2.24/1.30  #Sup     : 64
% 2.24/1.30  #Fact    : 0
% 2.24/1.30  #Define  : 0
% 2.24/1.30  #Split   : 1
% 2.24/1.30  #Chain   : 0
% 2.24/1.30  #Close   : 0
% 2.24/1.30  
% 2.24/1.30  Ordering : KBO
% 2.24/1.30  
% 2.24/1.30  Simplification rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Subsume      : 0
% 2.24/1.30  #Demod        : 7
% 2.24/1.30  #Tautology    : 28
% 2.24/1.30  #SimpNegUnit  : 1
% 2.24/1.30  #BackRed      : 0
% 2.24/1.30  
% 2.24/1.30  #Partial instantiations: 338
% 2.24/1.30  #Strategies tried      : 1
% 2.24/1.30  
% 2.24/1.30  Timing (in seconds)
% 2.24/1.30  ----------------------
% 2.24/1.30  Preprocessing        : 0.30
% 2.24/1.31  Parsing              : 0.15
% 2.24/1.31  CNF conversion       : 0.02
% 2.24/1.31  Main loop            : 0.25
% 2.24/1.31  Inferencing          : 0.13
% 2.24/1.31  Reduction            : 0.06
% 2.24/1.31  Demodulation         : 0.04
% 2.24/1.31  BG Simplification    : 0.02
% 2.24/1.31  Subsumption          : 0.04
% 2.24/1.31  Abstraction          : 0.01
% 2.24/1.31  MUC search           : 0.00
% 2.24/1.31  Cooper               : 0.00
% 2.24/1.31  Total                : 0.58
% 2.24/1.31  Index Insertion      : 0.00
% 2.24/1.31  Index Deletion       : 0.00
% 2.24/1.31  Index Matching       : 0.00
% 2.24/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

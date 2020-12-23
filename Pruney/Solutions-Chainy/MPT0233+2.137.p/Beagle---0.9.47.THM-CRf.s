%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:38 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_52,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    ! [A_30,B_31] : r2_hidden(A_30,k2_tarski(A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_26])).

tff(c_54,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_78,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_78])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,k2_tarski('#skF_7','#skF_8'))
      | ~ r2_hidden(D_6,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_4])).

tff(c_46,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_118,plain,(
    ! [E_51,C_52,B_53,A_54] :
      ( E_51 = C_52
      | E_51 = B_53
      | E_51 = A_54
      | ~ r2_hidden(E_51,k1_enumset1(A_54,B_53,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [E_55,B_56,A_57] :
      ( E_55 = B_56
      | E_55 = A_57
      | E_55 = A_57
      | ~ r2_hidden(E_55,k2_tarski(A_57,B_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_118])).

tff(c_152,plain,(
    ! [D_58] :
      ( D_58 = '#skF_8'
      | D_58 = '#skF_7'
      | ~ r2_hidden(D_58,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_101,c_137])).

tff(c_160,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:55:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.27  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.03/1.27  
% 2.03/1.27  %Foreground sorts:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Background operators:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Foreground operators:
% 2.03/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.03/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.03/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.03/1.27  
% 2.03/1.28  tff(f_67, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.03/1.28  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.28  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.03/1.28  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.03/1.28  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.03/1.28  tff(c_52, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.28  tff(c_50, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.28  tff(c_58, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.28  tff(c_26, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.03/1.28  tff(c_64, plain, (![A_30, B_31]: (r2_hidden(A_30, k2_tarski(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_26])).
% 2.03/1.28  tff(c_54, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.28  tff(c_78, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.03/1.28  tff(c_82, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_78])).
% 2.03/1.28  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.28  tff(c_101, plain, (![D_6]: (r2_hidden(D_6, k2_tarski('#skF_7', '#skF_8')) | ~r2_hidden(D_6, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_82, c_4])).
% 2.03/1.28  tff(c_46, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.28  tff(c_118, plain, (![E_51, C_52, B_53, A_54]: (E_51=C_52 | E_51=B_53 | E_51=A_54 | ~r2_hidden(E_51, k1_enumset1(A_54, B_53, C_52)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.03/1.28  tff(c_137, plain, (![E_55, B_56, A_57]: (E_55=B_56 | E_55=A_57 | E_55=A_57 | ~r2_hidden(E_55, k2_tarski(A_57, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_118])).
% 2.03/1.28  tff(c_152, plain, (![D_58]: (D_58='#skF_8' | D_58='#skF_7' | ~r2_hidden(D_58, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_101, c_137])).
% 2.03/1.28  tff(c_160, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_64, c_152])).
% 2.03/1.28  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_160])).
% 2.03/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.28  
% 2.03/1.28  Inference rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Ref     : 0
% 2.03/1.28  #Sup     : 24
% 2.03/1.28  #Fact    : 0
% 2.03/1.28  #Define  : 0
% 2.03/1.28  #Split   : 0
% 2.03/1.28  #Chain   : 0
% 2.03/1.28  #Close   : 0
% 2.03/1.28  
% 2.03/1.28  Ordering : KBO
% 2.03/1.28  
% 2.03/1.28  Simplification rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Subsume      : 0
% 2.03/1.28  #Demod        : 1
% 2.03/1.28  #Tautology    : 16
% 2.03/1.28  #SimpNegUnit  : 1
% 2.03/1.28  #BackRed      : 0
% 2.03/1.28  
% 2.03/1.28  #Partial instantiations: 0
% 2.03/1.28  #Strategies tried      : 1
% 2.03/1.28  
% 2.03/1.28  Timing (in seconds)
% 2.03/1.28  ----------------------
% 2.03/1.29  Preprocessing        : 0.32
% 2.03/1.29  Parsing              : 0.16
% 2.03/1.29  CNF conversion       : 0.02
% 2.03/1.29  Main loop            : 0.14
% 2.03/1.29  Inferencing          : 0.04
% 2.03/1.29  Reduction            : 0.05
% 2.03/1.29  Demodulation         : 0.03
% 2.03/1.29  BG Simplification    : 0.02
% 2.03/1.29  Subsumption          : 0.03
% 2.03/1.29  Abstraction          : 0.01
% 2.03/1.29  MUC search           : 0.00
% 2.03/1.29  Cooper               : 0.00
% 2.03/1.29  Total                : 0.48
% 2.03/1.29  Index Insertion      : 0.00
% 2.03/1.29  Index Deletion       : 0.00
% 2.03/1.29  Index Matching       : 0.00
% 2.03/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

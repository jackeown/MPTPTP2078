%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:38 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  52 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_38,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    '#skF_7' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_27,B_28] : k1_enumset1(A_27,A_27,B_28) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    ! [A_27,B_28] : r2_hidden(A_27,k2_tarski(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_82,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,(
    ! [A_51,B_52,B_53] :
      ( r2_hidden(A_51,B_52)
      | ~ r1_tarski(k2_tarski(A_51,B_53),B_52) ) ),
    inference(resolution,[status(thm)],[c_50,c_82])).

tff(c_149,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_139])).

tff(c_32,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [E_44,C_45,B_46,A_47] :
      ( E_44 = C_45
      | E_44 = B_46
      | E_44 = A_47
      | ~ r2_hidden(E_44,k1_enumset1(A_47,B_46,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_198,plain,(
    ! [E_72,B_73,A_74] :
      ( E_72 = B_73
      | E_72 = A_74
      | E_72 = A_74
      | ~ r2_hidden(E_72,k2_tarski(A_74,B_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_101])).

tff(c_201,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_149,c_198])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_36,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.23  
% 1.84/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.23  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.03/1.23  
% 2.03/1.23  %Foreground sorts:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Background operators:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Foreground operators:
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.23  tff('#skF_7', type, '#skF_7': $i).
% 2.03/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.03/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.03/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.23  
% 2.03/1.24  tff(f_61, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.03/1.24  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.24  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.03/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.03/1.24  tff(c_38, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.24  tff(c_36, plain, ('#skF_7'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.24  tff(c_40, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.24  tff(c_44, plain, (![A_27, B_28]: (k1_enumset1(A_27, A_27, B_28)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.24  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.24  tff(c_50, plain, (![A_27, B_28]: (r2_hidden(A_27, k2_tarski(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_12])).
% 2.03/1.24  tff(c_82, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.24  tff(c_139, plain, (![A_51, B_52, B_53]: (r2_hidden(A_51, B_52) | ~r1_tarski(k2_tarski(A_51, B_53), B_52))), inference(resolution, [status(thm)], [c_50, c_82])).
% 2.03/1.24  tff(c_149, plain, (r2_hidden('#skF_4', k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_40, c_139])).
% 2.03/1.24  tff(c_32, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.24  tff(c_101, plain, (![E_44, C_45, B_46, A_47]: (E_44=C_45 | E_44=B_46 | E_44=A_47 | ~r2_hidden(E_44, k1_enumset1(A_47, B_46, C_45)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.24  tff(c_198, plain, (![E_72, B_73, A_74]: (E_72=B_73 | E_72=A_74 | E_72=A_74 | ~r2_hidden(E_72, k2_tarski(A_74, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_101])).
% 2.03/1.24  tff(c_201, plain, ('#skF_7'='#skF_4' | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_149, c_198])).
% 2.03/1.24  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_36, c_201])).
% 2.03/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.24  
% 2.03/1.24  Inference rules
% 2.03/1.24  ----------------------
% 2.03/1.24  #Ref     : 0
% 2.03/1.24  #Sup     : 38
% 2.03/1.24  #Fact    : 0
% 2.03/1.24  #Define  : 0
% 2.03/1.24  #Split   : 0
% 2.03/1.24  #Chain   : 0
% 2.03/1.24  #Close   : 0
% 2.03/1.24  
% 2.03/1.24  Ordering : KBO
% 2.03/1.24  
% 2.03/1.24  Simplification rules
% 2.03/1.24  ----------------------
% 2.03/1.24  #Subsume      : 3
% 2.03/1.24  #Demod        : 8
% 2.03/1.24  #Tautology    : 15
% 2.03/1.24  #SimpNegUnit  : 1
% 2.03/1.24  #BackRed      : 0
% 2.03/1.24  
% 2.03/1.24  #Partial instantiations: 0
% 2.03/1.24  #Strategies tried      : 1
% 2.03/1.24  
% 2.03/1.24  Timing (in seconds)
% 2.03/1.24  ----------------------
% 2.03/1.24  Preprocessing        : 0.30
% 2.03/1.24  Parsing              : 0.15
% 2.03/1.24  CNF conversion       : 0.02
% 2.03/1.24  Main loop            : 0.18
% 2.03/1.24  Inferencing          : 0.06
% 2.03/1.24  Reduction            : 0.05
% 2.03/1.24  Demodulation         : 0.04
% 2.03/1.24  BG Simplification    : 0.02
% 2.03/1.25  Subsumption          : 0.04
% 2.03/1.25  Abstraction          : 0.01
% 2.03/1.25  MUC search           : 0.00
% 2.03/1.25  Cooper               : 0.00
% 2.03/1.25  Total                : 0.50
% 2.03/1.25  Index Insertion      : 0.00
% 2.03/1.25  Index Deletion       : 0.00
% 2.03/1.25  Index Matching       : 0.00
% 2.03/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

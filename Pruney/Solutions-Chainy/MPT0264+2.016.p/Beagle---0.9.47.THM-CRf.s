%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:23 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   44 (  53 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  77 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_56,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_122,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,(
    ! [B_39,A_38] : r2_hidden(B_39,k2_tarski(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_28])).

tff(c_60,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_156,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_168,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_5')) = k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_156])).

tff(c_440,plain,(
    ! [D_71,A_72,B_73] :
      ( r2_hidden(D_71,k4_xboole_0(A_72,B_73))
      | r2_hidden(D_71,B_73)
      | ~ r2_hidden(D_71,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1959,plain,(
    ! [D_122] :
      ( r2_hidden(D_122,k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'))
      | r2_hidden(D_122,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_122,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_440])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2526,plain,(
    ! [D_150] :
      ( ~ r2_hidden(D_150,'#skF_7')
      | r2_hidden(D_150,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_150,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1959,c_6])).

tff(c_2549,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_131,c_2526])).

tff(c_2561,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2549])).

tff(c_50,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_625,plain,(
    ! [E_77,C_78,B_79,A_80] :
      ( E_77 = C_78
      | E_77 = B_79
      | E_77 = A_80
      | ~ r2_hidden(E_77,k1_enumset1(A_80,B_79,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2023,plain,(
    ! [E_127,B_128,A_129] :
      ( E_127 = B_128
      | E_127 = A_129
      | E_127 = A_129
      | ~ r2_hidden(E_127,k2_tarski(A_129,B_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_625])).

tff(c_2051,plain,(
    ! [E_127,A_20] :
      ( E_127 = A_20
      | E_127 = A_20
      | E_127 = A_20
      | ~ r2_hidden(E_127,k1_tarski(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2023])).

tff(c_2567,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2561,c_2051])).

tff(c_2577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_2567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:33:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.79  
% 4.51/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.79  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 4.51/1.79  
% 4.51/1.79  %Foreground sorts:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Background operators:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Foreground operators:
% 4.51/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.51/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.51/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.51/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.51/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.51/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.51/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.51/1.79  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.51/1.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.51/1.79  
% 4.64/1.81  tff(f_71, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 4.64/1.81  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.64/1.81  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.64/1.81  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.64/1.81  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.64/1.81  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.64/1.81  tff(c_56, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.64/1.81  tff(c_58, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.64/1.81  tff(c_122, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.64/1.81  tff(c_28, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.64/1.81  tff(c_131, plain, (![B_39, A_38]: (r2_hidden(B_39, k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_28])).
% 4.64/1.81  tff(c_60, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.64/1.81  tff(c_156, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.64/1.81  tff(c_168, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_5'))=k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_60, c_156])).
% 4.64/1.81  tff(c_440, plain, (![D_71, A_72, B_73]: (r2_hidden(D_71, k4_xboole_0(A_72, B_73)) | r2_hidden(D_71, B_73) | ~r2_hidden(D_71, A_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.64/1.81  tff(c_1959, plain, (![D_122]: (r2_hidden(D_122, k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')) | r2_hidden(D_122, k1_tarski('#skF_5')) | ~r2_hidden(D_122, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_168, c_440])).
% 4.64/1.81  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.64/1.81  tff(c_2526, plain, (![D_150]: (~r2_hidden(D_150, '#skF_7') | r2_hidden(D_150, k1_tarski('#skF_5')) | ~r2_hidden(D_150, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1959, c_6])).
% 4.64/1.81  tff(c_2549, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_131, c_2526])).
% 4.64/1.81  tff(c_2561, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2549])).
% 4.64/1.81  tff(c_50, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.64/1.81  tff(c_52, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.64/1.81  tff(c_625, plain, (![E_77, C_78, B_79, A_80]: (E_77=C_78 | E_77=B_79 | E_77=A_80 | ~r2_hidden(E_77, k1_enumset1(A_80, B_79, C_78)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.64/1.81  tff(c_2023, plain, (![E_127, B_128, A_129]: (E_127=B_128 | E_127=A_129 | E_127=A_129 | ~r2_hidden(E_127, k2_tarski(A_129, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_625])).
% 4.64/1.81  tff(c_2051, plain, (![E_127, A_20]: (E_127=A_20 | E_127=A_20 | E_127=A_20 | ~r2_hidden(E_127, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2023])).
% 4.64/1.81  tff(c_2567, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2561, c_2051])).
% 4.64/1.81  tff(c_2577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_2567])).
% 4.64/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.81  
% 4.64/1.81  Inference rules
% 4.64/1.81  ----------------------
% 4.64/1.81  #Ref     : 0
% 4.64/1.81  #Sup     : 619
% 4.64/1.81  #Fact    : 0
% 4.64/1.81  #Define  : 0
% 4.64/1.81  #Split   : 0
% 4.64/1.81  #Chain   : 0
% 4.64/1.81  #Close   : 0
% 4.64/1.81  
% 4.64/1.81  Ordering : KBO
% 4.64/1.81  
% 4.64/1.81  Simplification rules
% 4.64/1.81  ----------------------
% 4.64/1.81  #Subsume      : 77
% 4.64/1.81  #Demod        : 759
% 4.64/1.81  #Tautology    : 376
% 4.64/1.81  #SimpNegUnit  : 2
% 4.64/1.81  #BackRed      : 0
% 4.64/1.81  
% 4.64/1.81  #Partial instantiations: 0
% 4.64/1.81  #Strategies tried      : 1
% 4.64/1.81  
% 4.64/1.81  Timing (in seconds)
% 4.64/1.81  ----------------------
% 4.64/1.82  Preprocessing        : 0.32
% 4.64/1.82  Parsing              : 0.15
% 4.64/1.82  CNF conversion       : 0.03
% 4.64/1.82  Main loop            : 0.73
% 4.64/1.82  Inferencing          : 0.21
% 4.64/1.82  Reduction            : 0.35
% 4.64/1.82  Demodulation         : 0.29
% 4.64/1.82  BG Simplification    : 0.03
% 4.64/1.82  Subsumption          : 0.11
% 4.64/1.82  Abstraction          : 0.04
% 4.64/1.82  MUC search           : 0.00
% 4.64/1.82  Cooper               : 0.00
% 4.64/1.82  Total                : 1.09
% 4.64/1.82  Index Insertion      : 0.00
% 4.64/1.82  Index Deletion       : 0.00
% 4.64/1.82  Index Matching       : 0.00
% 4.64/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

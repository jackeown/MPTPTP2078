%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:56 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_55,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_44,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ! [B_31,A_32] : r2_hidden(B_31,k2_tarski(A_32,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_22])).

tff(c_93,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_90])).

tff(c_48,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_tarski(A_17)) = k1_ordinal1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_110,plain,(
    ! [D_41,B_42,A_43] :
      ( ~ r2_hidden(D_41,B_42)
      | r2_hidden(D_41,k2_xboole_0(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_126,plain,(
    ! [D_47,A_48] :
      ( ~ r2_hidden(D_47,k1_tarski(A_48))
      | r2_hidden(D_47,k1_ordinal1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_110])).

tff(c_130,plain,(
    ! [A_14] : r2_hidden(A_14,k1_ordinal1(A_14)) ),
    inference(resolution,[status(thm)],[c_93,c_126])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  %$ r2_hidden > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.93/1.21  
% 1.93/1.21  %Foreground sorts:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Background operators:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Foreground operators:
% 1.93/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.21  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.93/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.21  
% 1.93/1.22  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.22  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.93/1.22  tff(f_49, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.93/1.22  tff(f_55, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.93/1.22  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.93/1.22  tff(f_58, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.93/1.22  tff(c_44, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.93/1.22  tff(c_72, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.22  tff(c_22, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.22  tff(c_90, plain, (![B_31, A_32]: (r2_hidden(B_31, k2_tarski(A_32, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_22])).
% 1.93/1.22  tff(c_93, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_90])).
% 1.93/1.22  tff(c_48, plain, (![A_17]: (k2_xboole_0(A_17, k1_tarski(A_17))=k1_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.22  tff(c_110, plain, (![D_41, B_42, A_43]: (~r2_hidden(D_41, B_42) | r2_hidden(D_41, k2_xboole_0(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.22  tff(c_126, plain, (![D_47, A_48]: (~r2_hidden(D_47, k1_tarski(A_48)) | r2_hidden(D_47, k1_ordinal1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_110])).
% 1.93/1.22  tff(c_130, plain, (![A_14]: (r2_hidden(A_14, k1_ordinal1(A_14)))), inference(resolution, [status(thm)], [c_93, c_126])).
% 1.93/1.22  tff(c_50, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.22  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_50])).
% 1.93/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  Inference rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Ref     : 0
% 1.93/1.22  #Sup     : 18
% 1.93/1.22  #Fact    : 0
% 1.93/1.22  #Define  : 0
% 1.93/1.22  #Split   : 0
% 1.93/1.22  #Chain   : 0
% 1.93/1.22  #Close   : 0
% 1.93/1.22  
% 1.93/1.22  Ordering : KBO
% 1.93/1.22  
% 1.93/1.22  Simplification rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Subsume      : 0
% 1.93/1.22  #Demod        : 3
% 1.93/1.22  #Tautology    : 10
% 1.93/1.22  #SimpNegUnit  : 0
% 1.93/1.22  #BackRed      : 1
% 1.93/1.22  
% 1.93/1.22  #Partial instantiations: 0
% 1.93/1.22  #Strategies tried      : 1
% 1.93/1.22  
% 1.93/1.22  Timing (in seconds)
% 1.93/1.22  ----------------------
% 1.93/1.22  Preprocessing        : 0.31
% 1.93/1.22  Parsing              : 0.15
% 1.93/1.22  CNF conversion       : 0.02
% 1.93/1.22  Main loop            : 0.14
% 1.93/1.22  Inferencing          : 0.04
% 1.93/1.22  Reduction            : 0.05
% 1.93/1.22  Demodulation         : 0.04
% 1.93/1.22  BG Simplification    : 0.01
% 1.93/1.22  Subsumption          : 0.03
% 1.93/1.22  Abstraction          : 0.01
% 1.93/1.22  MUC search           : 0.00
% 1.93/1.22  Cooper               : 0.00
% 1.93/1.22  Total                : 0.48
% 1.93/1.22  Index Insertion      : 0.00
% 1.93/1.22  Index Deletion       : 0.00
% 1.93/1.22  Index Matching       : 0.00
% 1.93/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

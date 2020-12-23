%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:47 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  28 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_30,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_57,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | k4_xboole_0(k1_tarski(A_19),B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_61,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_57])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    ! [D_24,B_25,A_26] :
      ( D_24 = B_25
      | D_24 = A_26
      | ~ r2_hidden(D_24,k2_tarski(A_26,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [D_27,A_28] :
      ( D_27 = A_28
      | D_27 = A_28
      | ~ r2_hidden(D_27,k1_tarski(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_111,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_61,c_108])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:42:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  %$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.63/1.12  
% 1.63/1.12  %Foreground sorts:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Background operators:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Foreground operators:
% 1.63/1.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.12  
% 1.73/1.12  tff(f_50, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.73/1.12  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.73/1.12  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.73/1.12  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.73/1.12  tff(c_30, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.12  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.12  tff(c_57, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | k4_xboole_0(k1_tarski(A_19), B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.73/1.12  tff(c_61, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_57])).
% 1.73/1.12  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.73/1.12  tff(c_94, plain, (![D_24, B_25, A_26]: (D_24=B_25 | D_24=A_26 | ~r2_hidden(D_24, k2_tarski(A_26, B_25)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.73/1.12  tff(c_108, plain, (![D_27, A_28]: (D_27=A_28 | D_27=A_28 | ~r2_hidden(D_27, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 1.73/1.12  tff(c_111, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_61, c_108])).
% 1.73/1.12  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_111])).
% 1.73/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.12  
% 1.73/1.12  Inference rules
% 1.73/1.12  ----------------------
% 1.73/1.12  #Ref     : 0
% 1.73/1.12  #Sup     : 18
% 1.73/1.12  #Fact    : 0
% 1.73/1.12  #Define  : 0
% 1.73/1.12  #Split   : 0
% 1.73/1.12  #Chain   : 0
% 1.73/1.12  #Close   : 0
% 1.73/1.12  
% 1.73/1.12  Ordering : KBO
% 1.73/1.12  
% 1.73/1.12  Simplification rules
% 1.73/1.12  ----------------------
% 1.73/1.12  #Subsume      : 0
% 1.73/1.12  #Demod        : 4
% 1.73/1.12  #Tautology    : 12
% 1.73/1.12  #SimpNegUnit  : 1
% 1.73/1.12  #BackRed      : 0
% 1.73/1.12  
% 1.73/1.12  #Partial instantiations: 0
% 1.73/1.12  #Strategies tried      : 1
% 1.73/1.12  
% 1.73/1.12  Timing (in seconds)
% 1.73/1.12  ----------------------
% 1.73/1.13  Preprocessing        : 0.28
% 1.73/1.13  Parsing              : 0.14
% 1.73/1.13  CNF conversion       : 0.02
% 1.73/1.13  Main loop            : 0.10
% 1.73/1.13  Inferencing          : 0.03
% 1.73/1.13  Reduction            : 0.03
% 1.73/1.13  Demodulation         : 0.02
% 1.73/1.13  BG Simplification    : 0.01
% 1.73/1.13  Subsumption          : 0.02
% 1.73/1.13  Abstraction          : 0.01
% 1.73/1.13  MUC search           : 0.00
% 1.73/1.13  Cooper               : 0.00
% 1.73/1.13  Total                : 0.41
% 1.73/1.13  Index Insertion      : 0.00
% 1.73/1.13  Index Deletion       : 0.00
% 1.73/1.13  Index Matching       : 0.00
% 1.73/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

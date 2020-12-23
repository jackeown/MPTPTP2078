%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:51 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    3
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(k1_tarski(A_22),B_23) = k1_xboole_0
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_3',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_28])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.23  
% 1.80/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.23  %$ r2_hidden > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.80/1.23  
% 1.80/1.23  %Foreground sorts:
% 1.80/1.23  
% 1.80/1.23  
% 1.80/1.23  %Background operators:
% 1.80/1.23  
% 1.80/1.23  
% 1.80/1.23  %Foreground operators:
% 1.80/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.80/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.80/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.80/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.80/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.23  
% 1.80/1.24  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.80/1.24  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.80/1.24  tff(f_45, negated_conjecture, ~(![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.80/1.24  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.80/1.24  tff(c_58, plain, (![A_22, B_23]: (k4_xboole_0(k1_tarski(A_22), B_23)=k1_xboole_0 | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.80/1.24  tff(c_28, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_3', '#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.80/1.24  tff(c_67, plain, (~r2_hidden('#skF_3', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_28])).
% 1.80/1.24  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_67])).
% 1.80/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.24  
% 1.80/1.24  Inference rules
% 1.80/1.24  ----------------------
% 1.80/1.24  #Ref     : 0
% 1.80/1.24  #Sup     : 10
% 1.80/1.24  #Fact    : 0
% 1.80/1.24  #Define  : 0
% 1.80/1.24  #Split   : 0
% 1.80/1.24  #Chain   : 0
% 1.80/1.24  #Close   : 0
% 1.80/1.24  
% 1.80/1.24  Ordering : KBO
% 1.80/1.24  
% 1.80/1.24  Simplification rules
% 1.80/1.24  ----------------------
% 1.80/1.24  #Subsume      : 0
% 1.80/1.24  #Demod        : 2
% 1.80/1.24  #Tautology    : 7
% 1.80/1.24  #SimpNegUnit  : 0
% 1.80/1.24  #BackRed      : 0
% 1.80/1.24  
% 1.80/1.24  #Partial instantiations: 0
% 1.80/1.24  #Strategies tried      : 1
% 1.80/1.24  
% 1.80/1.24  Timing (in seconds)
% 1.80/1.24  ----------------------
% 1.80/1.25  Preprocessing        : 0.35
% 1.80/1.25  Parsing              : 0.18
% 1.80/1.25  CNF conversion       : 0.02
% 1.80/1.25  Main loop            : 0.09
% 1.80/1.25  Inferencing          : 0.03
% 1.80/1.25  Reduction            : 0.03
% 1.80/1.25  Demodulation         : 0.02
% 1.80/1.25  BG Simplification    : 0.01
% 1.80/1.25  Subsumption          : 0.02
% 1.80/1.25  Abstraction          : 0.01
% 1.80/1.25  MUC search           : 0.00
% 1.80/1.25  Cooper               : 0.00
% 1.80/1.25  Total                : 0.47
% 1.80/1.25  Index Insertion      : 0.00
% 1.80/1.25  Index Deletion       : 0.00
% 1.80/1.25  Index Matching       : 0.00
% 1.80/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:34 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,negated_conjecture,(
    ~ ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_xboole_1)).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    ! [D_19,B_20,A_21] :
      ( ~ r2_hidden(D_19,B_20)
      | ~ r2_hidden(D_19,k4_xboole_0(A_21,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [D_23,A_24] :
      ( ~ r2_hidden(D_23,A_24)
      | ~ r2_hidden(D_23,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_50])).

tff(c_64,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden('#skF_3'(A_25,B_26),k1_xboole_0)
      | ~ r2_xboole_0(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_69,plain,(
    ! [A_7] : ~ r2_xboole_0(A_7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_26,plain,(
    r2_xboole_0('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  
% 1.67/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  %$ r2_xboole_0 > r2_hidden > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.67/1.10  
% 1.67/1.10  %Foreground sorts:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Background operators:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Foreground operators:
% 1.67/1.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.67/1.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.67/1.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.10  
% 1.67/1.11  tff(f_45, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.67/1.11  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.67/1.11  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.67/1.11  tff(f_51, negated_conjecture, ~(![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_xboole_1)).
% 1.67/1.11  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.67/1.11  tff(c_24, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.67/1.11  tff(c_50, plain, (![D_19, B_20, A_21]: (~r2_hidden(D_19, B_20) | ~r2_hidden(D_19, k4_xboole_0(A_21, B_20)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.11  tff(c_60, plain, (![D_23, A_24]: (~r2_hidden(D_23, A_24) | ~r2_hidden(D_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_50])).
% 1.67/1.11  tff(c_64, plain, (![A_25, B_26]: (~r2_hidden('#skF_3'(A_25, B_26), k1_xboole_0) | ~r2_xboole_0(A_25, B_26))), inference(resolution, [status(thm)], [c_22, c_60])).
% 1.67/1.11  tff(c_69, plain, (![A_7]: (~r2_xboole_0(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_64])).
% 1.67/1.11  tff(c_26, plain, (r2_xboole_0('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.67/1.11  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_26])).
% 1.67/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  Inference rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Ref     : 0
% 1.67/1.11  #Sup     : 14
% 1.67/1.11  #Fact    : 0
% 1.67/1.11  #Define  : 0
% 1.67/1.11  #Split   : 0
% 1.67/1.11  #Chain   : 0
% 1.67/1.11  #Close   : 0
% 1.67/1.11  
% 1.67/1.11  Ordering : KBO
% 1.67/1.11  
% 1.67/1.11  Simplification rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Subsume      : 0
% 1.67/1.11  #Demod        : 0
% 1.67/1.11  #Tautology    : 6
% 1.67/1.11  #SimpNegUnit  : 1
% 1.67/1.11  #BackRed      : 1
% 1.67/1.11  
% 1.67/1.11  #Partial instantiations: 0
% 1.67/1.11  #Strategies tried      : 1
% 1.67/1.11  
% 1.67/1.11  Timing (in seconds)
% 1.67/1.11  ----------------------
% 1.67/1.11  Preprocessing        : 0.26
% 1.67/1.11  Parsing              : 0.14
% 1.67/1.11  CNF conversion       : 0.02
% 1.67/1.11  Main loop            : 0.10
% 1.67/1.11  Inferencing          : 0.04
% 1.67/1.11  Reduction            : 0.02
% 1.67/1.11  Demodulation         : 0.01
% 1.67/1.11  BG Simplification    : 0.01
% 1.67/1.11  Subsumption          : 0.02
% 1.67/1.11  Abstraction          : 0.00
% 1.67/1.11  MUC search           : 0.00
% 1.67/1.11  Cooper               : 0.00
% 1.67/1.11  Total                : 0.38
% 1.67/1.11  Index Insertion      : 0.00
% 1.67/1.11  Index Deletion       : 0.00
% 1.67/1.11  Index Matching       : 0.00
% 1.67/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

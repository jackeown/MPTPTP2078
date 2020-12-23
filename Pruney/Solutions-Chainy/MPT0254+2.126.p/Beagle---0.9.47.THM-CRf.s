%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:35 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_26,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden(A_25,B_26)
      | ~ r1_xboole_0(k1_tarski(A_25),B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    ! [A_25] : ~ r2_hidden(A_25,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_80,plain,(
    ! [D_30,A_31,B_32] :
      ( ~ r2_hidden(D_30,A_31)
      | r2_hidden(D_30,k2_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83,plain,(
    ! [D_30] :
      ( ~ r2_hidden(D_30,k1_tarski('#skF_5'))
      | r2_hidden(D_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_80])).

tff(c_85,plain,(
    ! [D_33] : ~ r2_hidden(D_33,k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_83])).

tff(c_90,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_26,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:23:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.10  
% 1.74/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.10  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.74/1.10  
% 1.74/1.10  %Foreground sorts:
% 1.74/1.10  
% 1.74/1.10  
% 1.74/1.10  %Background operators:
% 1.74/1.10  
% 1.74/1.10  
% 1.74/1.10  %Foreground operators:
% 1.74/1.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.74/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.74/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.74/1.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.74/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.10  tff('#skF_5', type, '#skF_5': $i).
% 1.74/1.10  tff('#skF_6', type, '#skF_6': $i).
% 1.74/1.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.74/1.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.74/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.74/1.10  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.74/1.10  
% 1.74/1.11  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.74/1.11  tff(f_36, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.74/1.11  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.74/1.11  tff(f_58, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.74/1.11  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.74/1.11  tff(c_26, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.74/1.11  tff(c_20, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.74/1.11  tff(c_64, plain, (![A_25, B_26]: (~r2_hidden(A_25, B_26) | ~r1_xboole_0(k1_tarski(A_25), B_26))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.74/1.11  tff(c_69, plain, (![A_25]: (~r2_hidden(A_25, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_64])).
% 1.74/1.11  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.74/1.11  tff(c_80, plain, (![D_30, A_31, B_32]: (~r2_hidden(D_30, A_31) | r2_hidden(D_30, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.74/1.11  tff(c_83, plain, (![D_30]: (~r2_hidden(D_30, k1_tarski('#skF_5')) | r2_hidden(D_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_80])).
% 1.74/1.11  tff(c_85, plain, (![D_33]: (~r2_hidden(D_33, k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_69, c_83])).
% 1.74/1.11  tff(c_90, plain, $false, inference(resolution, [status(thm)], [c_26, c_85])).
% 1.74/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.11  
% 1.74/1.11  Inference rules
% 1.74/1.11  ----------------------
% 1.74/1.11  #Ref     : 0
% 1.74/1.11  #Sup     : 10
% 1.74/1.11  #Fact    : 0
% 1.74/1.11  #Define  : 0
% 1.74/1.11  #Split   : 0
% 1.74/1.11  #Chain   : 0
% 1.74/1.11  #Close   : 0
% 1.74/1.11  
% 1.74/1.11  Ordering : KBO
% 1.74/1.11  
% 1.74/1.11  Simplification rules
% 1.74/1.11  ----------------------
% 1.74/1.11  #Subsume      : 0
% 1.74/1.11  #Demod        : 0
% 1.74/1.11  #Tautology    : 7
% 1.74/1.11  #SimpNegUnit  : 1
% 1.74/1.11  #BackRed      : 0
% 1.74/1.11  
% 1.74/1.11  #Partial instantiations: 0
% 1.74/1.11  #Strategies tried      : 1
% 1.74/1.11  
% 1.74/1.11  Timing (in seconds)
% 1.74/1.11  ----------------------
% 1.74/1.11  Preprocessing        : 0.30
% 1.74/1.12  Parsing              : 0.15
% 1.74/1.12  CNF conversion       : 0.02
% 1.74/1.12  Main loop            : 0.10
% 1.74/1.12  Inferencing          : 0.03
% 1.74/1.12  Reduction            : 0.03
% 1.74/1.12  Demodulation         : 0.02
% 1.74/1.12  BG Simplification    : 0.01
% 1.74/1.12  Subsumption          : 0.02
% 1.74/1.12  Abstraction          : 0.01
% 1.74/1.12  MUC search           : 0.00
% 1.74/1.12  Cooper               : 0.00
% 1.74/1.12  Total                : 0.42
% 1.74/1.12  Index Insertion      : 0.00
% 1.74/1.12  Index Deletion       : 0.00
% 1.74/1.12  Index Matching       : 0.00
% 1.74/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

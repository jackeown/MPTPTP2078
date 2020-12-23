%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:56 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  31 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

tff(c_42,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_70,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_70])).

tff(c_83,plain,(
    ! [D_35,B_36,A_37] :
      ( r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k3_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_38,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_83])).

tff(c_92,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_24,c_87])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_92,c_22])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.23  
% 1.90/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.24  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.90/1.24  
% 1.90/1.24  %Foreground sorts:
% 1.90/1.24  
% 1.90/1.24  
% 1.90/1.24  %Background operators:
% 1.90/1.24  
% 1.90/1.24  
% 1.90/1.24  %Foreground operators:
% 1.90/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.90/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.90/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.90/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.90/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.90/1.24  
% 1.90/1.25  tff(f_58, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.90/1.25  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.90/1.25  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.90/1.25  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.90/1.25  tff(c_42, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.90/1.25  tff(c_24, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.25  tff(c_44, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.90/1.25  tff(c_70, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.25  tff(c_74, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_44, c_70])).
% 1.90/1.25  tff(c_83, plain, (![D_35, B_36, A_37]: (r2_hidden(D_35, B_36) | ~r2_hidden(D_35, k3_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.25  tff(c_87, plain, (![D_38]: (r2_hidden(D_38, k1_tarski('#skF_6')) | ~r2_hidden(D_38, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_83])).
% 1.90/1.25  tff(c_92, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_87])).
% 1.90/1.25  tff(c_22, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.25  tff(c_95, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_92, c_22])).
% 1.90/1.25  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_95])).
% 1.90/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.25  
% 1.90/1.25  Inference rules
% 1.90/1.25  ----------------------
% 1.90/1.25  #Ref     : 0
% 1.90/1.25  #Sup     : 12
% 1.90/1.25  #Fact    : 0
% 1.90/1.25  #Define  : 0
% 1.90/1.25  #Split   : 0
% 1.90/1.25  #Chain   : 0
% 1.90/1.25  #Close   : 0
% 1.90/1.25  
% 1.90/1.25  Ordering : KBO
% 1.90/1.25  
% 1.90/1.25  Simplification rules
% 1.90/1.25  ----------------------
% 1.90/1.25  #Subsume      : 0
% 1.90/1.25  #Demod        : 0
% 1.90/1.25  #Tautology    : 8
% 1.90/1.25  #SimpNegUnit  : 1
% 1.90/1.25  #BackRed      : 0
% 1.90/1.25  
% 1.90/1.25  #Partial instantiations: 0
% 1.90/1.25  #Strategies tried      : 1
% 1.90/1.25  
% 1.90/1.25  Timing (in seconds)
% 1.90/1.25  ----------------------
% 1.90/1.25  Preprocessing        : 0.30
% 1.90/1.25  Parsing              : 0.15
% 1.90/1.25  CNF conversion       : 0.02
% 1.90/1.25  Main loop            : 0.17
% 1.90/1.25  Inferencing          : 0.05
% 1.90/1.25  Reduction            : 0.06
% 1.90/1.25  Demodulation         : 0.04
% 1.90/1.25  BG Simplification    : 0.02
% 1.90/1.25  Subsumption          : 0.03
% 1.90/1.25  Abstraction          : 0.01
% 1.90/1.25  MUC search           : 0.00
% 1.90/1.25  Cooper               : 0.00
% 1.90/1.25  Total                : 0.50
% 1.90/1.25  Index Insertion      : 0.00
% 1.90/1.25  Index Deletion       : 0.00
% 1.90/1.25  Index Matching       : 0.00
% 1.90/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

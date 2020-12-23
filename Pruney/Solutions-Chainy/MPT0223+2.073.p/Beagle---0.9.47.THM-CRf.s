%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:26 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_54,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    ! [D_34,B_35,A_36] :
      ( r2_hidden(D_34,B_35)
      | ~ r2_hidden(D_34,k3_xboole_0(A_36,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_104,plain,(
    ! [D_37] :
      ( r2_hidden(D_37,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_37,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_100])).

tff(c_109,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_22,c_104])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_112,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_109,c_20])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  %$ r2_hidden > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4
% 1.65/1.16  
% 1.65/1.16  %Foreground sorts:
% 1.65/1.16  
% 1.65/1.16  
% 1.65/1.16  %Background operators:
% 1.65/1.16  
% 1.65/1.16  
% 1.65/1.16  %Foreground operators:
% 1.65/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.65/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.16  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.65/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.16  tff('#skF_7', type, '#skF_7': $i).
% 1.65/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.65/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.65/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.16  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.65/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.65/1.16  tff('#skF_8', type, '#skF_8': $i).
% 1.65/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.16  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.65/1.16  
% 1.83/1.17  tff(f_59, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.83/1.17  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.83/1.17  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.83/1.17  tff(c_54, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.83/1.17  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.83/1.17  tff(c_56, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.83/1.17  tff(c_100, plain, (![D_34, B_35, A_36]: (r2_hidden(D_34, B_35) | ~r2_hidden(D_34, k3_xboole_0(A_36, B_35)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.83/1.17  tff(c_104, plain, (![D_37]: (r2_hidden(D_37, k1_tarski('#skF_8')) | ~r2_hidden(D_37, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_56, c_100])).
% 1.83/1.17  tff(c_109, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_22, c_104])).
% 1.83/1.17  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.83/1.17  tff(c_112, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_109, c_20])).
% 1.83/1.17  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_112])).
% 1.83/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  Inference rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Ref     : 0
% 1.83/1.17  #Sup     : 13
% 1.83/1.17  #Fact    : 0
% 1.83/1.17  #Define  : 0
% 1.83/1.17  #Split   : 0
% 1.83/1.17  #Chain   : 0
% 1.83/1.17  #Close   : 0
% 1.83/1.17  
% 1.83/1.17  Ordering : KBO
% 1.83/1.17  
% 1.83/1.17  Simplification rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Subsume      : 0
% 1.83/1.17  #Demod        : 2
% 1.83/1.17  #Tautology    : 10
% 1.83/1.17  #SimpNegUnit  : 1
% 1.83/1.17  #BackRed      : 0
% 1.83/1.17  
% 1.83/1.17  #Partial instantiations: 0
% 1.83/1.17  #Strategies tried      : 1
% 1.83/1.17  
% 1.83/1.17  Timing (in seconds)
% 1.83/1.17  ----------------------
% 1.83/1.17  Preprocessing        : 0.30
% 1.83/1.17  Parsing              : 0.15
% 1.83/1.17  CNF conversion       : 0.02
% 1.83/1.17  Main loop            : 0.11
% 1.83/1.17  Inferencing          : 0.03
% 1.83/1.17  Reduction            : 0.04
% 1.83/1.17  Demodulation         : 0.03
% 1.83/1.17  BG Simplification    : 0.01
% 1.83/1.17  Subsumption          : 0.02
% 1.83/1.18  Abstraction          : 0.01
% 1.83/1.18  MUC search           : 0.00
% 1.83/1.18  Cooper               : 0.00
% 1.83/1.18  Total                : 0.43
% 1.83/1.18  Index Insertion      : 0.00
% 1.83/1.18  Index Deletion       : 0.00
% 1.83/1.18  Index Matching       : 0.00
% 1.83/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

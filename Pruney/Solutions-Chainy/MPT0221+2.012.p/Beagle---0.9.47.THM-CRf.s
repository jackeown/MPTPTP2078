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
% DateTime   : Thu Dec  3 09:48:13 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_27,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_51,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | ~ r2_hidden(C_22,B_21)
      | ~ r2_hidden(C_22,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [C_23] : ~ r2_hidden(C_23,k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_27,c_51])).

tff(c_70,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n018.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 20:02:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 1.65/1.16  
% 1.65/1.16  %Foreground sorts:
% 1.65/1.16  
% 1.65/1.16  
% 1.65/1.16  %Background operators:
% 1.65/1.16  
% 1.65/1.16  
% 1.65/1.16  %Foreground operators:
% 1.65/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.65/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.65/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.65/1.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.65/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.65/1.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.65/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.65/1.16  
% 1.65/1.17  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.65/1.17  tff(f_60, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.65/1.17  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.65/1.17  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.65/1.17  tff(c_24, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.65/1.17  tff(c_26, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.65/1.17  tff(c_27, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 1.65/1.17  tff(c_51, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | ~r2_hidden(C_22, B_21) | ~r2_hidden(C_22, A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.17  tff(c_55, plain, (![C_23]: (~r2_hidden(C_23, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_27, c_51])).
% 1.65/1.17  tff(c_70, plain, $false, inference(resolution, [status(thm)], [c_10, c_55])).
% 1.65/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.17  
% 1.65/1.17  Inference rules
% 1.65/1.17  ----------------------
% 1.65/1.17  #Ref     : 0
% 1.65/1.17  #Sup     : 9
% 1.65/1.17  #Fact    : 0
% 1.65/1.17  #Define  : 0
% 1.65/1.17  #Split   : 0
% 1.65/1.17  #Chain   : 0
% 1.65/1.17  #Close   : 0
% 1.65/1.17  
% 1.65/1.17  Ordering : KBO
% 1.65/1.17  
% 1.65/1.17  Simplification rules
% 1.65/1.17  ----------------------
% 1.65/1.17  #Subsume      : 0
% 1.65/1.17  #Demod        : 1
% 1.65/1.17  #Tautology    : 3
% 1.65/1.17  #SimpNegUnit  : 0
% 1.65/1.17  #BackRed      : 0
% 1.65/1.17  
% 1.65/1.17  #Partial instantiations: 0
% 1.65/1.17  #Strategies tried      : 1
% 1.65/1.17  
% 1.65/1.17  Timing (in seconds)
% 1.65/1.17  ----------------------
% 1.80/1.17  Preprocessing        : 0.30
% 1.80/1.17  Parsing              : 0.16
% 1.80/1.17  CNF conversion       : 0.02
% 1.80/1.17  Main loop            : 0.08
% 1.80/1.17  Inferencing          : 0.03
% 1.80/1.17  Reduction            : 0.02
% 1.80/1.17  Demodulation         : 0.02
% 1.80/1.17  BG Simplification    : 0.01
% 1.80/1.17  Subsumption          : 0.01
% 1.80/1.17  Abstraction          : 0.00
% 1.80/1.17  MUC search           : 0.00
% 1.80/1.17  Cooper               : 0.00
% 1.80/1.17  Total                : 0.40
% 1.80/1.17  Index Insertion      : 0.00
% 1.80/1.17  Index Deletion       : 0.00
% 1.80/1.17  Index Matching       : 0.00
% 1.80/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

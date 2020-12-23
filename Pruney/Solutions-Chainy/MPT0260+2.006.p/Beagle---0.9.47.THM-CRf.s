%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:10 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

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

tff(c_24,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [A_23,C_24,B_25] :
      ( r2_hidden(A_23,C_24)
      | ~ r1_tarski(k2_tarski(A_23,B_25),C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    ! [A_23,B_25] : r2_hidden(A_23,k2_tarski(A_23,B_25)) ),
    inference(resolution,[status(thm)],[c_12,c_46])).

tff(c_26,plain,(
    r1_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,B_39)
      | ~ r2_hidden(C_40,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [C_41] :
      ( ~ r2_hidden(C_41,'#skF_4')
      | ~ r2_hidden(C_41,k2_tarski('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_51,c_74])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n006.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 16:49:52 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.19  
% 1.68/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.87/1.19  
% 1.87/1.19  %Foreground sorts:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Background operators:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Foreground operators:
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.19  
% 1.89/1.20  tff(f_65, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.89/1.20  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.89/1.20  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.89/1.20  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.89/1.20  tff(c_24, plain, (r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.20  tff(c_46, plain, (![A_23, C_24, B_25]: (r2_hidden(A_23, C_24) | ~r1_tarski(k2_tarski(A_23, B_25), C_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.89/1.20  tff(c_51, plain, (![A_23, B_25]: (r2_hidden(A_23, k2_tarski(A_23, B_25)))), inference(resolution, [status(thm)], [c_12, c_46])).
% 1.89/1.20  tff(c_26, plain, (r1_xboole_0(k2_tarski('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_70, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, B_39) | ~r2_hidden(C_40, A_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.89/1.20  tff(c_74, plain, (![C_41]: (~r2_hidden(C_41, '#skF_4') | ~r2_hidden(C_41, k2_tarski('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_26, c_70])).
% 1.89/1.20  tff(c_86, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_51, c_74])).
% 1.89/1.20  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_86])).
% 1.89/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  Inference rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Ref     : 0
% 1.89/1.20  #Sup     : 12
% 1.89/1.20  #Fact    : 0
% 1.89/1.20  #Define  : 0
% 1.89/1.20  #Split   : 0
% 1.89/1.20  #Chain   : 0
% 1.89/1.20  #Close   : 0
% 1.89/1.20  
% 1.89/1.20  Ordering : KBO
% 1.89/1.20  
% 1.89/1.20  Simplification rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Subsume      : 0
% 1.89/1.20  #Demod        : 3
% 1.89/1.20  #Tautology    : 6
% 1.89/1.20  #SimpNegUnit  : 0
% 1.89/1.20  #BackRed      : 0
% 1.89/1.20  
% 1.89/1.20  #Partial instantiations: 0
% 1.89/1.20  #Strategies tried      : 1
% 1.89/1.20  
% 1.89/1.20  Timing (in seconds)
% 1.89/1.20  ----------------------
% 1.89/1.20  Preprocessing        : 0.31
% 1.89/1.20  Parsing              : 0.16
% 1.89/1.20  CNF conversion       : 0.02
% 1.89/1.20  Main loop            : 0.10
% 1.89/1.20  Inferencing          : 0.04
% 1.89/1.20  Reduction            : 0.03
% 1.89/1.20  Demodulation         : 0.02
% 1.89/1.20  BG Simplification    : 0.01
% 1.89/1.20  Subsumption          : 0.02
% 1.89/1.20  Abstraction          : 0.01
% 1.89/1.20  MUC search           : 0.00
% 1.89/1.20  Cooper               : 0.00
% 1.89/1.20  Total                : 0.43
% 1.89/1.20  Index Insertion      : 0.00
% 1.89/1.20  Index Deletion       : 0.00
% 1.89/1.20  Index Matching       : 0.00
% 1.89/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

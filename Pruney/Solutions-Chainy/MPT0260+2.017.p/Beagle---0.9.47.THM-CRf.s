%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:11 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  36 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_22,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden('#skF_1'(A_25,B_26),B_26)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_50,plain,(
    ! [A_30,C_31,B_32] :
      ( r2_hidden(A_30,C_31)
      | ~ r1_tarski(k2_tarski(A_30,B_32),C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_55,plain,(
    ! [A_30,B_32] : r2_hidden(A_30,k2_tarski(A_30,B_32)) ),
    inference(resolution,[status(thm)],[c_42,c_50])).

tff(c_24,plain,(
    r1_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,B_38)
      | ~ r2_hidden(C_39,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    ! [C_40] :
      ( ~ r2_hidden(C_40,'#skF_5')
      | ~ r2_hidden(C_40,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_24,c_58])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_55,c_62])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.93/1.24  
% 1.93/1.24  %Foreground sorts:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Background operators:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Foreground operators:
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.93/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.24  
% 1.93/1.25  tff(f_64, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.93/1.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.93/1.25  tff(f_58, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.93/1.25  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.93/1.25  tff(c_22, plain, (r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.93/1.25  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.25  tff(c_37, plain, (![A_25, B_26]: (~r2_hidden('#skF_1'(A_25, B_26), B_26) | r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.25  tff(c_42, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_37])).
% 1.93/1.25  tff(c_50, plain, (![A_30, C_31, B_32]: (r2_hidden(A_30, C_31) | ~r1_tarski(k2_tarski(A_30, B_32), C_31))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.25  tff(c_55, plain, (![A_30, B_32]: (r2_hidden(A_30, k2_tarski(A_30, B_32)))), inference(resolution, [status(thm)], [c_42, c_50])).
% 1.93/1.25  tff(c_24, plain, (r1_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.93/1.25  tff(c_58, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, B_38) | ~r2_hidden(C_39, A_37))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.25  tff(c_62, plain, (![C_40]: (~r2_hidden(C_40, '#skF_5') | ~r2_hidden(C_40, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_24, c_58])).
% 1.93/1.25  tff(c_70, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_55, c_62])).
% 1.93/1.25  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_70])).
% 1.93/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  Inference rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Ref     : 0
% 1.93/1.25  #Sup     : 11
% 1.93/1.25  #Fact    : 0
% 1.93/1.25  #Define  : 0
% 1.93/1.25  #Split   : 0
% 1.93/1.25  #Chain   : 0
% 1.93/1.25  #Close   : 0
% 1.93/1.25  
% 1.93/1.25  Ordering : KBO
% 1.93/1.25  
% 1.93/1.25  Simplification rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Subsume      : 0
% 1.93/1.25  #Demod        : 1
% 1.93/1.25  #Tautology    : 2
% 1.93/1.25  #SimpNegUnit  : 0
% 1.93/1.25  #BackRed      : 0
% 1.93/1.25  
% 1.93/1.25  #Partial instantiations: 0
% 1.93/1.25  #Strategies tried      : 1
% 1.93/1.25  
% 1.93/1.25  Timing (in seconds)
% 1.93/1.25  ----------------------
% 1.93/1.25  Preprocessing        : 0.30
% 1.93/1.25  Parsing              : 0.16
% 1.93/1.25  CNF conversion       : 0.02
% 1.93/1.25  Main loop            : 0.10
% 1.93/1.25  Inferencing          : 0.04
% 1.93/1.25  Reduction            : 0.03
% 1.93/1.25  Demodulation         : 0.02
% 1.93/1.25  BG Simplification    : 0.01
% 1.93/1.25  Subsumption          : 0.02
% 1.93/1.25  Abstraction          : 0.01
% 1.93/1.25  MUC search           : 0.00
% 1.93/1.25  Cooper               : 0.00
% 1.93/1.25  Total                : 0.42
% 1.93/1.25  Index Insertion      : 0.00
% 1.93/1.25  Index Deletion       : 0.00
% 1.93/1.25  Index Matching       : 0.00
% 1.93/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:44 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_187,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(k1_tarski(A_51),B_52) = B_52
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_222,plain,(
    ! [A_51] : ~ r2_hidden(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_40])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    ! [B_35,C_36,A_37] :
      ( r2_hidden(B_35,C_36)
      | ~ r1_tarski(k2_tarski(A_37,B_35),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_147,plain,(
    ! [B_35,A_37] : r2_hidden(B_35,k2_tarski(A_37,B_35)) ),
    inference(resolution,[status(thm)],[c_26,c_142])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    ! [D_31,A_32,B_33] :
      ( ~ r2_hidden(D_31,A_32)
      | r2_hidden(D_31,k2_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_176,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_tarski('#skF_3','#skF_4'))
      | r2_hidden(D_50,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_128])).

tff(c_186,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_147,c_176])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.30  
% 1.93/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.30  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.93/1.30  
% 1.93/1.30  %Foreground sorts:
% 1.93/1.30  
% 1.93/1.30  
% 1.93/1.30  %Background operators:
% 1.93/1.30  
% 1.93/1.30  
% 1.93/1.30  %Foreground operators:
% 1.93/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.30  
% 1.93/1.31  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.93/1.31  tff(f_59, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.93/1.31  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.93/1.31  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.93/1.31  tff(f_63, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.93/1.31  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.93/1.31  tff(c_187, plain, (![A_51, B_52]: (k2_xboole_0(k1_tarski(A_51), B_52)=B_52 | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.31  tff(c_40, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.31  tff(c_222, plain, (![A_51]: (~r2_hidden(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_187, c_40])).
% 1.93/1.31  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.31  tff(c_142, plain, (![B_35, C_36, A_37]: (r2_hidden(B_35, C_36) | ~r1_tarski(k2_tarski(A_37, B_35), C_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.31  tff(c_147, plain, (![B_35, A_37]: (r2_hidden(B_35, k2_tarski(A_37, B_35)))), inference(resolution, [status(thm)], [c_26, c_142])).
% 1.93/1.31  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.31  tff(c_128, plain, (![D_31, A_32, B_33]: (~r2_hidden(D_31, A_32) | r2_hidden(D_31, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.31  tff(c_176, plain, (![D_50]: (~r2_hidden(D_50, k2_tarski('#skF_3', '#skF_4')) | r2_hidden(D_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_128])).
% 1.93/1.31  tff(c_186, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_147, c_176])).
% 1.93/1.31  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_186])).
% 1.93/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.31  
% 1.93/1.31  Inference rules
% 1.93/1.31  ----------------------
% 1.93/1.31  #Ref     : 0
% 1.93/1.31  #Sup     : 45
% 1.93/1.31  #Fact    : 0
% 1.93/1.31  #Define  : 0
% 1.93/1.31  #Split   : 0
% 1.93/1.31  #Chain   : 0
% 1.93/1.31  #Close   : 0
% 1.93/1.31  
% 1.93/1.31  Ordering : KBO
% 1.93/1.31  
% 1.93/1.31  Simplification rules
% 1.93/1.31  ----------------------
% 1.93/1.31  #Subsume      : 6
% 1.93/1.31  #Demod        : 5
% 1.93/1.31  #Tautology    : 22
% 1.93/1.31  #SimpNegUnit  : 4
% 1.93/1.31  #BackRed      : 4
% 1.93/1.31  
% 1.93/1.31  #Partial instantiations: 0
% 1.93/1.31  #Strategies tried      : 1
% 1.93/1.31  
% 1.93/1.31  Timing (in seconds)
% 1.93/1.31  ----------------------
% 1.93/1.32  Preprocessing        : 0.29
% 1.93/1.32  Parsing              : 0.14
% 1.93/1.32  CNF conversion       : 0.02
% 1.93/1.32  Main loop            : 0.21
% 1.93/1.32  Inferencing          : 0.08
% 1.93/1.32  Reduction            : 0.07
% 1.93/1.32  Demodulation         : 0.05
% 1.93/1.32  BG Simplification    : 0.01
% 1.93/1.32  Subsumption          : 0.04
% 1.93/1.32  Abstraction          : 0.01
% 1.93/1.32  MUC search           : 0.00
% 1.93/1.32  Cooper               : 0.00
% 1.93/1.32  Total                : 0.53
% 1.93/1.32  Index Insertion      : 0.00
% 1.93/1.32  Index Deletion       : 0.00
% 1.93/1.32  Index Matching       : 0.00
% 1.93/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

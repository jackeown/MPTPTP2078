%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:20 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  46 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_28,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_134,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k2_tarski(A_47,B_48),C_49)
      | ~ r2_hidden(B_48,C_49)
      | ~ r2_hidden(A_47,C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_29,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_31,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [A_39,B_40] : k4_xboole_0(k4_xboole_0(A_39,B_40),B_40) = k4_xboole_0(A_39,B_40) ),
    inference(resolution,[status(thm)],[c_29,c_31])).

tff(c_84,plain,(
    ! [B_40,A_39] : k5_xboole_0(B_40,k4_xboole_0(A_39,B_40)) = k2_xboole_0(B_40,k4_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_12])).

tff(c_102,plain,(
    ! [B_40,A_39] : k2_xboole_0(B_40,k4_xboole_0(A_39,B_40)) = k2_xboole_0(B_40,A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_84])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_132,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2])).

tff(c_383,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_xboole_0(k2_tarski(A_69,B_70),C_71) = C_71
      | ~ r2_hidden(B_70,C_71)
      | ~ r2_hidden(A_69,C_71) ) ),
    inference(resolution,[status(thm)],[c_134,c_132])).

tff(c_24,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_393,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_24])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.15/1.24  
% 2.15/1.24  %Foreground sorts:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Background operators:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Foreground operators:
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.24  
% 2.15/1.25  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 2.15/1.25  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.15/1.25  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.15/1.25  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.15/1.25  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 2.15/1.25  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.15/1.25  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.15/1.25  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.25  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.25  tff(c_134, plain, (![A_47, B_48, C_49]: (r1_tarski(k2_tarski(A_47, B_48), C_49) | ~r2_hidden(B_48, C_49) | ~r2_hidden(A_47, C_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.25  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.25  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.25  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, k3_xboole_0(A_7, B_8)), B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.25  tff(c_29, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 2.15/1.25  tff(c_31, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.25  tff(c_75, plain, (![A_39, B_40]: (k4_xboole_0(k4_xboole_0(A_39, B_40), B_40)=k4_xboole_0(A_39, B_40))), inference(resolution, [status(thm)], [c_29, c_31])).
% 2.15/1.25  tff(c_84, plain, (![B_40, A_39]: (k5_xboole_0(B_40, k4_xboole_0(A_39, B_40))=k2_xboole_0(B_40, k4_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_12])).
% 2.15/1.25  tff(c_102, plain, (![B_40, A_39]: (k2_xboole_0(B_40, k4_xboole_0(A_39, B_40))=k2_xboole_0(B_40, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_84])).
% 2.15/1.25  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.15/1.25  tff(c_132, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2])).
% 2.15/1.25  tff(c_383, plain, (![A_69, B_70, C_71]: (k2_xboole_0(k2_tarski(A_69, B_70), C_71)=C_71 | ~r2_hidden(B_70, C_71) | ~r2_hidden(A_69, C_71))), inference(resolution, [status(thm)], [c_134, c_132])).
% 2.15/1.25  tff(c_24, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.25  tff(c_393, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_383, c_24])).
% 2.15/1.25  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_393])).
% 2.15/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  Inference rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Ref     : 0
% 2.15/1.25  #Sup     : 92
% 2.15/1.25  #Fact    : 0
% 2.15/1.25  #Define  : 0
% 2.15/1.25  #Split   : 0
% 2.15/1.25  #Chain   : 0
% 2.15/1.25  #Close   : 0
% 2.15/1.25  
% 2.15/1.25  Ordering : KBO
% 2.15/1.25  
% 2.15/1.25  Simplification rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Subsume      : 0
% 2.15/1.25  #Demod        : 50
% 2.15/1.25  #Tautology    : 46
% 2.15/1.25  #SimpNegUnit  : 0
% 2.15/1.25  #BackRed      : 0
% 2.15/1.25  
% 2.15/1.25  #Partial instantiations: 0
% 2.15/1.25  #Strategies tried      : 1
% 2.15/1.25  
% 2.15/1.25  Timing (in seconds)
% 2.15/1.25  ----------------------
% 2.15/1.25  Preprocessing        : 0.28
% 2.15/1.25  Parsing              : 0.16
% 2.15/1.25  CNF conversion       : 0.02
% 2.15/1.25  Main loop            : 0.21
% 2.15/1.25  Inferencing          : 0.08
% 2.15/1.25  Reduction            : 0.07
% 2.15/1.26  Demodulation         : 0.06
% 2.15/1.26  BG Simplification    : 0.01
% 2.15/1.26  Subsumption          : 0.03
% 2.15/1.26  Abstraction          : 0.02
% 2.15/1.26  MUC search           : 0.00
% 2.15/1.26  Cooper               : 0.00
% 2.15/1.26  Total                : 0.52
% 2.15/1.26  Index Insertion      : 0.00
% 2.15/1.26  Index Deletion       : 0.00
% 2.15/1.26  Index Matching       : 0.00
% 2.15/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

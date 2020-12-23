%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:39 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_119,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_175,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_177,plain,
    ( k2_tarski('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_119,c_175])).

tff(c_186,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_177])).

tff(c_24,plain,(
    ! [D_17,B_13] : r2_hidden(D_17,k2_tarski(D_17,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [D_17,B_13] : ~ v1_xboole_0(k2_tarski(D_17,B_13)) ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_207,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_56])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.14  
% 1.85/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.14  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.85/1.14  
% 1.85/1.14  %Foreground sorts:
% 1.85/1.14  
% 1.85/1.14  
% 1.85/1.14  %Background operators:
% 1.85/1.14  
% 1.85/1.14  
% 1.85/1.14  %Foreground operators:
% 1.85/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.85/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.85/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.85/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.85/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.85/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.14  
% 1.85/1.15  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.85/1.15  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.85/1.15  tff(f_65, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.85/1.15  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.85/1.15  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.85/1.15  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.85/1.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.85/1.15  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.15  tff(c_14, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.85/1.15  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.15  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.85/1.15  tff(c_119, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_16])).
% 1.85/1.15  tff(c_175, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.15  tff(c_177, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_119, c_175])).
% 1.85/1.15  tff(c_186, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_177])).
% 1.85/1.15  tff(c_24, plain, (![D_17, B_13]: (r2_hidden(D_17, k2_tarski(D_17, B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.15  tff(c_52, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.15  tff(c_56, plain, (![D_17, B_13]: (~v1_xboole_0(k2_tarski(D_17, B_13)))), inference(resolution, [status(thm)], [c_24, c_52])).
% 1.85/1.15  tff(c_207, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_186, c_56])).
% 1.85/1.15  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_207])).
% 1.85/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.15  
% 1.85/1.15  Inference rules
% 1.85/1.15  ----------------------
% 1.85/1.15  #Ref     : 0
% 1.85/1.15  #Sup     : 43
% 1.85/1.15  #Fact    : 0
% 1.85/1.15  #Define  : 0
% 1.85/1.15  #Split   : 0
% 1.85/1.15  #Chain   : 0
% 1.85/1.15  #Close   : 0
% 1.85/1.15  
% 1.85/1.15  Ordering : KBO
% 1.85/1.15  
% 1.85/1.15  Simplification rules
% 1.85/1.15  ----------------------
% 1.85/1.15  #Subsume      : 3
% 1.85/1.15  #Demod        : 13
% 1.85/1.15  #Tautology    : 27
% 1.85/1.15  #SimpNegUnit  : 0
% 1.85/1.15  #BackRed      : 2
% 1.85/1.15  
% 1.85/1.15  #Partial instantiations: 0
% 1.85/1.15  #Strategies tried      : 1
% 1.85/1.15  
% 1.85/1.15  Timing (in seconds)
% 1.85/1.15  ----------------------
% 1.85/1.16  Preprocessing        : 0.32
% 1.85/1.16  Parsing              : 0.17
% 1.85/1.16  CNF conversion       : 0.02
% 1.85/1.16  Main loop            : 0.14
% 1.85/1.16  Inferencing          : 0.04
% 1.85/1.16  Reduction            : 0.05
% 1.85/1.16  Demodulation         : 0.04
% 1.85/1.16  BG Simplification    : 0.01
% 1.85/1.16  Subsumption          : 0.02
% 1.85/1.16  Abstraction          : 0.01
% 1.85/1.16  MUC search           : 0.00
% 1.85/1.16  Cooper               : 0.00
% 1.85/1.16  Total                : 0.48
% 1.85/1.16  Index Insertion      : 0.00
% 1.85/1.16  Index Deletion       : 0.00
% 1.85/1.16  Index Matching       : 0.00
% 1.85/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

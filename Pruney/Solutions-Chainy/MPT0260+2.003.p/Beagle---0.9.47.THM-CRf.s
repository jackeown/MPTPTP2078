%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:09 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   46 (  47 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_32,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_41,B_42] : r1_tarski(k1_tarski(A_41),k2_tarski(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_91,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_91])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_99,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_2])).

tff(c_149,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_149])).

tff(c_170,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_158])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,k4_xboole_0(C_10,B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_259,plain,(
    ! [A_73] :
      ( r1_xboole_0(A_73,'#skF_3')
      | ~ r1_tarski(A_73,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_12])).

tff(c_264,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_259])).

tff(c_28,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden(A_39,B_40)
      | ~ r1_xboole_0(k1_tarski(A_39),B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_267,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_264,c_28])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.24  
% 2.28/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.28/1.25  
% 2.28/1.25  %Foreground sorts:
% 2.28/1.25  
% 2.28/1.25  
% 2.28/1.25  %Background operators:
% 2.28/1.25  
% 2.28/1.25  
% 2.28/1.25  %Foreground operators:
% 2.28/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.28/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.28/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.25  
% 2.28/1.26  tff(f_66, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.28/1.26  tff(f_60, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.28/1.26  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.28/1.26  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.28/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.28/1.26  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.28/1.26  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.28/1.26  tff(f_58, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.28/1.26  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.26  tff(c_30, plain, (![A_41, B_42]: (r1_tarski(k1_tarski(A_41), k2_tarski(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.28/1.26  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.26  tff(c_34, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.26  tff(c_91, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.26  tff(c_95, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_91])).
% 2.28/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.26  tff(c_99, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_95, c_2])).
% 2.28/1.26  tff(c_149, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.26  tff(c_158, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_99, c_149])).
% 2.28/1.26  tff(c_170, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_158])).
% 2.28/1.26  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, k4_xboole_0(C_10, B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.26  tff(c_259, plain, (![A_73]: (r1_xboole_0(A_73, '#skF_3') | ~r1_tarski(A_73, k2_tarski('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_170, c_12])).
% 2.28/1.26  tff(c_264, plain, (r1_xboole_0(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_30, c_259])).
% 2.28/1.26  tff(c_28, plain, (![A_39, B_40]: (~r2_hidden(A_39, B_40) | ~r1_xboole_0(k1_tarski(A_39), B_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.28/1.26  tff(c_267, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_264, c_28])).
% 2.28/1.26  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_267])).
% 2.28/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.26  
% 2.28/1.26  Inference rules
% 2.28/1.26  ----------------------
% 2.28/1.26  #Ref     : 0
% 2.28/1.26  #Sup     : 59
% 2.28/1.26  #Fact    : 0
% 2.28/1.26  #Define  : 0
% 2.28/1.26  #Split   : 0
% 2.28/1.26  #Chain   : 0
% 2.28/1.26  #Close   : 0
% 2.28/1.26  
% 2.28/1.26  Ordering : KBO
% 2.28/1.26  
% 2.28/1.26  Simplification rules
% 2.28/1.26  ----------------------
% 2.28/1.26  #Subsume      : 3
% 2.28/1.26  #Demod        : 13
% 2.28/1.26  #Tautology    : 39
% 2.28/1.26  #SimpNegUnit  : 0
% 2.28/1.26  #BackRed      : 0
% 2.28/1.26  
% 2.28/1.26  #Partial instantiations: 0
% 2.28/1.26  #Strategies tried      : 1
% 2.28/1.26  
% 2.28/1.26  Timing (in seconds)
% 2.28/1.26  ----------------------
% 2.28/1.26  Preprocessing        : 0.30
% 2.28/1.26  Parsing              : 0.16
% 2.28/1.26  CNF conversion       : 0.02
% 2.28/1.26  Main loop            : 0.16
% 2.28/1.26  Inferencing          : 0.06
% 2.28/1.26  Reduction            : 0.06
% 2.28/1.26  Demodulation         : 0.05
% 2.28/1.26  BG Simplification    : 0.01
% 2.28/1.26  Subsumption          : 0.02
% 2.28/1.26  Abstraction          : 0.01
% 2.28/1.26  MUC search           : 0.00
% 2.28/1.26  Cooper               : 0.00
% 2.28/1.26  Total                : 0.49
% 2.28/1.26  Index Insertion      : 0.00
% 2.28/1.26  Index Deletion       : 0.00
% 2.28/1.26  Index Matching       : 0.00
% 2.28/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

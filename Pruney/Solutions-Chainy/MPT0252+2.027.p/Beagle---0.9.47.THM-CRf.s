%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:04 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(resolution,[status(thm)],[c_10,c_71])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_tarski(k3_xboole_0(A_64,C_65),B_66)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_193,plain,(
    ! [A_80,B_81,B_82] :
      ( r1_tarski(k3_xboole_0(A_80,B_81),B_82)
      | ~ r1_tarski(B_81,B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_130])).

tff(c_261,plain,(
    ! [A_88,B_89,B_90] :
      ( r1_tarski(A_88,B_89)
      | ~ r1_tarski(k2_xboole_0(A_88,B_90),B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_193])).

tff(c_273,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_261])).

tff(c_32,plain,(
    ! [A_43,C_45,B_44] :
      ( r2_hidden(A_43,C_45)
      | ~ r1_tarski(k2_tarski(A_43,B_44),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_280,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_273,c_32])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.43  
% 2.31/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.44  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.31/1.44  
% 2.31/1.44  %Foreground sorts:
% 2.31/1.44  
% 2.31/1.44  
% 2.31/1.44  %Background operators:
% 2.31/1.44  
% 2.31/1.44  
% 2.31/1.44  %Foreground operators:
% 2.31/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.31/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.31/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.44  
% 2.31/1.45  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.31/1.45  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.31/1.45  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.31/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.31/1.45  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.31/1.45  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.31/1.45  tff(c_34, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.45  tff(c_36, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.45  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.45  tff(c_71, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.45  tff(c_79, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(resolution, [status(thm)], [c_10, c_71])).
% 2.31/1.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.45  tff(c_130, plain, (![A_64, C_65, B_66]: (r1_tarski(k3_xboole_0(A_64, C_65), B_66) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.45  tff(c_193, plain, (![A_80, B_81, B_82]: (r1_tarski(k3_xboole_0(A_80, B_81), B_82) | ~r1_tarski(B_81, B_82))), inference(superposition, [status(thm), theory('equality')], [c_2, c_130])).
% 2.31/1.45  tff(c_261, plain, (![A_88, B_89, B_90]: (r1_tarski(A_88, B_89) | ~r1_tarski(k2_xboole_0(A_88, B_90), B_89))), inference(superposition, [status(thm), theory('equality')], [c_79, c_193])).
% 2.31/1.45  tff(c_273, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_36, c_261])).
% 2.31/1.45  tff(c_32, plain, (![A_43, C_45, B_44]: (r2_hidden(A_43, C_45) | ~r1_tarski(k2_tarski(A_43, B_44), C_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.45  tff(c_280, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_273, c_32])).
% 2.31/1.45  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_280])).
% 2.31/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.45  
% 2.31/1.45  Inference rules
% 2.31/1.45  ----------------------
% 2.31/1.45  #Ref     : 0
% 2.31/1.45  #Sup     : 62
% 2.31/1.45  #Fact    : 0
% 2.31/1.45  #Define  : 0
% 2.31/1.45  #Split   : 0
% 2.31/1.45  #Chain   : 0
% 2.31/1.45  #Close   : 0
% 2.31/1.45  
% 2.31/1.45  Ordering : KBO
% 2.31/1.45  
% 2.31/1.45  Simplification rules
% 2.31/1.45  ----------------------
% 2.31/1.45  #Subsume      : 3
% 2.31/1.45  #Demod        : 3
% 2.31/1.45  #Tautology    : 33
% 2.31/1.45  #SimpNegUnit  : 1
% 2.31/1.45  #BackRed      : 0
% 2.31/1.45  
% 2.31/1.45  #Partial instantiations: 0
% 2.31/1.45  #Strategies tried      : 1
% 2.31/1.45  
% 2.31/1.45  Timing (in seconds)
% 2.31/1.45  ----------------------
% 2.52/1.45  Preprocessing        : 0.42
% 2.52/1.45  Parsing              : 0.20
% 2.52/1.45  CNF conversion       : 0.03
% 2.52/1.45  Main loop            : 0.21
% 2.52/1.45  Inferencing          : 0.08
% 2.52/1.45  Reduction            : 0.07
% 2.52/1.45  Demodulation         : 0.05
% 2.52/1.45  BG Simplification    : 0.02
% 2.52/1.45  Subsumption          : 0.03
% 2.52/1.45  Abstraction          : 0.02
% 2.52/1.45  MUC search           : 0.00
% 2.52/1.45  Cooper               : 0.00
% 2.52/1.45  Total                : 0.65
% 2.52/1.45  Index Insertion      : 0.00
% 2.52/1.45  Index Deletion       : 0.00
% 2.52/1.45  Index Matching       : 0.00
% 2.52/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

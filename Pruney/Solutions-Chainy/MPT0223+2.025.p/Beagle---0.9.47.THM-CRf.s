%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:20 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_54,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_127,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_279,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(B_60,A_61)
      | k3_xboole_0(A_61,k1_tarski(B_60)) != k1_tarski(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_294,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_279])).

tff(c_32,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_298,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_294,c_32])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:34:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.05/1.24  
% 2.05/1.24  %Foreground sorts:
% 2.05/1.24  
% 2.05/1.24  
% 2.05/1.24  %Background operators:
% 2.05/1.24  
% 2.05/1.24  
% 2.05/1.24  %Foreground operators:
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.05/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.05/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.05/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.05/1.24  
% 2.05/1.25  tff(f_72, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.05/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.05/1.25  tff(f_67, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.05/1.25  tff(f_53, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.05/1.25  tff(c_54, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.05/1.25  tff(c_56, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.05/1.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.25  tff(c_127, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 2.05/1.25  tff(c_279, plain, (![B_60, A_61]: (r2_hidden(B_60, A_61) | k3_xboole_0(A_61, k1_tarski(B_60))!=k1_tarski(B_60))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.05/1.25  tff(c_294, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_279])).
% 2.05/1.25  tff(c_32, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.25  tff(c_298, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_294, c_32])).
% 2.05/1.25  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_298])).
% 2.05/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  Inference rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Ref     : 0
% 2.05/1.25  #Sup     : 61
% 2.05/1.25  #Fact    : 0
% 2.05/1.25  #Define  : 0
% 2.05/1.25  #Split   : 1
% 2.05/1.25  #Chain   : 0
% 2.05/1.25  #Close   : 0
% 2.05/1.25  
% 2.05/1.25  Ordering : KBO
% 2.05/1.25  
% 2.05/1.25  Simplification rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Subsume      : 1
% 2.05/1.25  #Demod        : 13
% 2.05/1.25  #Tautology    : 44
% 2.05/1.25  #SimpNegUnit  : 2
% 2.05/1.25  #BackRed      : 0
% 2.05/1.25  
% 2.05/1.25  #Partial instantiations: 0
% 2.05/1.25  #Strategies tried      : 1
% 2.05/1.25  
% 2.05/1.25  Timing (in seconds)
% 2.05/1.25  ----------------------
% 2.05/1.25  Preprocessing        : 0.31
% 2.05/1.25  Parsing              : 0.16
% 2.05/1.25  CNF conversion       : 0.02
% 2.05/1.25  Main loop            : 0.18
% 2.05/1.25  Inferencing          : 0.05
% 2.05/1.25  Reduction            : 0.07
% 2.05/1.25  Demodulation         : 0.05
% 2.05/1.25  BG Simplification    : 0.02
% 2.05/1.25  Subsumption          : 0.04
% 2.05/1.25  Abstraction          : 0.01
% 2.05/1.25  MUC search           : 0.00
% 2.05/1.25  Cooper               : 0.00
% 2.05/1.25  Total                : 0.52
% 2.05/1.25  Index Insertion      : 0.00
% 2.05/1.25  Index Deletion       : 0.00
% 2.05/1.25  Index Matching       : 0.00
% 2.05/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

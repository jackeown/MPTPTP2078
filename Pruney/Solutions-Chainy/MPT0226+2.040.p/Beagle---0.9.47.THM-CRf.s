%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:42 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  32 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_56,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_150,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_172,plain,(
    ! [C_62,B_63] :
      ( r2_hidden(C_62,B_63)
      | ~ r1_tarski(k1_tarski(C_62),B_63) ) ),
    inference(resolution,[status(thm)],[c_40,c_150])).

tff(c_214,plain,(
    ! [C_70,B_71] :
      ( r2_hidden(C_70,B_71)
      | k4_xboole_0(k1_tarski(C_70),B_71) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_172])).

tff(c_224,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_214])).

tff(c_38,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_229,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_224,c_38])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.20  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 1.94/1.20  
% 1.94/1.20  %Foreground sorts:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Background operators:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Foreground operators:
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.20  tff('#skF_7', type, '#skF_7': $i).
% 1.94/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.94/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.94/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.94/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.94/1.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.94/1.20  
% 1.94/1.21  tff(f_71, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.94/1.21  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.94/1.21  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.94/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.94/1.21  tff(c_56, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.94/1.21  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.94/1.21  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.21  tff(c_40, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.21  tff(c_150, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.21  tff(c_172, plain, (![C_62, B_63]: (r2_hidden(C_62, B_63) | ~r1_tarski(k1_tarski(C_62), B_63))), inference(resolution, [status(thm)], [c_40, c_150])).
% 1.94/1.21  tff(c_214, plain, (![C_70, B_71]: (r2_hidden(C_70, B_71) | k4_xboole_0(k1_tarski(C_70), B_71)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_172])).
% 1.94/1.21  tff(c_224, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_214])).
% 1.94/1.21  tff(c_38, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.21  tff(c_229, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_224, c_38])).
% 1.94/1.21  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_229])).
% 1.94/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  Inference rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Ref     : 0
% 1.94/1.21  #Sup     : 39
% 1.94/1.21  #Fact    : 0
% 1.94/1.21  #Define  : 0
% 1.94/1.21  #Split   : 0
% 1.94/1.21  #Chain   : 0
% 1.94/1.21  #Close   : 0
% 1.94/1.21  
% 1.94/1.21  Ordering : KBO
% 1.94/1.21  
% 1.94/1.21  Simplification rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Subsume      : 2
% 1.94/1.21  #Demod        : 7
% 1.94/1.21  #Tautology    : 19
% 1.94/1.21  #SimpNegUnit  : 1
% 1.94/1.21  #BackRed      : 0
% 1.94/1.21  
% 1.94/1.21  #Partial instantiations: 0
% 1.94/1.21  #Strategies tried      : 1
% 1.94/1.21  
% 1.94/1.21  Timing (in seconds)
% 1.94/1.21  ----------------------
% 1.94/1.21  Preprocessing        : 0.30
% 1.94/1.21  Parsing              : 0.14
% 1.94/1.21  CNF conversion       : 0.02
% 1.94/1.21  Main loop            : 0.16
% 1.94/1.21  Inferencing          : 0.05
% 1.94/1.21  Reduction            : 0.05
% 1.94/1.21  Demodulation         : 0.04
% 1.94/1.21  BG Simplification    : 0.01
% 1.94/1.21  Subsumption          : 0.03
% 1.94/1.21  Abstraction          : 0.01
% 1.94/1.21  MUC search           : 0.00
% 1.94/1.21  Cooper               : 0.00
% 1.94/1.21  Total                : 0.48
% 1.94/1.21  Index Insertion      : 0.00
% 1.94/1.21  Index Deletion       : 0.00
% 1.94/1.21  Index Matching       : 0.00
% 1.94/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

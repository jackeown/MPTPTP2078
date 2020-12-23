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
% DateTime   : Thu Dec  3 09:52:46 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(c_42,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_236,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,k1_tarski(B_69)) = A_68
      | r2_hidden(B_69,A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_249,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_46])).

tff(c_262,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_249])).

tff(c_36,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_266,plain,(
    ! [A_70,B_71] :
      ( r2_xboole_0(A_70,B_71)
      | B_71 = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k4_xboole_0(B_8,A_7) != k1_xboole_0
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1120,plain,(
    ! [B_122,A_123] :
      ( k4_xboole_0(B_122,A_123) != k1_xboole_0
      | B_122 = A_123
      | ~ r1_tarski(A_123,B_122) ) ),
    inference(resolution,[status(thm)],[c_266,c_12])).

tff(c_12499,plain,(
    ! [B_193,A_194] :
      ( k4_xboole_0(B_193,k1_tarski(A_194)) != k1_xboole_0
      | k1_tarski(A_194) = B_193
      | ~ r2_hidden(A_194,B_193) ) ),
    inference(resolution,[status(thm)],[c_36,c_1120])).

tff(c_12509,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_12499])).

tff(c_12512,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_12509])).

tff(c_12514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_12512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:49:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.91/3.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/3.55  
% 7.91/3.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/3.55  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.91/3.55  
% 7.91/3.55  %Foreground sorts:
% 7.91/3.55  
% 7.91/3.55  
% 7.91/3.55  %Background operators:
% 7.91/3.55  
% 7.91/3.55  
% 7.91/3.55  %Foreground operators:
% 7.91/3.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.91/3.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.91/3.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.91/3.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.91/3.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.91/3.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.91/3.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.91/3.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.91/3.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.91/3.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.91/3.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.91/3.55  tff('#skF_2', type, '#skF_2': $i).
% 7.91/3.55  tff('#skF_1', type, '#skF_1': $i).
% 7.91/3.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.91/3.55  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 7.91/3.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.91/3.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.91/3.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.91/3.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.91/3.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.91/3.55  
% 7.91/3.56  tff(f_80, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 7.91/3.56  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.91/3.56  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.91/3.56  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 7.91/3.56  tff(f_41, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 7.91/3.56  tff(c_42, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.91/3.56  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.91/3.56  tff(c_236, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k1_tarski(B_69))=A_68 | r2_hidden(B_69, A_68))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.91/3.56  tff(c_46, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.91/3.56  tff(c_249, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_236, c_46])).
% 7.91/3.56  tff(c_262, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_249])).
% 7.91/3.56  tff(c_36, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.91/3.56  tff(c_266, plain, (![A_70, B_71]: (r2_xboole_0(A_70, B_71) | B_71=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.91/3.56  tff(c_12, plain, (![B_8, A_7]: (k4_xboole_0(B_8, A_7)!=k1_xboole_0 | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.91/3.56  tff(c_1120, plain, (![B_122, A_123]: (k4_xboole_0(B_122, A_123)!=k1_xboole_0 | B_122=A_123 | ~r1_tarski(A_123, B_122))), inference(resolution, [status(thm)], [c_266, c_12])).
% 7.91/3.56  tff(c_12499, plain, (![B_193, A_194]: (k4_xboole_0(B_193, k1_tarski(A_194))!=k1_xboole_0 | k1_tarski(A_194)=B_193 | ~r2_hidden(A_194, B_193))), inference(resolution, [status(thm)], [c_36, c_1120])).
% 7.91/3.56  tff(c_12509, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_46, c_12499])).
% 7.91/3.56  tff(c_12512, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_262, c_12509])).
% 7.91/3.56  tff(c_12514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_12512])).
% 7.91/3.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/3.56  
% 7.91/3.56  Inference rules
% 7.91/3.56  ----------------------
% 7.91/3.56  #Ref     : 0
% 7.91/3.56  #Sup     : 3177
% 7.91/3.56  #Fact    : 0
% 7.91/3.56  #Define  : 0
% 7.91/3.56  #Split   : 0
% 7.91/3.56  #Chain   : 0
% 7.91/3.56  #Close   : 0
% 7.91/3.56  
% 7.91/3.56  Ordering : KBO
% 7.91/3.56  
% 7.91/3.56  Simplification rules
% 7.91/3.56  ----------------------
% 7.91/3.56  #Subsume      : 363
% 7.91/3.56  #Demod        : 4881
% 7.91/3.56  #Tautology    : 1395
% 7.91/3.56  #SimpNegUnit  : 5
% 7.91/3.56  #BackRed      : 1
% 7.91/3.56  
% 7.91/3.56  #Partial instantiations: 0
% 7.91/3.56  #Strategies tried      : 1
% 7.91/3.56  
% 7.91/3.56  Timing (in seconds)
% 7.91/3.56  ----------------------
% 7.91/3.56  Preprocessing        : 0.30
% 7.91/3.56  Parsing              : 0.15
% 7.91/3.56  CNF conversion       : 0.02
% 7.91/3.56  Main loop            : 2.59
% 7.91/3.56  Inferencing          : 0.45
% 7.91/3.56  Reduction            : 1.79
% 7.91/3.56  Demodulation         : 1.68
% 7.91/3.56  BG Simplification    : 0.07
% 7.91/3.56  Subsumption          : 0.21
% 7.91/3.56  Abstraction          : 0.11
% 7.91/3.56  MUC search           : 0.00
% 7.91/3.56  Cooper               : 0.00
% 7.91/3.56  Total                : 2.91
% 7.91/3.57  Index Insertion      : 0.00
% 7.91/3.57  Index Deletion       : 0.00
% 7.91/3.57  Index Matching       : 0.00
% 7.91/3.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

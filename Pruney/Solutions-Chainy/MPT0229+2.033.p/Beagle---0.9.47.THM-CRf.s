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
% DateTime   : Thu Dec  3 09:48:57 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   35 (  55 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  74 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(c_24,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    ! [B_33,A_34] :
      ( k1_tarski(B_33) = A_34
      | k1_xboole_0 = A_34
      | ~ r1_tarski(A_34,k1_tarski(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,
    ( k1_tarski('#skF_2') = k1_tarski('#skF_1')
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_88])).

tff(c_103,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_57,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [B_13] : ~ r1_xboole_0(k1_tarski(B_13),k1_tarski(B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_61,plain,(
    ! [B_13] : k4_xboole_0(k1_tarski(B_13),k1_tarski(B_13)) != k1_tarski(B_13) ),
    inference(resolution,[status(thm)],[c_57,c_20])).

tff(c_112,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_61])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2,c_103,c_112])).

tff(c_142,plain,(
    k1_tarski('#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(k1_tarski(A_14),k1_tarski(B_15))
      | B_15 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_187,plain,(
    ! [B_35] :
      ( r1_xboole_0(k1_tarski('#skF_1'),k1_tarski(B_35))
      | B_35 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_22])).

tff(c_194,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_187,c_20])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  %$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.64/1.15  
% 1.64/1.15  %Foreground sorts:
% 1.64/1.15  
% 1.64/1.15  
% 1.64/1.15  %Background operators:
% 1.64/1.15  
% 1.64/1.15  
% 1.64/1.15  %Foreground operators:
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.64/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.64/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.64/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.15  
% 1.64/1.16  tff(f_58, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.64/1.16  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.64/1.16  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.64/1.16  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.64/1.16  tff(f_48, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.64/1.16  tff(f_53, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.64/1.16  tff(c_24, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.64/1.16  tff(c_26, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.64/1.16  tff(c_88, plain, (![B_33, A_34]: (k1_tarski(B_33)=A_34 | k1_xboole_0=A_34 | ~r1_tarski(A_34, k1_tarski(B_33)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.64/1.16  tff(c_100, plain, (k1_tarski('#skF_2')=k1_tarski('#skF_1') | k1_tarski('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_88])).
% 1.64/1.16  tff(c_103, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_100])).
% 1.64/1.16  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.16  tff(c_57, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k4_xboole_0(A_23, B_24)!=A_23)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.16  tff(c_20, plain, (![B_13]: (~r1_xboole_0(k1_tarski(B_13), k1_tarski(B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.16  tff(c_61, plain, (![B_13]: (k4_xboole_0(k1_tarski(B_13), k1_tarski(B_13))!=k1_tarski(B_13))), inference(resolution, [status(thm)], [c_57, c_20])).
% 1.64/1.16  tff(c_112, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_103, c_61])).
% 1.64/1.16  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_2, c_103, c_112])).
% 1.64/1.16  tff(c_142, plain, (k1_tarski('#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_100])).
% 1.64/1.16  tff(c_22, plain, (![A_14, B_15]: (r1_xboole_0(k1_tarski(A_14), k1_tarski(B_15)) | B_15=A_14)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.64/1.16  tff(c_187, plain, (![B_35]: (r1_xboole_0(k1_tarski('#skF_1'), k1_tarski(B_35)) | B_35='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_142, c_22])).
% 1.64/1.16  tff(c_194, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_187, c_20])).
% 1.64/1.16  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_194])).
% 1.64/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  Inference rules
% 1.64/1.16  ----------------------
% 1.64/1.16  #Ref     : 0
% 1.64/1.16  #Sup     : 42
% 1.64/1.16  #Fact    : 0
% 1.64/1.16  #Define  : 0
% 1.64/1.16  #Split   : 1
% 1.64/1.16  #Chain   : 0
% 1.64/1.16  #Close   : 0
% 1.64/1.16  
% 1.64/1.16  Ordering : KBO
% 1.64/1.16  
% 1.64/1.16  Simplification rules
% 1.64/1.16  ----------------------
% 1.64/1.16  #Subsume      : 5
% 1.64/1.16  #Demod        : 20
% 1.64/1.16  #Tautology    : 20
% 1.64/1.16  #SimpNegUnit  : 1
% 1.64/1.16  #BackRed      : 2
% 1.64/1.16  
% 1.64/1.16  #Partial instantiations: 0
% 1.64/1.16  #Strategies tried      : 1
% 1.64/1.16  
% 1.64/1.16  Timing (in seconds)
% 1.64/1.16  ----------------------
% 1.64/1.16  Preprocessing        : 0.28
% 1.64/1.16  Parsing              : 0.15
% 1.64/1.16  CNF conversion       : 0.02
% 1.64/1.16  Main loop            : 0.13
% 1.64/1.16  Inferencing          : 0.05
% 1.64/1.16  Reduction            : 0.04
% 1.64/1.16  Demodulation         : 0.03
% 1.64/1.16  BG Simplification    : 0.01
% 1.64/1.16  Subsumption          : 0.02
% 1.64/1.16  Abstraction          : 0.01
% 1.64/1.16  MUC search           : 0.00
% 1.64/1.16  Cooper               : 0.00
% 1.64/1.16  Total                : 0.43
% 1.64/1.16  Index Insertion      : 0.00
% 1.64/1.16  Index Deletion       : 0.00
% 1.64/1.16  Index Matching       : 0.00
% 1.64/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

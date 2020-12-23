%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:45 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_54,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46,plain,(
    ! [B_23] : r1_tarski(k1_tarski(B_23),k1_tarski(B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [B_23] : k4_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_99])).

tff(c_50,plain,(
    ! [B_25] : k4_xboole_0(k1_tarski(B_25),k1_tarski(B_25)) != k1_tarski(B_25) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_126,plain,(
    ! [B_25] : k1_tarski(B_25) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_50])).

tff(c_172,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(k1_tarski(A_52),k1_tarski(B_53)) = k1_tarski(A_52)
      | B_53 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_182,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_56])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_126,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.22  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 1.94/1.22  
% 1.94/1.22  %Foreground sorts:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Background operators:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Foreground operators:
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.94/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.94/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.22  
% 1.94/1.23  tff(f_69, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.94/1.23  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.94/1.23  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.94/1.23  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.94/1.23  tff(c_54, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.94/1.23  tff(c_46, plain, (![B_23]: (r1_tarski(k1_tarski(B_23), k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.23  tff(c_99, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.23  tff(c_110, plain, (![B_23]: (k4_xboole_0(k1_tarski(B_23), k1_tarski(B_23))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_99])).
% 1.94/1.23  tff(c_50, plain, (![B_25]: (k4_xboole_0(k1_tarski(B_25), k1_tarski(B_25))!=k1_tarski(B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.23  tff(c_126, plain, (![B_25]: (k1_tarski(B_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_50])).
% 1.94/1.23  tff(c_172, plain, (![A_52, B_53]: (k4_xboole_0(k1_tarski(A_52), k1_tarski(B_53))=k1_tarski(A_52) | B_53=A_52)), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.23  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.94/1.23  tff(c_182, plain, (k1_tarski('#skF_5')=k1_xboole_0 | '#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_172, c_56])).
% 1.94/1.23  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_126, c_182])).
% 1.94/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  Inference rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Ref     : 0
% 1.94/1.23  #Sup     : 30
% 1.94/1.23  #Fact    : 0
% 1.94/1.23  #Define  : 0
% 1.94/1.23  #Split   : 0
% 1.94/1.23  #Chain   : 0
% 1.94/1.23  #Close   : 0
% 1.94/1.23  
% 1.94/1.23  Ordering : KBO
% 1.94/1.23  
% 1.94/1.23  Simplification rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Subsume      : 1
% 1.94/1.23  #Demod        : 3
% 1.94/1.23  #Tautology    : 22
% 1.94/1.23  #SimpNegUnit  : 4
% 1.94/1.23  #BackRed      : 0
% 1.94/1.23  
% 1.94/1.23  #Partial instantiations: 0
% 1.94/1.23  #Strategies tried      : 1
% 1.94/1.23  
% 1.94/1.23  Timing (in seconds)
% 1.94/1.23  ----------------------
% 1.94/1.23  Preprocessing        : 0.32
% 1.94/1.23  Parsing              : 0.15
% 1.94/1.23  CNF conversion       : 0.02
% 1.94/1.23  Main loop            : 0.15
% 1.94/1.23  Inferencing          : 0.05
% 1.94/1.23  Reduction            : 0.05
% 1.94/1.23  Demodulation         : 0.04
% 1.94/1.23  BG Simplification    : 0.01
% 1.94/1.23  Subsumption          : 0.03
% 1.94/1.23  Abstraction          : 0.01
% 1.94/1.23  MUC search           : 0.00
% 1.94/1.23  Cooper               : 0.00
% 1.94/1.23  Total                : 0.49
% 1.94/1.23  Index Insertion      : 0.00
% 1.94/1.23  Index Deletion       : 0.00
% 1.94/1.23  Index Matching       : 0.00
% 1.94/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:48:49 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   23 (  32 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  36 expanded)
%              Number of equality atoms :   14 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_2,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k1_tarski(A_11)
      | B_12 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_49,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_16])).

tff(c_59,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_49])).

tff(c_8,plain,(
    ! [B_4] : ~ r1_xboole_0(k1_tarski(B_4),k1_tarski(B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_8])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_59,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.13  
% 1.59/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.13  %$ r1_xboole_0 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.59/1.13  
% 1.59/1.13  %Foreground sorts:
% 1.59/1.13  
% 1.59/1.13  
% 1.59/1.13  %Background operators:
% 1.59/1.13  
% 1.59/1.13  
% 1.59/1.13  %Foreground operators:
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.59/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.59/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.59/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.13  
% 1.59/1.14  tff(f_37, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.59/1.14  tff(f_54, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.59/1.14  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.59/1.14  tff(f_44, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.59/1.14  tff(c_2, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.59/1.14  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.59/1.14  tff(c_39, plain, (![A_11, B_12]: (k4_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k1_tarski(A_11) | B_12=A_11)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.59/1.14  tff(c_16, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.59/1.14  tff(c_49, plain, (k1_tarski('#skF_1')=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_39, c_16])).
% 1.59/1.14  tff(c_59, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14, c_49])).
% 1.59/1.14  tff(c_8, plain, (![B_4]: (~r1_xboole_0(k1_tarski(B_4), k1_tarski(B_4)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.59/1.14  tff(c_78, plain, (~r1_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_8])).
% 1.59/1.14  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_59, c_78])).
% 1.59/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.14  
% 1.59/1.14  Inference rules
% 1.59/1.14  ----------------------
% 1.59/1.14  #Ref     : 0
% 1.59/1.14  #Sup     : 18
% 1.59/1.14  #Fact    : 0
% 1.59/1.14  #Define  : 0
% 1.59/1.14  #Split   : 0
% 1.59/1.14  #Chain   : 0
% 1.59/1.14  #Close   : 0
% 1.59/1.14  
% 1.59/1.14  Ordering : KBO
% 1.59/1.14  
% 1.59/1.14  Simplification rules
% 1.59/1.14  ----------------------
% 1.59/1.14  #Subsume      : 0
% 1.59/1.14  #Demod        : 8
% 1.59/1.14  #Tautology    : 9
% 1.59/1.14  #SimpNegUnit  : 2
% 1.59/1.14  #BackRed      : 1
% 1.59/1.14  
% 1.59/1.14  #Partial instantiations: 0
% 1.59/1.14  #Strategies tried      : 1
% 1.59/1.14  
% 1.59/1.14  Timing (in seconds)
% 1.59/1.14  ----------------------
% 1.59/1.14  Preprocessing        : 0.26
% 1.59/1.14  Parsing              : 0.13
% 1.59/1.14  CNF conversion       : 0.01
% 1.59/1.14  Main loop            : 0.08
% 1.59/1.14  Inferencing          : 0.03
% 1.59/1.15  Reduction            : 0.03
% 1.59/1.15  Demodulation         : 0.01
% 1.59/1.15  BG Simplification    : 0.01
% 1.59/1.15  Subsumption          : 0.01
% 1.59/1.15  Abstraction          : 0.00
% 1.59/1.15  MUC search           : 0.00
% 1.59/1.15  Cooper               : 0.00
% 1.59/1.15  Total                : 0.35
% 1.59/1.15  Index Insertion      : 0.00
% 1.59/1.15  Index Deletion       : 0.00
% 1.59/1.15  Index Matching       : 0.00
% 1.59/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

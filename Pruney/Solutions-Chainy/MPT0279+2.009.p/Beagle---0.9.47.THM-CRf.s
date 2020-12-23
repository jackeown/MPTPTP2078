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
% DateTime   : Thu Dec  3 09:53:24 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_79,plain,(
    ! [C_26,A_27] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k1_tarski(A_20),B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ~ r2_hidden('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_26])).

tff(c_82,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_54])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.09  
% 1.58/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.09  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_2 > #skF_1
% 1.58/1.09  
% 1.58/1.09  %Foreground sorts:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Background operators:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Foreground operators:
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.58/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.58/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.58/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.58/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.58/1.09  
% 1.69/1.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.69/1.10  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.69/1.10  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.69/1.10  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.69/1.10  tff(f_47, negated_conjecture, ~(![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.69/1.10  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.10  tff(c_45, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.10  tff(c_48, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_45])).
% 1.69/1.10  tff(c_79, plain, (![C_26, A_27]: (r2_hidden(C_26, k1_zfmisc_1(A_27)) | ~r1_tarski(C_26, A_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.69/1.10  tff(c_50, plain, (![A_20, B_21]: (r1_tarski(k1_tarski(A_20), B_21) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.10  tff(c_26, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.69/1.10  tff(c_54, plain, (~r2_hidden('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_26])).
% 1.69/1.10  tff(c_82, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_79, c_54])).
% 1.69/1.10  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_82])).
% 1.69/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.10  
% 1.69/1.10  Inference rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Ref     : 0
% 1.69/1.10  #Sup     : 12
% 1.69/1.10  #Fact    : 0
% 1.69/1.10  #Define  : 0
% 1.69/1.10  #Split   : 0
% 1.69/1.10  #Chain   : 0
% 1.69/1.10  #Close   : 0
% 1.69/1.10  
% 1.69/1.10  Ordering : KBO
% 1.69/1.10  
% 1.69/1.10  Simplification rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Subsume      : 0
% 1.69/1.10  #Demod        : 1
% 1.69/1.10  #Tautology    : 7
% 1.69/1.10  #SimpNegUnit  : 0
% 1.69/1.10  #BackRed      : 0
% 1.69/1.10  
% 1.69/1.10  #Partial instantiations: 0
% 1.69/1.10  #Strategies tried      : 1
% 1.69/1.10  
% 1.69/1.10  Timing (in seconds)
% 1.69/1.10  ----------------------
% 1.69/1.10  Preprocessing        : 0.27
% 1.69/1.10  Parsing              : 0.14
% 1.69/1.10  CNF conversion       : 0.02
% 1.69/1.10  Main loop            : 0.08
% 1.69/1.10  Inferencing          : 0.03
% 1.69/1.10  Reduction            : 0.02
% 1.69/1.10  Demodulation         : 0.02
% 1.69/1.10  BG Simplification    : 0.01
% 1.69/1.10  Subsumption          : 0.01
% 1.69/1.10  Abstraction          : 0.01
% 1.69/1.10  MUC search           : 0.00
% 1.69/1.10  Cooper               : 0.00
% 1.69/1.10  Total                : 0.37
% 1.69/1.10  Index Insertion      : 0.00
% 1.69/1.10  Index Deletion       : 0.00
% 1.69/1.10  Index Matching       : 0.00
% 1.69/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:56 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  45 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_20,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_22,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(k1_mcart_1(A_23),B_24)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_63])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_65])).

tff(c_70,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_92,plain,(
    ! [A_31,C_32,B_33] :
      ( r2_hidden(k2_mcart_1(A_31),C_32)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_33,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_92])).

tff(c_102,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(k1_tarski(A_37),k1_tarski(B_38)) = k1_tarski(A_37)
      | B_38 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r2_hidden(B_10,A_9)
      | k4_xboole_0(A_9,k1_tarski(B_10)) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [B_42,A_43] :
      ( ~ r2_hidden(B_42,k1_tarski(A_43))
      | B_42 = A_43 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_12])).

tff(c_142,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_95,c_139])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.28  
% 1.69/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.29  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.69/1.29  
% 1.69/1.29  %Foreground sorts:
% 1.69/1.29  
% 1.69/1.29  
% 1.69/1.29  %Background operators:
% 1.69/1.29  
% 1.69/1.29  
% 1.69/1.29  %Foreground operators:
% 1.69/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.29  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.69/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.69/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.29  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.69/1.29  
% 1.69/1.29  tff(f_54, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.69/1.29  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.69/1.29  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.69/1.29  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.69/1.29  tff(c_20, plain, (k2_mcart_1('#skF_1')!='#skF_3' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.29  tff(c_42, plain, (~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 1.69/1.29  tff(c_22, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.29  tff(c_63, plain, (![A_23, B_24, C_25]: (r2_hidden(k1_mcart_1(A_23), B_24) | ~r2_hidden(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.69/1.29  tff(c_65, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_63])).
% 1.69/1.29  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_65])).
% 1.69/1.29  tff(c_70, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 1.69/1.29  tff(c_92, plain, (![A_31, C_32, B_33]: (r2_hidden(k2_mcart_1(A_31), C_32) | ~r2_hidden(A_31, k2_zfmisc_1(B_33, C_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.69/1.29  tff(c_95, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_92])).
% 1.69/1.29  tff(c_102, plain, (![A_37, B_38]: (k4_xboole_0(k1_tarski(A_37), k1_tarski(B_38))=k1_tarski(A_37) | B_38=A_37)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.69/1.29  tff(c_12, plain, (![B_10, A_9]: (~r2_hidden(B_10, A_9) | k4_xboole_0(A_9, k1_tarski(B_10))!=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.69/1.29  tff(c_139, plain, (![B_42, A_43]: (~r2_hidden(B_42, k1_tarski(A_43)) | B_42=A_43)), inference(superposition, [status(thm), theory('equality')], [c_102, c_12])).
% 1.69/1.29  tff(c_142, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_95, c_139])).
% 1.69/1.29  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_142])).
% 1.69/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.29  
% 1.69/1.29  Inference rules
% 1.69/1.29  ----------------------
% 1.69/1.29  #Ref     : 0
% 1.69/1.29  #Sup     : 25
% 1.69/1.29  #Fact    : 0
% 1.69/1.29  #Define  : 0
% 1.69/1.29  #Split   : 1
% 1.69/1.29  #Chain   : 0
% 1.69/1.29  #Close   : 0
% 1.69/1.29  
% 1.69/1.29  Ordering : KBO
% 1.69/1.29  
% 1.69/1.29  Simplification rules
% 1.69/1.29  ----------------------
% 1.69/1.29  #Subsume      : 0
% 1.69/1.29  #Demod        : 1
% 1.69/1.29  #Tautology    : 18
% 1.69/1.29  #SimpNegUnit  : 2
% 1.69/1.29  #BackRed      : 0
% 1.69/1.29  
% 1.69/1.29  #Partial instantiations: 0
% 1.69/1.29  #Strategies tried      : 1
% 1.69/1.29  
% 1.69/1.29  Timing (in seconds)
% 1.69/1.29  ----------------------
% 1.69/1.30  Preprocessing        : 0.28
% 1.69/1.30  Parsing              : 0.14
% 1.69/1.30  CNF conversion       : 0.02
% 1.69/1.30  Main loop            : 0.12
% 1.69/1.30  Inferencing          : 0.05
% 1.69/1.30  Reduction            : 0.03
% 1.69/1.30  Demodulation         : 0.02
% 1.69/1.30  BG Simplification    : 0.01
% 1.84/1.30  Subsumption          : 0.01
% 1.84/1.30  Abstraction          : 0.01
% 1.84/1.30  MUC search           : 0.00
% 1.84/1.30  Cooper               : 0.00
% 1.84/1.30  Total                : 0.43
% 1.84/1.30  Index Insertion      : 0.00
% 1.84/1.30  Index Deletion       : 0.00
% 1.84/1.30  Index Matching       : 0.00
% 1.84/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

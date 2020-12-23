%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:55 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  45 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_18,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden(k1_mcart_1(A_27),B_28)
      | ~ r2_hidden(A_27,k2_zfmisc_1(B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_49])).

tff(c_54,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_76,plain,(
    ! [A_40,C_41,B_42] :
      ( r2_hidden(k2_mcart_1(A_40),C_41)
      | ~ r2_hidden(A_40,k2_zfmisc_1(B_42,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_76])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(k1_tarski(A_13),k1_tarski(B_14))
      | B_14 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | ~ r1_xboole_0(k1_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden(A_13,k1_tarski(B_14))
      | B_14 = A_13 ) ),
    inference(resolution,[status(thm)],[c_12,c_56])).

tff(c_82,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_79,c_60])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.11  
% 1.69/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.11  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.69/1.11  
% 1.69/1.11  %Foreground sorts:
% 1.69/1.11  
% 1.69/1.11  
% 1.69/1.11  %Background operators:
% 1.69/1.11  
% 1.69/1.11  
% 1.69/1.11  %Foreground operators:
% 1.69/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.69/1.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.69/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.11  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.69/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.69/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.11  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.69/1.11  
% 1.69/1.11  tff(f_56, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.69/1.11  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.69/1.11  tff(f_43, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.69/1.11  tff(f_38, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.69/1.11  tff(c_18, plain, (k2_mcart_1('#skF_1')!='#skF_3' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.11  tff(c_40, plain, (~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 1.69/1.11  tff(c_20, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.11  tff(c_47, plain, (![A_27, B_28, C_29]: (r2_hidden(k1_mcart_1(A_27), B_28) | ~r2_hidden(A_27, k2_zfmisc_1(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.69/1.11  tff(c_49, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_47])).
% 1.69/1.11  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_49])).
% 1.69/1.11  tff(c_54, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_18])).
% 1.69/1.11  tff(c_76, plain, (![A_40, C_41, B_42]: (r2_hidden(k2_mcart_1(A_40), C_41) | ~r2_hidden(A_40, k2_zfmisc_1(B_42, C_41)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.69/1.11  tff(c_79, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_76])).
% 1.69/1.11  tff(c_12, plain, (![A_13, B_14]: (r1_xboole_0(k1_tarski(A_13), k1_tarski(B_14)) | B_14=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.69/1.11  tff(c_56, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | ~r1_xboole_0(k1_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.69/1.11  tff(c_60, plain, (![A_13, B_14]: (~r2_hidden(A_13, k1_tarski(B_14)) | B_14=A_13)), inference(resolution, [status(thm)], [c_12, c_56])).
% 1.69/1.11  tff(c_82, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_79, c_60])).
% 1.69/1.11  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_82])).
% 1.69/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.11  
% 1.69/1.12  Inference rules
% 1.69/1.12  ----------------------
% 1.69/1.12  #Ref     : 0
% 1.69/1.12  #Sup     : 12
% 1.69/1.12  #Fact    : 0
% 1.69/1.12  #Define  : 0
% 1.69/1.12  #Split   : 1
% 1.69/1.12  #Chain   : 0
% 1.69/1.12  #Close   : 0
% 1.69/1.12  
% 1.69/1.12  Ordering : KBO
% 1.69/1.12  
% 1.69/1.12  Simplification rules
% 1.69/1.12  ----------------------
% 1.69/1.12  #Subsume      : 0
% 1.69/1.12  #Demod        : 1
% 1.69/1.12  #Tautology    : 7
% 1.69/1.12  #SimpNegUnit  : 2
% 1.69/1.12  #BackRed      : 0
% 1.69/1.12  
% 1.69/1.12  #Partial instantiations: 0
% 1.69/1.12  #Strategies tried      : 1
% 1.69/1.12  
% 1.69/1.12  Timing (in seconds)
% 1.69/1.12  ----------------------
% 1.69/1.12  Preprocessing        : 0.27
% 1.69/1.12  Parsing              : 0.14
% 1.69/1.12  CNF conversion       : 0.02
% 1.69/1.12  Main loop            : 0.10
% 1.69/1.12  Inferencing          : 0.04
% 1.69/1.12  Reduction            : 0.03
% 1.69/1.12  Demodulation         : 0.02
% 1.69/1.12  BG Simplification    : 0.01
% 1.69/1.12  Subsumption          : 0.01
% 1.69/1.12  Abstraction          : 0.01
% 1.69/1.12  MUC search           : 0.00
% 1.69/1.12  Cooper               : 0.00
% 1.69/1.12  Total                : 0.39
% 1.69/1.12  Index Insertion      : 0.00
% 1.69/1.12  Index Deletion       : 0.00
% 1.69/1.12  Index Matching       : 0.00
% 1.69/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

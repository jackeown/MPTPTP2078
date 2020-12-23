%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:24 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [A_42,B_43] : r1_tarski(k3_xboole_0(A_42,B_43),A_42) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_55])).

tff(c_86,plain,(
    ! [C_54,A_55] :
      ( r2_hidden(C_54,k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_54,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tarski(A_50),B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_76,c_36])).

tff(c_92,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_84])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_2 > #skF_1
% 1.70/1.14  
% 1.70/1.14  %Foreground sorts:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Background operators:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Foreground operators:
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.70/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.14  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.70/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.14  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.14  
% 1.70/1.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.70/1.15  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.70/1.15  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.70/1.15  tff(f_54, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.70/1.15  tff(f_57, negated_conjecture, ~(![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.70/1.15  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.15  tff(c_55, plain, (![A_42, B_43]: (r1_tarski(k3_xboole_0(A_42, B_43), A_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.15  tff(c_58, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_55])).
% 1.70/1.15  tff(c_86, plain, (![C_54, A_55]: (r2_hidden(C_54, k1_zfmisc_1(A_55)) | ~r1_tarski(C_54, A_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.70/1.15  tff(c_76, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.70/1.15  tff(c_36, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.15  tff(c_84, plain, (~r2_hidden('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_76, c_36])).
% 1.70/1.15  tff(c_92, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_86, c_84])).
% 1.70/1.15  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_92])).
% 1.70/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  Inference rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Ref     : 0
% 1.70/1.15  #Sup     : 12
% 1.70/1.15  #Fact    : 0
% 1.70/1.15  #Define  : 0
% 1.70/1.15  #Split   : 0
% 1.70/1.15  #Chain   : 0
% 1.70/1.15  #Close   : 0
% 1.70/1.15  
% 1.70/1.15  Ordering : KBO
% 1.70/1.15  
% 1.70/1.15  Simplification rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Subsume      : 0
% 1.70/1.15  #Demod        : 1
% 1.70/1.15  #Tautology    : 8
% 1.70/1.15  #SimpNegUnit  : 0
% 1.70/1.15  #BackRed      : 0
% 1.70/1.15  
% 1.70/1.15  #Partial instantiations: 0
% 1.70/1.15  #Strategies tried      : 1
% 1.70/1.15  
% 1.70/1.15  Timing (in seconds)
% 1.70/1.15  ----------------------
% 1.70/1.15  Preprocessing        : 0.31
% 1.70/1.15  Parsing              : 0.16
% 1.70/1.15  CNF conversion       : 0.02
% 1.70/1.15  Main loop            : 0.09
% 1.70/1.15  Inferencing          : 0.03
% 1.70/1.15  Reduction            : 0.03
% 1.70/1.15  Demodulation         : 0.02
% 1.70/1.15  BG Simplification    : 0.02
% 1.70/1.15  Subsumption          : 0.02
% 1.70/1.15  Abstraction          : 0.01
% 1.70/1.15  MUC search           : 0.00
% 1.70/1.15  Cooper               : 0.00
% 1.70/1.15  Total                : 0.42
% 1.70/1.15  Index Insertion      : 0.00
% 1.70/1.15  Index Deletion       : 0.00
% 1.70/1.15  Index Matching       : 0.00
% 1.70/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

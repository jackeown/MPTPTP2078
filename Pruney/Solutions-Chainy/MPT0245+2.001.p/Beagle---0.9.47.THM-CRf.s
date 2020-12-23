%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:59 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  33 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => ( r2_hidden(C,A)
          | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_20,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_33,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(k1_tarski(A_23),B_24)
      | r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( r1_xboole_0(B_24,k1_tarski(A_23))
      | r2_hidden(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_33,c_2])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_tarski(A_34,k4_xboole_0(B_35,C_36))
      | ~ r1_xboole_0(A_34,C_36)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2',k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_71,plain,
    ( ~ r1_xboole_0('#skF_1',k1_tarski('#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_18])).

tff(c_74,plain,(
    ~ r1_xboole_0('#skF_1',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_71])).

tff(c_77,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_74])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 13:43:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.66/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.66/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.13  
% 1.66/1.14  tff(f_57, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_zfmisc_1)).
% 1.66/1.14  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.66/1.14  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.66/1.14  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 1.66/1.14  tff(c_20, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.66/1.14  tff(c_33, plain, (![A_23, B_24]: (r1_xboole_0(k1_tarski(A_23), B_24) | r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.66/1.14  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.14  tff(c_36, plain, (![B_24, A_23]: (r1_xboole_0(B_24, k1_tarski(A_23)) | r2_hidden(A_23, B_24))), inference(resolution, [status(thm)], [c_33, c_2])).
% 1.66/1.14  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.66/1.14  tff(c_68, plain, (![A_34, B_35, C_36]: (r1_tarski(A_34, k4_xboole_0(B_35, C_36)) | ~r1_xboole_0(A_34, C_36) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.14  tff(c_18, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.66/1.14  tff(c_71, plain, (~r1_xboole_0('#skF_1', k1_tarski('#skF_3')) | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_18])).
% 1.66/1.14  tff(c_74, plain, (~r1_xboole_0('#skF_1', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_71])).
% 1.66/1.14  tff(c_77, plain, (r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_74])).
% 1.66/1.14  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_77])).
% 1.66/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  Inference rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Ref     : 0
% 1.66/1.14  #Sup     : 12
% 1.66/1.14  #Fact    : 0
% 1.66/1.14  #Define  : 0
% 1.66/1.14  #Split   : 0
% 1.66/1.14  #Chain   : 0
% 1.66/1.14  #Close   : 0
% 1.66/1.14  
% 1.66/1.14  Ordering : KBO
% 1.66/1.14  
% 1.66/1.14  Simplification rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Subsume      : 1
% 1.66/1.14  #Demod        : 1
% 1.66/1.14  #Tautology    : 8
% 1.66/1.14  #SimpNegUnit  : 1
% 1.66/1.14  #BackRed      : 0
% 1.66/1.14  
% 1.66/1.14  #Partial instantiations: 0
% 1.66/1.14  #Strategies tried      : 1
% 1.66/1.14  
% 1.66/1.14  Timing (in seconds)
% 1.66/1.14  ----------------------
% 1.66/1.14  Preprocessing        : 0.29
% 1.66/1.14  Parsing              : 0.15
% 1.66/1.14  CNF conversion       : 0.02
% 1.66/1.14  Main loop            : 0.10
% 1.66/1.14  Inferencing          : 0.04
% 1.66/1.14  Reduction            : 0.03
% 1.66/1.14  Demodulation         : 0.02
% 1.66/1.14  BG Simplification    : 0.01
% 1.66/1.14  Subsumption          : 0.01
% 1.66/1.14  Abstraction          : 0.01
% 1.66/1.14  MUC search           : 0.00
% 1.66/1.14  Cooper               : 0.00
% 1.66/1.14  Total                : 0.40
% 1.66/1.14  Index Insertion      : 0.00
% 1.66/1.14  Index Deletion       : 0.00
% 1.66/1.14  Index Matching       : 0.00
% 1.66/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

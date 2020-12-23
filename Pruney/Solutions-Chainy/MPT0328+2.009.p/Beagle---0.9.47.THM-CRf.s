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
% DateTime   : Thu Dec  3 09:54:39 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_16,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(k1_tarski(A_13),B_14)
      | r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_21,plain,(
    ! [B_14,A_13] :
      ( r1_xboole_0(B_14,k1_tarski(A_13))
      | r2_hidden(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_2])).

tff(c_52,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(k2_xboole_0(A_23,B_24),B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ~ r1_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_70,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_21,c_66])).

tff(c_74,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.11  
% 1.59/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.11  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.59/1.11  
% 1.59/1.11  %Foreground sorts:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Background operators:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Foreground operators:
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.59/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.59/1.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.59/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.11  
% 1.59/1.12  tff(f_51, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.59/1.12  tff(f_40, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.59/1.12  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.59/1.12  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 1.59/1.12  tff(c_16, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.59/1.12  tff(c_18, plain, (![A_13, B_14]: (r1_xboole_0(k1_tarski(A_13), B_14) | r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.59/1.12  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.12  tff(c_21, plain, (![B_14, A_13]: (r1_xboole_0(B_14, k1_tarski(A_13)) | r2_hidden(A_13, B_14))), inference(resolution, [status(thm)], [c_18, c_2])).
% 1.59/1.12  tff(c_52, plain, (![A_23, B_24]: (k4_xboole_0(k2_xboole_0(A_23, B_24), B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.59/1.12  tff(c_14, plain, (k4_xboole_0(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.59/1.12  tff(c_66, plain, (~r1_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_14])).
% 1.59/1.12  tff(c_70, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_21, c_66])).
% 1.59/1.12  tff(c_74, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_70])).
% 1.59/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  Inference rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Ref     : 0
% 1.59/1.12  #Sup     : 13
% 1.59/1.12  #Fact    : 0
% 1.59/1.12  #Define  : 0
% 1.59/1.12  #Split   : 0
% 1.59/1.12  #Chain   : 0
% 1.59/1.12  #Close   : 0
% 1.59/1.12  
% 1.59/1.12  Ordering : KBO
% 1.59/1.12  
% 1.59/1.12  Simplification rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Subsume      : 1
% 1.59/1.12  #Demod        : 0
% 1.59/1.12  #Tautology    : 7
% 1.59/1.12  #SimpNegUnit  : 1
% 1.59/1.12  #BackRed      : 0
% 1.59/1.12  
% 1.59/1.12  #Partial instantiations: 0
% 1.59/1.12  #Strategies tried      : 1
% 1.59/1.12  
% 1.59/1.12  Timing (in seconds)
% 1.59/1.12  ----------------------
% 1.59/1.12  Preprocessing        : 0.25
% 1.59/1.12  Parsing              : 0.14
% 1.59/1.12  CNF conversion       : 0.02
% 1.59/1.12  Main loop            : 0.10
% 1.59/1.12  Inferencing          : 0.05
% 1.59/1.12  Reduction            : 0.02
% 1.59/1.12  Demodulation         : 0.01
% 1.59/1.12  BG Simplification    : 0.01
% 1.59/1.12  Subsumption          : 0.01
% 1.59/1.12  Abstraction          : 0.01
% 1.59/1.12  MUC search           : 0.00
% 1.59/1.12  Cooper               : 0.00
% 1.59/1.12  Total                : 0.37
% 1.59/1.13  Index Insertion      : 0.00
% 1.59/1.13  Index Deletion       : 0.00
% 1.59/1.13  Index Matching       : 0.00
% 1.59/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

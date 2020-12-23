%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:15 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_16,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_setfam_1(B_8),A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    ! [A_16,C_17,B_18,D_19] :
      ( r1_xboole_0(A_16,C_17)
      | ~ r1_xboole_0(B_18,D_19)
      | ~ r1_tarski(C_17,D_19)
      | ~ r1_tarski(A_16,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_20,C_21] :
      ( r1_xboole_0(A_20,C_21)
      | ~ r1_tarski(C_21,'#skF_3')
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_42])).

tff(c_12,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_51,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_12])).

tff(c_55,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_51])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.08  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.62/1.08  
% 1.62/1.08  %Foreground sorts:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Background operators:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Foreground operators:
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.62/1.08  
% 1.62/1.09  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 1.62/1.09  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.62/1.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.62/1.09  tff(f_39, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 1.62/1.09  tff(c_16, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.62/1.09  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k1_setfam_1(B_8), A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.62/1.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.09  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.62/1.09  tff(c_42, plain, (![A_16, C_17, B_18, D_19]: (r1_xboole_0(A_16, C_17) | ~r1_xboole_0(B_18, D_19) | ~r1_tarski(C_17, D_19) | ~r1_tarski(A_16, B_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.62/1.09  tff(c_46, plain, (![A_20, C_21]: (r1_xboole_0(A_20, C_21) | ~r1_tarski(C_21, '#skF_3') | ~r1_tarski(A_20, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_42])).
% 1.62/1.09  tff(c_12, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.62/1.09  tff(c_51, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_46, c_12])).
% 1.62/1.09  tff(c_55, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_51])).
% 1.62/1.09  tff(c_58, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_55])).
% 1.62/1.09  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 1.62/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  Inference rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Ref     : 0
% 1.62/1.09  #Sup     : 8
% 1.62/1.09  #Fact    : 0
% 1.62/1.09  #Define  : 0
% 1.62/1.09  #Split   : 0
% 1.62/1.09  #Chain   : 0
% 1.62/1.09  #Close   : 0
% 1.62/1.09  
% 1.62/1.09  Ordering : KBO
% 1.62/1.09  
% 1.62/1.09  Simplification rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Subsume      : 0
% 1.62/1.09  #Demod        : 4
% 1.62/1.09  #Tautology    : 3
% 1.62/1.09  #SimpNegUnit  : 0
% 1.62/1.09  #BackRed      : 0
% 1.62/1.09  
% 1.62/1.09  #Partial instantiations: 0
% 1.62/1.09  #Strategies tried      : 1
% 1.62/1.09  
% 1.62/1.09  Timing (in seconds)
% 1.62/1.09  ----------------------
% 1.62/1.09  Preprocessing        : 0.25
% 1.62/1.09  Parsing              : 0.14
% 1.62/1.09  CNF conversion       : 0.02
% 1.62/1.09  Main loop            : 0.09
% 1.62/1.09  Inferencing          : 0.04
% 1.62/1.09  Reduction            : 0.02
% 1.62/1.09  Demodulation         : 0.02
% 1.62/1.09  BG Simplification    : 0.01
% 1.62/1.09  Subsumption          : 0.02
% 1.62/1.09  Abstraction          : 0.00
% 1.62/1.09  MUC search           : 0.00
% 1.62/1.09  Cooper               : 0.00
% 1.62/1.09  Total                : 0.36
% 1.62/1.09  Index Insertion      : 0.00
% 1.62/1.09  Index Deletion       : 0.00
% 1.62/1.09  Index Matching       : 0.00
% 1.62/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

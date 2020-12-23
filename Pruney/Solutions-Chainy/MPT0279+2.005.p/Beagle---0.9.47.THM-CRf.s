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
% DateTime   : Thu Dec  3 09:53:23 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [C_8,A_4] :
      ( r2_hidden(C_8,k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_33,B_34,C_35] :
      ( r1_tarski(k2_tarski(A_33,B_34),C_35)
      | ~ r2_hidden(B_34,C_35)
      | ~ r2_hidden(A_33,C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    ! [A_36,C_37] :
      ( r1_tarski(k1_tarski(A_36),C_37)
      | ~ r2_hidden(A_36,C_37)
      | ~ r2_hidden(A_36,C_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_28,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_114,plain,(
    ~ r2_hidden('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_103,c_28])).

tff(c_117,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_114])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:32:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.15  %$ r2_hidden > r1_tarski > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_2 > #skF_1
% 1.60/1.15  
% 1.60/1.15  %Foreground sorts:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Background operators:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Foreground operators:
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.60/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.60/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.60/1.15  
% 1.60/1.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.60/1.16  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.60/1.16  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.60/1.16  tff(f_46, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.60/1.16  tff(f_49, negated_conjecture, ~(![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.60/1.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.16  tff(c_12, plain, (![C_8, A_4]: (r2_hidden(C_8, k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.16  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.16  tff(c_88, plain, (![A_33, B_34, C_35]: (r1_tarski(k2_tarski(A_33, B_34), C_35) | ~r2_hidden(B_34, C_35) | ~r2_hidden(A_33, C_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.60/1.16  tff(c_103, plain, (![A_36, C_37]: (r1_tarski(k1_tarski(A_36), C_37) | ~r2_hidden(A_36, C_37) | ~r2_hidden(A_36, C_37))), inference(superposition, [status(thm), theory('equality')], [c_8, c_88])).
% 1.60/1.16  tff(c_28, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.60/1.16  tff(c_114, plain, (~r2_hidden('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_103, c_28])).
% 1.60/1.16  tff(c_117, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_114])).
% 1.60/1.16  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_117])).
% 1.60/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  Inference rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Ref     : 0
% 1.60/1.16  #Sup     : 19
% 1.60/1.16  #Fact    : 0
% 1.60/1.16  #Define  : 0
% 1.60/1.16  #Split   : 0
% 1.60/1.16  #Chain   : 0
% 1.60/1.16  #Close   : 0
% 1.60/1.16  
% 1.60/1.16  Ordering : KBO
% 1.60/1.16  
% 1.60/1.16  Simplification rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Subsume      : 1
% 1.60/1.16  #Demod        : 5
% 1.60/1.16  #Tautology    : 10
% 1.60/1.16  #SimpNegUnit  : 0
% 1.60/1.16  #BackRed      : 0
% 1.60/1.16  
% 1.60/1.16  #Partial instantiations: 0
% 1.60/1.16  #Strategies tried      : 1
% 1.60/1.16  
% 1.60/1.16  Timing (in seconds)
% 1.60/1.16  ----------------------
% 1.60/1.16  Preprocessing        : 0.28
% 1.60/1.16  Parsing              : 0.14
% 1.60/1.16  CNF conversion       : 0.02
% 1.60/1.16  Main loop            : 0.11
% 1.60/1.16  Inferencing          : 0.04
% 1.60/1.16  Reduction            : 0.03
% 1.60/1.16  Demodulation         : 0.03
% 1.60/1.16  BG Simplification    : 0.01
% 1.60/1.16  Subsumption          : 0.02
% 1.60/1.16  Abstraction          : 0.01
% 1.60/1.16  MUC search           : 0.00
% 1.60/1.16  Cooper               : 0.00
% 1.60/1.16  Total                : 0.41
% 1.60/1.16  Index Insertion      : 0.00
% 1.60/1.16  Index Deletion       : 0.00
% 1.60/1.16  Index Matching       : 0.00
% 1.60/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

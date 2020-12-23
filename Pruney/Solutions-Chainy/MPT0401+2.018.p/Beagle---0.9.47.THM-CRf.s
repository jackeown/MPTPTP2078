%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:40 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  40 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_16] : k3_tarski(k1_tarski(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    r1_setfam_1('#skF_2',k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k3_tarski(A_17),k3_tarski(B_18))
      | ~ r1_setfam_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,C_31)
      | ~ r1_tarski(B_32,C_31)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_49,B_50,A_51] :
      ( r1_tarski(A_49,k3_tarski(B_50))
      | ~ r1_tarski(A_49,k3_tarski(A_51))
      | ~ r1_setfam_1(A_51,B_50) ) ),
    inference(resolution,[status(thm)],[c_16,c_62])).

tff(c_131,plain,(
    ! [A_52,B_53,B_54] :
      ( r1_tarski(A_52,k3_tarski(B_53))
      | ~ r1_setfam_1(B_54,B_53)
      | ~ r2_hidden(A_52,B_54) ) ),
    inference(resolution,[status(thm)],[c_12,c_115])).

tff(c_133,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,k3_tarski(k1_tarski('#skF_1')))
      | ~ r2_hidden(A_52,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_131])).

tff(c_136,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,'#skF_1')
      | ~ r2_hidden(A_55,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_139,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_136])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:25:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.69/1.16  
% 1.69/1.16  %Foreground sorts:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Background operators:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Foreground operators:
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.16  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.69/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.69/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.16  
% 1.69/1.16  tff(f_57, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 1.69/1.16  tff(f_45, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 1.69/1.16  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.69/1.16  tff(f_49, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 1.69/1.16  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.69/1.16  tff(c_18, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.69/1.16  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.69/1.16  tff(c_14, plain, (![A_16]: (k3_tarski(k1_tarski(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.69/1.16  tff(c_22, plain, (r1_setfam_1('#skF_2', k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.69/1.16  tff(c_12, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.69/1.16  tff(c_16, plain, (![A_17, B_18]: (r1_tarski(k3_tarski(A_17), k3_tarski(B_18)) | ~r1_setfam_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.69/1.16  tff(c_62, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, C_31) | ~r1_tarski(B_32, C_31) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.16  tff(c_115, plain, (![A_49, B_50, A_51]: (r1_tarski(A_49, k3_tarski(B_50)) | ~r1_tarski(A_49, k3_tarski(A_51)) | ~r1_setfam_1(A_51, B_50))), inference(resolution, [status(thm)], [c_16, c_62])).
% 1.69/1.16  tff(c_131, plain, (![A_52, B_53, B_54]: (r1_tarski(A_52, k3_tarski(B_53)) | ~r1_setfam_1(B_54, B_53) | ~r2_hidden(A_52, B_54))), inference(resolution, [status(thm)], [c_12, c_115])).
% 1.69/1.16  tff(c_133, plain, (![A_52]: (r1_tarski(A_52, k3_tarski(k1_tarski('#skF_1'))) | ~r2_hidden(A_52, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_131])).
% 1.69/1.16  tff(c_136, plain, (![A_55]: (r1_tarski(A_55, '#skF_1') | ~r2_hidden(A_55, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_133])).
% 1.69/1.16  tff(c_139, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_136])).
% 1.69/1.16  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_139])).
% 1.69/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  
% 1.69/1.16  Inference rules
% 1.69/1.16  ----------------------
% 1.69/1.16  #Ref     : 0
% 1.69/1.16  #Sup     : 30
% 1.69/1.16  #Fact    : 0
% 1.69/1.16  #Define  : 0
% 1.69/1.16  #Split   : 0
% 1.69/1.16  #Chain   : 0
% 1.89/1.16  #Close   : 0
% 1.89/1.16  
% 1.89/1.16  Ordering : KBO
% 1.89/1.16  
% 1.89/1.16  Simplification rules
% 1.89/1.16  ----------------------
% 1.89/1.16  #Subsume      : 1
% 1.89/1.16  #Demod        : 1
% 1.89/1.16  #Tautology    : 10
% 1.89/1.16  #SimpNegUnit  : 1
% 1.89/1.16  #BackRed      : 0
% 1.89/1.16  
% 1.89/1.16  #Partial instantiations: 0
% 1.89/1.16  #Strategies tried      : 1
% 1.89/1.16  
% 1.89/1.16  Timing (in seconds)
% 1.89/1.16  ----------------------
% 1.89/1.17  Preprocessing        : 0.28
% 1.89/1.17  Parsing              : 0.15
% 1.89/1.17  CNF conversion       : 0.02
% 1.89/1.17  Main loop            : 0.13
% 1.89/1.17  Inferencing          : 0.05
% 1.89/1.17  Reduction            : 0.03
% 1.89/1.17  Demodulation         : 0.02
% 1.89/1.17  BG Simplification    : 0.01
% 1.89/1.17  Subsumption          : 0.02
% 1.89/1.17  Abstraction          : 0.01
% 1.89/1.17  MUC search           : 0.00
% 1.89/1.17  Cooper               : 0.00
% 1.89/1.17  Total                : 0.43
% 1.89/1.17  Index Insertion      : 0.00
% 1.89/1.17  Index Deletion       : 0.00
% 1.89/1.17  Index Matching       : 0.00
% 1.89/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

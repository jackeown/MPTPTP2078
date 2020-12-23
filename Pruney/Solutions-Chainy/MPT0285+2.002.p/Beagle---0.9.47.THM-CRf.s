%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:30 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_6,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ~ r1_tarski('#skF_1',k3_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_7,c_4])).

tff(c_14,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.03  
% 1.49/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.04  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_2 > #skF_1
% 1.49/1.04  
% 1.49/1.04  %Foreground sorts:
% 1.49/1.04  
% 1.49/1.04  
% 1.49/1.04  %Background operators:
% 1.49/1.04  
% 1.49/1.04  
% 1.49/1.04  %Foreground operators:
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.49/1.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.49/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.05  
% 1.49/1.05  tff(f_34, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 1.49/1.05  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.49/1.05  tff(c_6, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.49/1.05  tff(c_7, plain, (![A_3, B_4]: (r1_tarski(A_3, k3_tarski(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.49/1.05  tff(c_4, plain, (~r1_tarski('#skF_1', k3_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.49/1.05  tff(c_10, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_7, c_4])).
% 1.49/1.05  tff(c_14, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.49/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.05  
% 1.49/1.05  Inference rules
% 1.49/1.05  ----------------------
% 1.49/1.05  #Ref     : 0
% 1.49/1.05  #Sup     : 1
% 1.49/1.05  #Fact    : 0
% 1.49/1.05  #Define  : 0
% 1.49/1.05  #Split   : 0
% 1.49/1.05  #Chain   : 0
% 1.49/1.05  #Close   : 0
% 1.49/1.05  
% 1.49/1.05  Ordering : KBO
% 1.49/1.05  
% 1.49/1.05  Simplification rules
% 1.49/1.05  ----------------------
% 1.49/1.05  #Subsume      : 0
% 1.49/1.05  #Demod        : 1
% 1.49/1.05  #Tautology    : 0
% 1.49/1.05  #SimpNegUnit  : 0
% 1.49/1.05  #BackRed      : 0
% 1.49/1.05  
% 1.49/1.05  #Partial instantiations: 0
% 1.49/1.05  #Strategies tried      : 1
% 1.49/1.05  
% 1.49/1.05  Timing (in seconds)
% 1.49/1.05  ----------------------
% 1.49/1.05  Preprocessing        : 0.24
% 1.49/1.05  Parsing              : 0.14
% 1.49/1.05  CNF conversion       : 0.01
% 1.49/1.05  Main loop            : 0.05
% 1.49/1.06  Inferencing          : 0.03
% 1.49/1.06  Reduction            : 0.01
% 1.49/1.06  Demodulation         : 0.01
% 1.49/1.06  BG Simplification    : 0.01
% 1.49/1.06  Subsumption          : 0.00
% 1.49/1.06  Abstraction          : 0.00
% 1.49/1.06  MUC search           : 0.00
% 1.49/1.06  Cooper               : 0.00
% 1.49/1.06  Total                : 0.32
% 1.49/1.06  Index Insertion      : 0.00
% 1.49/1.06  Index Deletion       : 0.00
% 1.49/1.06  Index Matching       : 0.00
% 1.49/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------

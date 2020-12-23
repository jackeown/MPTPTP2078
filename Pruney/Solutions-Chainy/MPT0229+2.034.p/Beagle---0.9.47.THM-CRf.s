%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:57 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   14 (  15 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_4,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7,plain,(
    ! [B_3,A_4] :
      ( B_3 = A_4
      | ~ r1_tarski(k1_tarski(A_4),k1_tarski(B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_7])).

tff(c_14,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:28:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.08  
% 1.52/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.08  %$ r1_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.52/1.08  
% 1.52/1.08  %Foreground sorts:
% 1.52/1.08  
% 1.52/1.08  
% 1.52/1.08  %Background operators:
% 1.52/1.08  
% 1.52/1.08  
% 1.52/1.08  %Foreground operators:
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.52/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.52/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.08  
% 1.52/1.08  tff(f_34, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.52/1.08  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.52/1.08  tff(c_4, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.52/1.08  tff(c_6, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.52/1.08  tff(c_7, plain, (![B_3, A_4]: (B_3=A_4 | ~r1_tarski(k1_tarski(A_4), k1_tarski(B_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.52/1.08  tff(c_10, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_6, c_7])).
% 1.52/1.08  tff(c_14, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_10])).
% 1.52/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.08  
% 1.52/1.08  Inference rules
% 1.52/1.08  ----------------------
% 1.52/1.08  #Ref     : 0
% 1.52/1.08  #Sup     : 1
% 1.52/1.08  #Fact    : 0
% 1.52/1.08  #Define  : 0
% 1.52/1.08  #Split   : 0
% 1.52/1.08  #Chain   : 0
% 1.52/1.08  #Close   : 0
% 1.52/1.08  
% 1.52/1.08  Ordering : KBO
% 1.52/1.08  
% 1.52/1.08  Simplification rules
% 1.52/1.08  ----------------------
% 1.52/1.08  #Subsume      : 0
% 1.52/1.08  #Demod        : 0
% 1.52/1.08  #Tautology    : 0
% 1.52/1.08  #SimpNegUnit  : 1
% 1.52/1.08  #BackRed      : 0
% 1.52/1.08  
% 1.52/1.08  #Partial instantiations: 0
% 1.52/1.08  #Strategies tried      : 1
% 1.52/1.08  
% 1.52/1.08  Timing (in seconds)
% 1.52/1.08  ----------------------
% 1.52/1.09  Preprocessing        : 0.23
% 1.52/1.09  Parsing              : 0.12
% 1.52/1.09  CNF conversion       : 0.01
% 1.52/1.09  Main loop            : 0.05
% 1.52/1.09  Inferencing          : 0.02
% 1.52/1.09  Reduction            : 0.01
% 1.52/1.09  Demodulation         : 0.01
% 1.52/1.09  BG Simplification    : 0.01
% 1.52/1.09  Subsumption          : 0.00
% 1.52/1.09  Abstraction          : 0.00
% 1.52/1.09  MUC search           : 0.00
% 1.52/1.09  Cooper               : 0.00
% 1.52/1.09  Total                : 0.30
% 1.52/1.09  Index Insertion      : 0.00
% 1.52/1.09  Index Deletion       : 0.00
% 1.52/1.09  Index Matching       : 0.00
% 1.52/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

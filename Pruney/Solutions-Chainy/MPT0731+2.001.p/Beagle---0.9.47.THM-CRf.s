%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:00 EST 2020

% Result     : Theorem 1.43s
% Output     : CNFRefutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  16 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > #nlpp > k1_ordinal1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_36,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_32,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_6,plain,(
    k1_ordinal1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    ! [A_4] : r2_hidden(A_4,k1_ordinal1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_11])).

tff(c_15,plain,(
    ! [B_5,A_6] :
      ( ~ r2_hidden(B_5,A_6)
      | ~ r2_hidden(A_6,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_17,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_15])).

tff(c_23,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:50:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.43/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.43/1.13  
% 1.43/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.43/1.14  %$ r2_hidden > #nlpp > k1_ordinal1 > #skF_1
% 1.43/1.14  
% 1.43/1.14  %Foreground sorts:
% 1.43/1.14  
% 1.43/1.14  
% 1.43/1.14  %Background operators:
% 1.43/1.14  
% 1.43/1.14  
% 1.43/1.14  %Foreground operators:
% 1.43/1.14  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.43/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.43/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.43/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.43/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.43/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.43/1.14  
% 1.43/1.14  tff(f_36, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 1.43/1.14  tff(f_32, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.43/1.14  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 1.43/1.14  tff(c_6, plain, (k1_ordinal1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.43/1.14  tff(c_11, plain, (![A_4]: (r2_hidden(A_4, k1_ordinal1(A_4)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.43/1.14  tff(c_14, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_11])).
% 1.43/1.14  tff(c_15, plain, (![B_5, A_6]: (~r2_hidden(B_5, A_6) | ~r2_hidden(A_6, B_5))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.43/1.14  tff(c_17, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_15])).
% 1.43/1.14  tff(c_23, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_17])).
% 1.43/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.43/1.14  
% 1.43/1.14  Inference rules
% 1.43/1.14  ----------------------
% 1.43/1.14  #Ref     : 0
% 1.43/1.14  #Sup     : 5
% 1.43/1.14  #Fact    : 0
% 1.43/1.14  #Define  : 0
% 1.43/1.14  #Split   : 0
% 1.43/1.14  #Chain   : 0
% 1.43/1.14  #Close   : 0
% 1.43/1.14  
% 1.43/1.14  Ordering : KBO
% 1.43/1.14  
% 1.43/1.14  Simplification rules
% 1.43/1.14  ----------------------
% 1.43/1.14  #Subsume      : 0
% 1.43/1.14  #Demod        : 1
% 1.43/1.14  #Tautology    : 2
% 1.43/1.14  #SimpNegUnit  : 0
% 1.43/1.14  #BackRed      : 0
% 1.43/1.14  
% 1.43/1.14  #Partial instantiations: 0
% 1.43/1.14  #Strategies tried      : 1
% 1.43/1.14  
% 1.43/1.14  Timing (in seconds)
% 1.43/1.14  ----------------------
% 1.43/1.15  Preprocessing        : 0.22
% 1.43/1.15  Parsing              : 0.11
% 1.43/1.15  CNF conversion       : 0.01
% 1.43/1.15  Main loop            : 0.05
% 1.43/1.15  Inferencing          : 0.02
% 1.43/1.15  Reduction            : 0.01
% 1.43/1.15  Demodulation         : 0.01
% 1.43/1.15  BG Simplification    : 0.01
% 1.43/1.15  Subsumption          : 0.00
% 1.43/1.15  Abstraction          : 0.00
% 1.43/1.15  MUC search           : 0.00
% 1.43/1.15  Cooper               : 0.00
% 1.43/1.15  Total                : 0.30
% 1.43/1.15  Index Insertion      : 0.00
% 1.43/1.15  Index Deletion       : 0.00
% 1.43/1.15  Index Matching       : 0.00
% 1.43/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

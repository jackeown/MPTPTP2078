%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:41 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  34 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_10,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k1_tarski(A_4),k2_tarski(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_11,C_12,B_13] :
      ( r1_tarski(A_11,C_12)
      | ~ r1_tarski(B_13,C_12)
      | ~ r1_tarski(A_11,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,k2_tarski('#skF_3','#skF_4'))
      | ~ r1_tarski(A_23,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_14])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( C_8 = A_6
      | B_7 = A_6
      | ~ r1_tarski(k1_tarski(A_6),k2_tarski(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    ! [A_24] :
      ( A_24 = '#skF_4'
      | A_24 = '#skF_3'
      | ~ r1_tarski(k1_tarski(A_24),k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_37,c_6])).

tff(c_53,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_46])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_8,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.09  
% 1.65/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.09  %$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.65/1.09  
% 1.65/1.09  %Foreground sorts:
% 1.65/1.09  
% 1.65/1.09  
% 1.65/1.09  %Background operators:
% 1.65/1.09  
% 1.65/1.09  
% 1.65/1.09  %Foreground operators:
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.09  
% 1.65/1.10  tff(f_52, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.65/1.10  tff(f_33, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.65/1.10  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.65/1.10  tff(f_42, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.65/1.10  tff(c_10, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.10  tff(c_8, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.10  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), k2_tarski(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.10  tff(c_12, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.10  tff(c_14, plain, (![A_11, C_12, B_13]: (r1_tarski(A_11, C_12) | ~r1_tarski(B_13, C_12) | ~r1_tarski(A_11, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.10  tff(c_37, plain, (![A_23]: (r1_tarski(A_23, k2_tarski('#skF_3', '#skF_4')) | ~r1_tarski(A_23, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_12, c_14])).
% 1.65/1.10  tff(c_6, plain, (![C_8, A_6, B_7]: (C_8=A_6 | B_7=A_6 | ~r1_tarski(k1_tarski(A_6), k2_tarski(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.65/1.10  tff(c_46, plain, (![A_24]: (A_24='#skF_4' | A_24='#skF_3' | ~r1_tarski(k1_tarski(A_24), k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_37, c_6])).
% 1.65/1.10  tff(c_53, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_4, c_46])).
% 1.65/1.10  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_8, c_53])).
% 1.65/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.10  
% 1.65/1.10  Inference rules
% 1.65/1.10  ----------------------
% 1.65/1.10  #Ref     : 0
% 1.65/1.10  #Sup     : 9
% 1.65/1.10  #Fact    : 0
% 1.65/1.10  #Define  : 0
% 1.65/1.10  #Split   : 0
% 1.65/1.10  #Chain   : 0
% 1.65/1.10  #Close   : 0
% 1.65/1.10  
% 1.65/1.10  Ordering : KBO
% 1.65/1.10  
% 1.65/1.10  Simplification rules
% 1.65/1.10  ----------------------
% 1.65/1.10  #Subsume      : 0
% 1.65/1.10  #Demod        : 0
% 1.65/1.10  #Tautology    : 1
% 1.65/1.10  #SimpNegUnit  : 1
% 1.65/1.10  #BackRed      : 0
% 1.65/1.10  
% 1.65/1.10  #Partial instantiations: 0
% 1.65/1.10  #Strategies tried      : 1
% 1.65/1.10  
% 1.65/1.10  Timing (in seconds)
% 1.65/1.10  ----------------------
% 1.65/1.10  Preprocessing        : 0.25
% 1.65/1.10  Parsing              : 0.14
% 1.65/1.10  CNF conversion       : 0.02
% 1.65/1.10  Main loop            : 0.10
% 1.65/1.10  Inferencing          : 0.04
% 1.65/1.10  Reduction            : 0.02
% 1.65/1.10  Demodulation         : 0.01
% 1.65/1.10  BG Simplification    : 0.01
% 1.65/1.11  Subsumption          : 0.02
% 1.65/1.11  Abstraction          : 0.00
% 1.65/1.11  MUC search           : 0.00
% 1.65/1.11  Cooper               : 0.00
% 1.65/1.11  Total                : 0.37
% 1.65/1.11  Index Insertion      : 0.00
% 1.65/1.11  Index Deletion       : 0.00
% 1.65/1.11  Index Matching       : 0.00
% 1.65/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

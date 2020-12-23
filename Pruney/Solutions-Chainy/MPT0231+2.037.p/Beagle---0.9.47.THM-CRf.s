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
% DateTime   : Thu Dec  3 09:49:19 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(c_8,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k1_tarski(A_4),k2_tarski(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13,plain,(
    ! [A_12,C_13,B_14] :
      ( r1_tarski(A_12,C_13)
      | ~ r1_tarski(B_14,C_13)
      | ~ r1_tarski(A_12,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_18,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_13])).

tff(c_34,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_24])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(k1_tarski(A_6),k1_tarski(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_6])).

tff(c_44,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  %$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.80/1.17  
% 1.80/1.17  %Foreground sorts:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Background operators:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Foreground operators:
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.17  
% 1.80/1.18  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.80/1.18  tff(f_33, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.80/1.18  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.80/1.18  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.80/1.18  tff(c_8, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.80/1.18  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), k2_tarski(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.18  tff(c_10, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.80/1.18  tff(c_13, plain, (![A_12, C_13, B_14]: (r1_tarski(A_12, C_13) | ~r1_tarski(B_14, C_13) | ~r1_tarski(A_12, B_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.18  tff(c_24, plain, (![A_18]: (r1_tarski(A_18, k1_tarski('#skF_3')) | ~r1_tarski(A_18, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_10, c_13])).
% 1.80/1.18  tff(c_34, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_24])).
% 1.80/1.18  tff(c_6, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(k1_tarski(A_6), k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.80/1.18  tff(c_39, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_34, c_6])).
% 1.80/1.18  tff(c_44, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_39])).
% 1.80/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  Inference rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Ref     : 0
% 1.80/1.18  #Sup     : 7
% 1.80/1.18  #Fact    : 0
% 1.80/1.18  #Define  : 0
% 1.80/1.18  #Split   : 0
% 1.80/1.18  #Chain   : 0
% 1.80/1.18  #Close   : 0
% 1.80/1.18  
% 1.80/1.18  Ordering : KBO
% 1.80/1.18  
% 1.80/1.18  Simplification rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Subsume      : 0
% 1.80/1.18  #Demod        : 0
% 1.80/1.18  #Tautology    : 0
% 1.80/1.18  #SimpNegUnit  : 1
% 1.80/1.18  #BackRed      : 0
% 1.80/1.18  
% 1.80/1.18  #Partial instantiations: 0
% 1.80/1.18  #Strategies tried      : 1
% 1.80/1.18  
% 1.80/1.18  Timing (in seconds)
% 1.80/1.18  ----------------------
% 1.80/1.18  Preprocessing        : 0.28
% 1.80/1.18  Parsing              : 0.15
% 1.80/1.18  CNF conversion       : 0.02
% 1.80/1.18  Main loop            : 0.08
% 1.80/1.18  Inferencing          : 0.04
% 1.80/1.18  Reduction            : 0.02
% 1.80/1.18  Demodulation         : 0.01
% 1.80/1.18  BG Simplification    : 0.01
% 1.80/1.18  Subsumption          : 0.01
% 1.80/1.18  Abstraction          : 0.00
% 1.80/1.18  MUC search           : 0.00
% 1.80/1.18  Cooper               : 0.00
% 1.80/1.18  Total                : 0.39
% 1.80/1.18  Index Insertion      : 0.00
% 1.80/1.18  Index Deletion       : 0.00
% 1.80/1.18  Index Matching       : 0.00
% 1.80/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

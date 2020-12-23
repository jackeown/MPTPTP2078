%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:40 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_14,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),k1_tarski(B_19)) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(k1_tarski(A_20),C_21)
      | ~ r1_tarski(k2_tarski(A_20,B_22),C_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_55,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_16,c_48])).

tff(c_56,plain,(
    ! [C_23,A_24,B_25] :
      ( C_23 = A_24
      | B_25 = A_24
      | ~ r1_tarski(k1_tarski(A_24),k2_tarski(B_25,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_55,c_56])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_12,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:03:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.17  
% 1.62/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.17  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.62/1.17  
% 1.62/1.17  %Foreground sorts:
% 1.62/1.17  
% 1.62/1.17  
% 1.62/1.17  %Background operators:
% 1.62/1.17  
% 1.62/1.17  
% 1.62/1.17  %Foreground operators:
% 1.62/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.62/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.62/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.17  
% 1.62/1.17  tff(f_54, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.62/1.17  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.62/1.17  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.62/1.17  tff(f_44, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.62/1.17  tff(c_14, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.17  tff(c_12, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.17  tff(c_16, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.17  tff(c_36, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(B_19))=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.17  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.17  tff(c_48, plain, (![A_20, C_21, B_22]: (r1_tarski(k1_tarski(A_20), C_21) | ~r1_tarski(k2_tarski(A_20, B_22), C_21))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2])).
% 1.62/1.17  tff(c_55, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_48])).
% 1.62/1.17  tff(c_56, plain, (![C_23, A_24, B_25]: (C_23=A_24 | B_25=A_24 | ~r1_tarski(k1_tarski(A_24), k2_tarski(B_25, C_23)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.17  tff(c_59, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_55, c_56])).
% 1.62/1.17  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_12, c_59])).
% 1.62/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.17  
% 1.62/1.17  Inference rules
% 1.62/1.17  ----------------------
% 1.62/1.17  #Ref     : 0
% 1.62/1.18  #Sup     : 11
% 1.62/1.18  #Fact    : 0
% 1.62/1.18  #Define  : 0
% 1.62/1.18  #Split   : 0
% 1.62/1.18  #Chain   : 0
% 1.62/1.18  #Close   : 0
% 1.62/1.18  
% 1.62/1.18  Ordering : KBO
% 1.62/1.18  
% 1.62/1.18  Simplification rules
% 1.62/1.18  ----------------------
% 1.62/1.18  #Subsume      : 0
% 1.62/1.18  #Demod        : 0
% 1.62/1.18  #Tautology    : 7
% 1.62/1.18  #SimpNegUnit  : 1
% 1.62/1.18  #BackRed      : 0
% 1.62/1.18  
% 1.62/1.18  #Partial instantiations: 0
% 1.62/1.18  #Strategies tried      : 1
% 1.62/1.18  
% 1.62/1.18  Timing (in seconds)
% 1.62/1.18  ----------------------
% 1.62/1.18  Preprocessing        : 0.29
% 1.62/1.18  Parsing              : 0.15
% 1.62/1.18  CNF conversion       : 0.02
% 1.62/1.18  Main loop            : 0.08
% 1.62/1.18  Inferencing          : 0.03
% 1.62/1.18  Reduction            : 0.02
% 1.62/1.18  Demodulation         : 0.01
% 1.62/1.18  BG Simplification    : 0.01
% 1.62/1.18  Subsumption          : 0.01
% 1.62/1.18  Abstraction          : 0.00
% 1.62/1.18  MUC search           : 0.00
% 1.62/1.18  Cooper               : 0.00
% 1.62/1.18  Total                : 0.40
% 1.62/1.18  Index Insertion      : 0.00
% 1.62/1.18  Index Deletion       : 0.00
% 1.62/1.18  Index Matching       : 0.00
% 1.62/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

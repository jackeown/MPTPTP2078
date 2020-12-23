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
% DateTime   : Thu Dec  3 09:49:40 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  34 expanded)
%              Number of equality atoms :   14 (  18 expanded)
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

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

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

tff(c_8,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k1_tarski(A_24),k2_tarski(B_25,C_26)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_134,plain,(
    ! [A_31,C_32,B_33,C_34] :
      ( r1_tarski(k1_tarski(A_31),C_32)
      | ~ r1_tarski(k1_enumset1(A_31,B_33,C_34),C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_144,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(k1_tarski(A_35),C_36)
      | ~ r1_tarski(k2_tarski(A_35,B_37),C_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_134])).

tff(c_151,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_16,c_144])).

tff(c_10,plain,(
    ! [C_12,A_10,B_11] :
      ( C_12 = A_10
      | B_11 = A_10
      | ~ r1_tarski(k1_tarski(A_10),k2_tarski(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_154,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_151,c_10])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_12,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:46:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.18  
% 1.73/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.18  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.73/1.18  
% 1.73/1.18  %Foreground sorts:
% 1.73/1.18  
% 1.73/1.18  
% 1.73/1.18  %Background operators:
% 1.73/1.18  
% 1.73/1.18  
% 1.73/1.18  %Foreground operators:
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.18  
% 1.73/1.19  tff(f_54, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.73/1.19  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.73/1.19  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 1.73/1.19  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.73/1.19  tff(f_44, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.73/1.19  tff(c_14, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.19  tff(c_12, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.19  tff(c_16, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.19  tff(c_8, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.19  tff(c_41, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(B_25, C_26))=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.19  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.19  tff(c_134, plain, (![A_31, C_32, B_33, C_34]: (r1_tarski(k1_tarski(A_31), C_32) | ~r1_tarski(k1_enumset1(A_31, B_33, C_34), C_32))), inference(superposition, [status(thm), theory('equality')], [c_41, c_2])).
% 1.73/1.19  tff(c_144, plain, (![A_35, C_36, B_37]: (r1_tarski(k1_tarski(A_35), C_36) | ~r1_tarski(k2_tarski(A_35, B_37), C_36))), inference(superposition, [status(thm), theory('equality')], [c_8, c_134])).
% 1.73/1.19  tff(c_151, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_144])).
% 1.73/1.19  tff(c_10, plain, (![C_12, A_10, B_11]: (C_12=A_10 | B_11=A_10 | ~r1_tarski(k1_tarski(A_10), k2_tarski(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.73/1.19  tff(c_154, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_151, c_10])).
% 1.73/1.19  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_12, c_154])).
% 1.73/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.19  
% 1.73/1.19  Inference rules
% 1.73/1.19  ----------------------
% 1.73/1.19  #Ref     : 0
% 1.73/1.19  #Sup     : 33
% 1.73/1.19  #Fact    : 0
% 1.73/1.19  #Define  : 0
% 1.73/1.19  #Split   : 0
% 1.73/1.19  #Chain   : 0
% 1.73/1.19  #Close   : 0
% 1.73/1.19  
% 1.73/1.19  Ordering : KBO
% 1.73/1.19  
% 1.73/1.19  Simplification rules
% 1.73/1.19  ----------------------
% 1.73/1.19  #Subsume      : 1
% 1.73/1.19  #Demod        : 8
% 1.73/1.19  #Tautology    : 23
% 1.73/1.19  #SimpNegUnit  : 1
% 1.73/1.19  #BackRed      : 0
% 1.73/1.19  
% 1.73/1.19  #Partial instantiations: 0
% 1.73/1.19  #Strategies tried      : 1
% 1.73/1.19  
% 1.73/1.19  Timing (in seconds)
% 1.73/1.19  ----------------------
% 1.73/1.19  Preprocessing        : 0.25
% 1.73/1.19  Parsing              : 0.13
% 1.73/1.19  CNF conversion       : 0.02
% 1.73/1.19  Main loop            : 0.12
% 1.73/1.20  Inferencing          : 0.05
% 1.73/1.20  Reduction            : 0.04
% 1.73/1.20  Demodulation         : 0.03
% 1.73/1.20  BG Simplification    : 0.01
% 1.73/1.20  Subsumption          : 0.01
% 1.73/1.20  Abstraction          : 0.01
% 1.73/1.20  MUC search           : 0.00
% 1.73/1.20  Cooper               : 0.00
% 1.73/1.20  Total                : 0.39
% 1.73/1.20  Index Insertion      : 0.00
% 1.73/1.20  Index Deletion       : 0.00
% 1.73/1.20  Index Matching       : 0.00
% 1.73/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:49:41 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_12,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_13,B_14] : r1_tarski(k1_tarski(A_13),k2_tarski(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4])).

tff(c_14,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(A_15,C_16)
      | ~ r1_tarski(B_17,C_16)
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_tarski('#skF_3','#skF_4'))
      | ~ r1_tarski(A_15,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_14,c_28])).

tff(c_54,plain,(
    ! [C_27,A_28,B_29] :
      ( C_27 = A_28
      | B_29 = A_28
      | ~ r1_tarski(k1_tarski(A_28),k2_tarski(B_29,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    ! [A_33] :
      ( A_33 = '#skF_4'
      | A_33 = '#skF_3'
      | ~ r1_tarski(k1_tarski(A_33),k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_33,c_54])).

tff(c_78,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_10,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:17:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.09  
% 1.66/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.09  %$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.66/1.09  
% 1.66/1.09  %Foreground sorts:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Background operators:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Foreground operators:
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.09  
% 1.66/1.10  tff(f_54, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.66/1.10  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.66/1.10  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.66/1.10  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.66/1.10  tff(f_44, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.66/1.10  tff(c_12, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.10  tff(c_10, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.10  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.10  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.10  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), k2_tarski(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4])).
% 1.66/1.10  tff(c_14, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.10  tff(c_28, plain, (![A_15, C_16, B_17]: (r1_tarski(A_15, C_16) | ~r1_tarski(B_17, C_16) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.10  tff(c_33, plain, (![A_15]: (r1_tarski(A_15, k2_tarski('#skF_3', '#skF_4')) | ~r1_tarski(A_15, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_14, c_28])).
% 1.66/1.10  tff(c_54, plain, (![C_27, A_28, B_29]: (C_27=A_28 | B_29=A_28 | ~r1_tarski(k1_tarski(A_28), k2_tarski(B_29, C_27)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.66/1.10  tff(c_71, plain, (![A_33]: (A_33='#skF_4' | A_33='#skF_3' | ~r1_tarski(k1_tarski(A_33), k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_33, c_54])).
% 1.66/1.10  tff(c_78, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_22, c_71])).
% 1.66/1.10  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_10, c_78])).
% 1.66/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  Inference rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Ref     : 0
% 1.66/1.10  #Sup     : 15
% 1.66/1.10  #Fact    : 0
% 1.66/1.10  #Define  : 0
% 1.66/1.10  #Split   : 0
% 1.66/1.10  #Chain   : 0
% 1.66/1.10  #Close   : 0
% 1.66/1.10  
% 1.66/1.10  Ordering : KBO
% 1.66/1.10  
% 1.66/1.10  Simplification rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Subsume      : 1
% 1.66/1.10  #Demod        : 0
% 1.66/1.10  #Tautology    : 3
% 1.66/1.10  #SimpNegUnit  : 1
% 1.66/1.10  #BackRed      : 0
% 1.66/1.10  
% 1.66/1.10  #Partial instantiations: 0
% 1.66/1.10  #Strategies tried      : 1
% 1.66/1.10  
% 1.66/1.10  Timing (in seconds)
% 1.66/1.10  ----------------------
% 1.66/1.10  Preprocessing        : 0.26
% 1.66/1.10  Parsing              : 0.14
% 1.66/1.10  CNF conversion       : 0.01
% 1.66/1.10  Main loop            : 0.11
% 1.66/1.10  Inferencing          : 0.04
% 1.66/1.10  Reduction            : 0.03
% 1.66/1.10  Demodulation         : 0.02
% 1.66/1.10  BG Simplification    : 0.01
% 1.66/1.10  Subsumption          : 0.02
% 1.66/1.10  Abstraction          : 0.01
% 1.66/1.10  MUC search           : 0.00
% 1.66/1.10  Cooper               : 0.00
% 1.66/1.10  Total                : 0.39
% 1.66/1.10  Index Insertion      : 0.00
% 1.66/1.10  Index Deletion       : 0.00
% 1.66/1.10  Index Matching       : 0.00
% 1.66/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

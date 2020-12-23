%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:19 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  33 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_10,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k1_tarski(A_5),k2_tarski(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(A_14,C_15)
      | ~ r1_tarski(B_16,C_15)
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_20,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_27])).

tff(c_54,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_4,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [C_22,A_23,B_24] :
      ( C_22 = A_23
      | B_24 = A_23
      | ~ r1_tarski(k1_tarski(A_23),k2_tarski(B_24,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,(
    ! [A_26,A_25] :
      ( A_26 = A_25
      | A_26 = A_25
      | ~ r1_tarski(k1_tarski(A_26),k1_tarski(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_83,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_76])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_10,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.14  %$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.68/1.14  
% 1.68/1.14  %Foreground sorts:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Background operators:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Foreground operators:
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.14  
% 1.68/1.15  tff(f_49, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.68/1.15  tff(f_35, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.68/1.15  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.68/1.15  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.68/1.15  tff(f_44, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.68/1.15  tff(c_10, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.68/1.15  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), k2_tarski(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.15  tff(c_12, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.68/1.15  tff(c_27, plain, (![A_14, C_15, B_16]: (r1_tarski(A_14, C_15) | ~r1_tarski(B_16, C_15) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.15  tff(c_44, plain, (![A_20]: (r1_tarski(A_20, k1_tarski('#skF_3')) | ~r1_tarski(A_20, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_12, c_27])).
% 1.68/1.15  tff(c_54, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_44])).
% 1.68/1.15  tff(c_4, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.15  tff(c_62, plain, (![C_22, A_23, B_24]: (C_22=A_23 | B_24=A_23 | ~r1_tarski(k1_tarski(A_23), k2_tarski(B_24, C_22)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.15  tff(c_76, plain, (![A_26, A_25]: (A_26=A_25 | A_26=A_25 | ~r1_tarski(k1_tarski(A_26), k1_tarski(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 1.68/1.15  tff(c_83, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_54, c_76])).
% 1.68/1.15  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_10, c_83])).
% 1.68/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  Inference rules
% 1.68/1.15  ----------------------
% 1.68/1.15  #Ref     : 0
% 1.68/1.15  #Sup     : 18
% 1.68/1.15  #Fact    : 0
% 1.68/1.15  #Define  : 0
% 1.68/1.15  #Split   : 0
% 1.68/1.15  #Chain   : 0
% 1.68/1.15  #Close   : 0
% 1.68/1.15  
% 1.68/1.15  Ordering : KBO
% 1.68/1.15  
% 1.68/1.15  Simplification rules
% 1.68/1.15  ----------------------
% 1.68/1.15  #Subsume      : 1
% 1.68/1.15  #Demod        : 0
% 1.68/1.15  #Tautology    : 5
% 1.68/1.15  #SimpNegUnit  : 1
% 1.68/1.15  #BackRed      : 0
% 1.68/1.15  
% 1.68/1.15  #Partial instantiations: 0
% 1.68/1.15  #Strategies tried      : 1
% 1.68/1.15  
% 1.68/1.15  Timing (in seconds)
% 1.68/1.15  ----------------------
% 1.68/1.15  Preprocessing        : 0.27
% 1.68/1.15  Parsing              : 0.15
% 1.68/1.15  CNF conversion       : 0.02
% 1.68/1.15  Main loop            : 0.11
% 1.68/1.15  Inferencing          : 0.04
% 1.68/1.15  Reduction            : 0.03
% 1.68/1.15  Demodulation         : 0.02
% 1.68/1.15  BG Simplification    : 0.01
% 1.68/1.15  Subsumption          : 0.02
% 1.68/1.15  Abstraction          : 0.00
% 1.68/1.15  MUC search           : 0.00
% 1.68/1.15  Cooper               : 0.00
% 1.68/1.15  Total                : 0.41
% 1.68/1.15  Index Insertion      : 0.00
% 1.68/1.15  Index Deletion       : 0.00
% 1.68/1.15  Index Matching       : 0.00
% 1.68/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

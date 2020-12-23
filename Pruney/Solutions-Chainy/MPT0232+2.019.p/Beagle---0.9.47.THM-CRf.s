%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:22 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  36 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_18,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,(
    ! [C_15,A_16,B_17] :
      ( C_15 = A_16
      | ~ r1_tarski(k2_tarski(A_16,B_17),k1_tarski(C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_35])).

tff(c_16,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_12,plain,(
    ! [A_6,B_7] : r1_tarski(k1_tarski(A_6),k2_tarski(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_70,plain,(
    ! [B_22,A_23] :
      ( B_22 = A_23
      | ~ r1_tarski(B_22,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1')
    | ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_43,c_70])).

tff(c_79,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:05:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  %$ r1_tarski > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.63/1.10  
% 1.63/1.10  %Foreground sorts:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Background operators:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Foreground operators:
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.63/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.10  
% 1.63/1.10  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 1.63/1.10  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.63/1.10  tff(f_37, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.63/1.10  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.63/1.10  tff(c_18, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.10  tff(c_35, plain, (![C_15, A_16, B_17]: (C_15=A_16 | ~r1_tarski(k2_tarski(A_16, B_17), k1_tarski(C_15)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.63/1.10  tff(c_42, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_18, c_35])).
% 1.63/1.10  tff(c_16, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.10  tff(c_44, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16])).
% 1.63/1.10  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), k2_tarski(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.10  tff(c_43, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 1.63/1.10  tff(c_70, plain, (![B_22, A_23]: (B_22=A_23 | ~r1_tarski(B_22, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.10  tff(c_72, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1') | ~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_43, c_70])).
% 1.63/1.10  tff(c_79, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_72])).
% 1.63/1.10  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_79])).
% 1.63/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  Inference rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Ref     : 0
% 1.63/1.10  #Sup     : 14
% 1.63/1.10  #Fact    : 0
% 1.63/1.10  #Define  : 0
% 1.63/1.11  #Split   : 0
% 1.63/1.11  #Chain   : 0
% 1.63/1.11  #Close   : 0
% 1.63/1.11  
% 1.63/1.11  Ordering : KBO
% 1.63/1.11  
% 1.63/1.11  Simplification rules
% 1.63/1.11  ----------------------
% 1.63/1.11  #Subsume      : 0
% 1.63/1.11  #Demod        : 5
% 1.63/1.11  #Tautology    : 10
% 1.63/1.11  #SimpNegUnit  : 1
% 1.63/1.11  #BackRed      : 2
% 1.63/1.11  
% 1.63/1.11  #Partial instantiations: 0
% 1.63/1.11  #Strategies tried      : 1
% 1.63/1.11  
% 1.63/1.11  Timing (in seconds)
% 1.63/1.11  ----------------------
% 1.63/1.11  Preprocessing        : 0.25
% 1.63/1.11  Parsing              : 0.13
% 1.63/1.11  CNF conversion       : 0.02
% 1.63/1.11  Main loop            : 0.08
% 1.63/1.11  Inferencing          : 0.03
% 1.63/1.11  Reduction            : 0.03
% 1.63/1.11  Demodulation         : 0.02
% 1.63/1.11  BG Simplification    : 0.01
% 1.63/1.11  Subsumption          : 0.01
% 1.63/1.11  Abstraction          : 0.00
% 1.63/1.11  MUC search           : 0.00
% 1.63/1.11  Cooper               : 0.00
% 1.63/1.11  Total                : 0.36
% 1.63/1.11  Index Insertion      : 0.00
% 1.63/1.11  Index Deletion       : 0.00
% 1.63/1.11  Index Matching       : 0.00
% 1.63/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:43 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_15,B_16] : r1_tarski(k1_tarski(A_15),k2_tarski(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_43,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(k1_tarski(A_6),k1_tarski(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_43,c_8])).

tff(c_50,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.06  
% 1.48/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.06  %$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.48/1.06  
% 1.48/1.06  %Foreground sorts:
% 1.48/1.06  
% 1.48/1.06  
% 1.48/1.06  %Background operators:
% 1.48/1.06  
% 1.48/1.06  
% 1.48/1.06  %Foreground operators:
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.48/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.48/1.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.48/1.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.48/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.48/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.48/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.48/1.06  
% 1.48/1.06  tff(f_40, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 1.48/1.06  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.48/1.06  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.48/1.06  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.48/1.06  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.48/1.06  tff(c_12, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.48/1.06  tff(c_28, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.48/1.06  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.48/1.06  tff(c_40, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), k2_tarski(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2])).
% 1.48/1.06  tff(c_43, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_40])).
% 1.48/1.06  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(k1_tarski(A_6), k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.48/1.06  tff(c_46, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_43, c_8])).
% 1.48/1.06  tff(c_50, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_46])).
% 1.48/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.06  
% 1.48/1.06  Inference rules
% 1.48/1.06  ----------------------
% 1.48/1.06  #Ref     : 0
% 1.48/1.06  #Sup     : 9
% 1.48/1.06  #Fact    : 0
% 1.48/1.06  #Define  : 0
% 1.48/1.06  #Split   : 0
% 1.48/1.06  #Chain   : 0
% 1.48/1.06  #Close   : 0
% 1.48/1.06  
% 1.48/1.06  Ordering : KBO
% 1.48/1.06  
% 1.48/1.06  Simplification rules
% 1.48/1.06  ----------------------
% 1.48/1.06  #Subsume      : 0
% 1.48/1.07  #Demod        : 0
% 1.48/1.07  #Tautology    : 6
% 1.48/1.07  #SimpNegUnit  : 1
% 1.48/1.07  #BackRed      : 0
% 1.48/1.07  
% 1.48/1.07  #Partial instantiations: 0
% 1.48/1.07  #Strategies tried      : 1
% 1.48/1.07  
% 1.48/1.07  Timing (in seconds)
% 1.48/1.07  ----------------------
% 1.48/1.07  Preprocessing        : 0.25
% 1.48/1.07  Parsing              : 0.13
% 1.48/1.07  CNF conversion       : 0.01
% 1.48/1.07  Main loop            : 0.07
% 1.48/1.07  Inferencing          : 0.03
% 1.48/1.07  Reduction            : 0.02
% 1.48/1.07  Demodulation         : 0.01
% 1.48/1.07  BG Simplification    : 0.01
% 1.48/1.07  Subsumption          : 0.01
% 1.48/1.07  Abstraction          : 0.00
% 1.48/1.07  MUC search           : 0.00
% 1.48/1.07  Cooper               : 0.00
% 1.48/1.07  Total                : 0.34
% 1.48/1.07  Index Insertion      : 0.00
% 1.48/1.07  Index Deletion       : 0.00
% 1.48/1.07  Index Matching       : 0.00
% 1.48/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------

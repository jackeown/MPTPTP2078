%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:52 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  41 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_34,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_90,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_172,plain,(
    ! [A_44,B_45] : k2_xboole_0(k3_xboole_0(A_44,B_45),k4_xboole_0(A_44,B_45)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_190,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_172])).

tff(c_24,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_193,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_17,k1_xboole_0)) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_172])).

tff(c_201,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_193])).

tff(c_292,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_201])).

tff(c_502,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(k4_xboole_0(A_72,B_73),C_74)
      | ~ r1_tarski(A_72,k2_xboole_0(B_73,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_684,plain,(
    ! [C_88] :
      ( r1_tarski('#skF_3',C_88)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_502])).

tff(c_713,plain,(
    ! [B_89] :
      ( r1_tarski('#skF_3',B_89)
      | ~ r1_tarski('#skF_3',k2_xboole_0(B_89,'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_684])).

tff(c_739,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_713])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.86  
% 3.24/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.24/1.87  
% 3.24/1.87  %Foreground sorts:
% 3.24/1.87  
% 3.24/1.87  
% 3.24/1.87  %Background operators:
% 3.24/1.87  
% 3.24/1.87  
% 3.24/1.87  %Foreground operators:
% 3.24/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.87  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.24/1.87  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.87  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.24/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.24/1.87  
% 3.24/1.88  tff(f_79, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 3.24/1.88  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.24/1.88  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.24/1.88  tff(f_70, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.24/1.88  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.24/1.88  tff(f_58, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.24/1.88  tff(f_66, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.24/1.88  tff(c_34, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.24/1.88  tff(c_38, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.24/1.88  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.88  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.24/1.88  tff(c_90, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.24/1.88  tff(c_103, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_90])).
% 3.24/1.88  tff(c_172, plain, (![A_44, B_45]: (k2_xboole_0(k3_xboole_0(A_44, B_45), k4_xboole_0(A_44, B_45))=A_44)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.24/1.88  tff(c_190, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_103, c_172])).
% 3.24/1.88  tff(c_24, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.88  tff(c_20, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.88  tff(c_193, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_17, k1_xboole_0))=A_17)), inference(superposition, [status(thm), theory('equality')], [c_20, c_172])).
% 3.24/1.88  tff(c_201, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_193])).
% 3.24/1.88  tff(c_292, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_190, c_201])).
% 3.24/1.88  tff(c_502, plain, (![A_72, B_73, C_74]: (r1_tarski(k4_xboole_0(A_72, B_73), C_74) | ~r1_tarski(A_72, k2_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.24/1.88  tff(c_684, plain, (![C_88]: (r1_tarski('#skF_3', C_88) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_88)))), inference(superposition, [status(thm), theory('equality')], [c_292, c_502])).
% 3.24/1.88  tff(c_713, plain, (![B_89]: (r1_tarski('#skF_3', B_89) | ~r1_tarski('#skF_3', k2_xboole_0(B_89, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_684])).
% 3.24/1.88  tff(c_739, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_713])).
% 3.24/1.88  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_739])).
% 3.24/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.88  
% 3.24/1.88  Inference rules
% 3.24/1.88  ----------------------
% 3.24/1.88  #Ref     : 1
% 3.24/1.88  #Sup     : 168
% 3.24/1.88  #Fact    : 0
% 3.24/1.88  #Define  : 0
% 3.24/1.88  #Split   : 2
% 3.24/1.88  #Chain   : 0
% 3.24/1.88  #Close   : 0
% 3.24/1.88  
% 3.24/1.88  Ordering : KBO
% 3.24/1.88  
% 3.24/1.88  Simplification rules
% 3.24/1.88  ----------------------
% 3.24/1.89  #Subsume      : 25
% 3.24/1.89  #Demod        : 56
% 3.24/1.89  #Tautology    : 94
% 3.24/1.89  #SimpNegUnit  : 4
% 3.24/1.89  #BackRed      : 1
% 3.24/1.89  
% 3.24/1.89  #Partial instantiations: 0
% 3.24/1.89  #Strategies tried      : 1
% 3.24/1.89  
% 3.24/1.89  Timing (in seconds)
% 3.24/1.89  ----------------------
% 3.24/1.89  Preprocessing        : 0.45
% 3.24/1.89  Parsing              : 0.24
% 3.24/1.89  CNF conversion       : 0.03
% 3.24/1.89  Main loop            : 0.52
% 3.24/1.89  Inferencing          : 0.19
% 3.24/1.89  Reduction            : 0.19
% 3.24/1.89  Demodulation         : 0.15
% 3.24/1.89  BG Simplification    : 0.03
% 3.24/1.89  Subsumption          : 0.09
% 3.24/1.89  Abstraction          : 0.02
% 3.24/1.89  MUC search           : 0.00
% 3.24/1.89  Cooper               : 0.00
% 3.24/1.89  Total                : 1.01
% 3.24/1.89  Index Insertion      : 0.00
% 3.24/1.89  Index Deletion       : 0.00
% 3.24/1.89  Index Matching       : 0.00
% 3.24/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------

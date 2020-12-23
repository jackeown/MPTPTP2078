%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:22 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_24,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_55,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_55])).

tff(c_77,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(k2_xboole_0(A_36,B_38),C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_153,plain,(
    ! [C_48] :
      ( r1_tarski('#skF_1',C_48)
      | ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_77])).

tff(c_157,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_153])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_157])).

tff(c_162,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_16,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_276,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_xboole_0(A_66,C_67)
      | ~ r1_xboole_0(B_68,C_67)
      | ~ r1_tarski(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_291,plain,(
    ! [A_71,B_72,A_73] :
      ( r1_xboole_0(A_71,B_72)
      | ~ r1_tarski(A_71,k4_xboole_0(A_73,B_72)) ) ),
    inference(resolution,[status(thm)],[c_16,c_276])).

tff(c_309,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_291])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.92/1.21  
% 1.92/1.21  %Foreground sorts:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Background operators:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Foreground operators:
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.92/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.21  
% 1.92/1.22  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.92/1.22  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.92/1.22  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.92/1.22  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.92/1.22  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.92/1.22  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.92/1.22  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.22  tff(c_54, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 1.92/1.22  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.22  tff(c_26, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.22  tff(c_55, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.22  tff(c_63, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_55])).
% 1.92/1.22  tff(c_77, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(k2_xboole_0(A_36, B_38), C_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.22  tff(c_153, plain, (![C_48]: (r1_tarski('#skF_1', C_48) | ~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), C_48))), inference(superposition, [status(thm), theory('equality')], [c_63, c_77])).
% 1.92/1.22  tff(c_157, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_153])).
% 1.92/1.22  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_157])).
% 1.92/1.22  tff(c_162, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 1.92/1.22  tff(c_16, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.22  tff(c_276, plain, (![A_66, C_67, B_68]: (r1_xboole_0(A_66, C_67) | ~r1_xboole_0(B_68, C_67) | ~r1_tarski(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.22  tff(c_291, plain, (![A_71, B_72, A_73]: (r1_xboole_0(A_71, B_72) | ~r1_tarski(A_71, k4_xboole_0(A_73, B_72)))), inference(resolution, [status(thm)], [c_16, c_276])).
% 1.92/1.22  tff(c_309, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_291])).
% 1.92/1.22  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_309])).
% 1.92/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  Inference rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Ref     : 0
% 1.92/1.22  #Sup     : 70
% 1.92/1.22  #Fact    : 0
% 1.92/1.22  #Define  : 0
% 1.92/1.22  #Split   : 1
% 1.92/1.22  #Chain   : 0
% 1.92/1.22  #Close   : 0
% 1.92/1.22  
% 1.92/1.22  Ordering : KBO
% 1.92/1.22  
% 1.92/1.22  Simplification rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Subsume      : 1
% 1.92/1.22  #Demod        : 8
% 1.92/1.22  #Tautology    : 40
% 1.92/1.22  #SimpNegUnit  : 2
% 1.92/1.22  #BackRed      : 0
% 1.92/1.22  
% 1.92/1.22  #Partial instantiations: 0
% 1.92/1.22  #Strategies tried      : 1
% 1.92/1.22  
% 1.92/1.22  Timing (in seconds)
% 1.92/1.22  ----------------------
% 2.06/1.22  Preprocessing        : 0.27
% 2.06/1.22  Parsing              : 0.15
% 2.06/1.22  CNF conversion       : 0.02
% 2.06/1.22  Main loop            : 0.19
% 2.06/1.22  Inferencing          : 0.08
% 2.06/1.22  Reduction            : 0.06
% 2.06/1.22  Demodulation         : 0.04
% 2.06/1.22  BG Simplification    : 0.01
% 2.06/1.22  Subsumption          : 0.03
% 2.06/1.22  Abstraction          : 0.01
% 2.06/1.22  MUC search           : 0.00
% 2.06/1.22  Cooper               : 0.00
% 2.06/1.22  Total                : 0.48
% 2.06/1.22  Index Insertion      : 0.00
% 2.06/1.22  Index Deletion       : 0.00
% 2.06/1.22  Index Matching       : 0.00
% 2.06/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

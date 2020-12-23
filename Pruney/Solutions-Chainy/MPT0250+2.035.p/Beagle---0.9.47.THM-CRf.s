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
% DateTime   : Thu Dec  3 09:50:36 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  45 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_80,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_152,plain,(
    ! [B_57,A_58] : k3_tarski(k2_tarski(B_57,A_58)) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_80])).

tff(c_26,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_158,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_26])).

tff(c_36,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_178,plain,(
    r1_tarski(k2_xboole_0('#skF_3',k1_tarski('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_36])).

tff(c_12,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_132,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(A_54,C_55)
      | ~ r1_tarski(k2_tarski(A_54,B_56),C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_238,plain,(
    ! [A_65,B_66,B_67] : r2_hidden(A_65,k2_xboole_0(k2_tarski(A_65,B_66),B_67)) ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_260,plain,(
    ! [A_68,B_69] : r2_hidden(A_68,k2_xboole_0(k1_tarski(A_68),B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_238])).

tff(c_264,plain,(
    ! [A_68,B_57] : r2_hidden(A_68,k2_xboole_0(B_57,k1_tarski(A_68))) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_260])).

tff(c_345,plain,(
    ! [C_82,B_83,A_84] :
      ( r2_hidden(C_82,B_83)
      | ~ r2_hidden(C_82,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_769,plain,(
    ! [A_149,B_150,B_151] :
      ( r2_hidden(A_149,B_150)
      | ~ r1_tarski(k2_xboole_0(B_151,k1_tarski(A_149)),B_150) ) ),
    inference(resolution,[status(thm)],[c_264,c_345])).

tff(c_776,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_178,c_769])).

tff(c_806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.35  
% 2.65/1.36  tff(f_63, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.65/1.36  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.65/1.36  tff(f_52, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.65/1.36  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.65/1.36  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.65/1.36  tff(f_58, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.65/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.65/1.36  tff(c_34, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.36  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.65/1.36  tff(c_80, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.65/1.36  tff(c_152, plain, (![B_57, A_58]: (k3_tarski(k2_tarski(B_57, A_58))=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_10, c_80])).
% 2.65/1.36  tff(c_26, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.65/1.36  tff(c_158, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_152, c_26])).
% 2.65/1.36  tff(c_36, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.36  tff(c_178, plain, (r1_tarski(k2_xboole_0('#skF_3', k1_tarski('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_36])).
% 2.65/1.36  tff(c_12, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.65/1.36  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.65/1.36  tff(c_132, plain, (![A_54, C_55, B_56]: (r2_hidden(A_54, C_55) | ~r1_tarski(k2_tarski(A_54, B_56), C_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.65/1.36  tff(c_238, plain, (![A_65, B_66, B_67]: (r2_hidden(A_65, k2_xboole_0(k2_tarski(A_65, B_66), B_67)))), inference(resolution, [status(thm)], [c_8, c_132])).
% 2.65/1.36  tff(c_260, plain, (![A_68, B_69]: (r2_hidden(A_68, k2_xboole_0(k1_tarski(A_68), B_69)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_238])).
% 2.65/1.36  tff(c_264, plain, (![A_68, B_57]: (r2_hidden(A_68, k2_xboole_0(B_57, k1_tarski(A_68))))), inference(superposition, [status(thm), theory('equality')], [c_158, c_260])).
% 2.65/1.36  tff(c_345, plain, (![C_82, B_83, A_84]: (r2_hidden(C_82, B_83) | ~r2_hidden(C_82, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.36  tff(c_769, plain, (![A_149, B_150, B_151]: (r2_hidden(A_149, B_150) | ~r1_tarski(k2_xboole_0(B_151, k1_tarski(A_149)), B_150))), inference(resolution, [status(thm)], [c_264, c_345])).
% 2.65/1.36  tff(c_776, plain, (r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_178, c_769])).
% 2.65/1.36  tff(c_806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_776])).
% 2.65/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  Inference rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Ref     : 0
% 2.65/1.36  #Sup     : 178
% 2.65/1.36  #Fact    : 0
% 2.65/1.36  #Define  : 0
% 2.65/1.36  #Split   : 0
% 2.65/1.36  #Chain   : 0
% 2.65/1.36  #Close   : 0
% 2.65/1.36  
% 2.65/1.36  Ordering : KBO
% 2.65/1.36  
% 2.65/1.36  Simplification rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Subsume      : 12
% 2.65/1.36  #Demod        : 60
% 2.65/1.36  #Tautology    : 100
% 2.65/1.36  #SimpNegUnit  : 1
% 2.65/1.36  #BackRed      : 1
% 2.65/1.36  
% 2.65/1.36  #Partial instantiations: 0
% 2.65/1.36  #Strategies tried      : 1
% 2.65/1.36  
% 2.65/1.36  Timing (in seconds)
% 2.65/1.36  ----------------------
% 2.65/1.36  Preprocessing        : 0.28
% 2.65/1.36  Parsing              : 0.15
% 2.65/1.36  CNF conversion       : 0.02
% 2.65/1.36  Main loop            : 0.33
% 2.65/1.36  Inferencing          : 0.12
% 2.65/1.36  Reduction            : 0.12
% 2.65/1.36  Demodulation         : 0.09
% 2.65/1.36  BG Simplification    : 0.02
% 2.65/1.36  Subsumption          : 0.05
% 2.65/1.36  Abstraction          : 0.02
% 2.65/1.36  MUC search           : 0.00
% 2.65/1.36  Cooper               : 0.00
% 2.65/1.36  Total                : 0.63
% 2.65/1.36  Index Insertion      : 0.00
% 2.65/1.36  Index Deletion       : 0.00
% 2.65/1.36  Index Matching       : 0.00
% 2.65/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

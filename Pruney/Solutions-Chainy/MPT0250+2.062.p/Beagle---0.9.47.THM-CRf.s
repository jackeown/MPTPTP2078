%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:40 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_36,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(resolution,[status(thm)],[c_10,c_82])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_284,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(k3_xboole_0(A_84,C_85),B_86)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_363,plain,(
    ! [A_93,B_94,B_95] :
      ( r1_tarski(k3_xboole_0(A_93,B_94),B_95)
      | ~ r1_tarski(B_94,B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_284])).

tff(c_386,plain,(
    ! [A_96,B_97,B_98] :
      ( r1_tarski(A_96,B_97)
      | ~ r1_tarski(k2_xboole_0(A_96,B_98),B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_363])).

tff(c_402,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_386])).

tff(c_14,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_207,plain,(
    ! [A_65,C_66,B_67] :
      ( r2_hidden(A_65,C_66)
      | ~ r1_tarski(k2_tarski(A_65,B_67),C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_218,plain,(
    ! [A_14,C_66] :
      ( r2_hidden(A_14,C_66)
      | ~ r1_tarski(k1_tarski(A_14),C_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_207])).

tff(c_415,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_402,c_218])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:13:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.14/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  
% 2.14/1.28  tff(f_68, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.14/1.28  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.14/1.28  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.14/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.14/1.28  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.14/1.28  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.28  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.14/1.28  tff(c_36, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.28  tff(c_38, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.28  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.28  tff(c_82, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.28  tff(c_90, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(resolution, [status(thm)], [c_10, c_82])).
% 2.14/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.28  tff(c_284, plain, (![A_84, C_85, B_86]: (r1_tarski(k3_xboole_0(A_84, C_85), B_86) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.28  tff(c_363, plain, (![A_93, B_94, B_95]: (r1_tarski(k3_xboole_0(A_93, B_94), B_95) | ~r1_tarski(B_94, B_95))), inference(superposition, [status(thm), theory('equality')], [c_2, c_284])).
% 2.14/1.28  tff(c_386, plain, (![A_96, B_97, B_98]: (r1_tarski(A_96, B_97) | ~r1_tarski(k2_xboole_0(A_96, B_98), B_97))), inference(superposition, [status(thm), theory('equality')], [c_90, c_363])).
% 2.14/1.28  tff(c_402, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_38, c_386])).
% 2.14/1.28  tff(c_14, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.28  tff(c_207, plain, (![A_65, C_66, B_67]: (r2_hidden(A_65, C_66) | ~r1_tarski(k2_tarski(A_65, B_67), C_66))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.28  tff(c_218, plain, (![A_14, C_66]: (r2_hidden(A_14, C_66) | ~r1_tarski(k1_tarski(A_14), C_66))), inference(superposition, [status(thm), theory('equality')], [c_14, c_207])).
% 2.14/1.28  tff(c_415, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_402, c_218])).
% 2.14/1.28  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_415])).
% 2.14/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  Inference rules
% 2.14/1.28  ----------------------
% 2.14/1.28  #Ref     : 0
% 2.14/1.28  #Sup     : 95
% 2.14/1.28  #Fact    : 0
% 2.14/1.29  #Define  : 0
% 2.14/1.29  #Split   : 0
% 2.14/1.29  #Chain   : 0
% 2.14/1.29  #Close   : 0
% 2.14/1.29  
% 2.14/1.29  Ordering : KBO
% 2.14/1.29  
% 2.14/1.29  Simplification rules
% 2.14/1.29  ----------------------
% 2.14/1.29  #Subsume      : 4
% 2.14/1.29  #Demod        : 14
% 2.14/1.29  #Tautology    : 54
% 2.14/1.29  #SimpNegUnit  : 1
% 2.14/1.29  #BackRed      : 0
% 2.14/1.29  
% 2.14/1.29  #Partial instantiations: 0
% 2.14/1.29  #Strategies tried      : 1
% 2.14/1.29  
% 2.14/1.29  Timing (in seconds)
% 2.14/1.29  ----------------------
% 2.14/1.29  Preprocessing        : 0.32
% 2.14/1.29  Parsing              : 0.17
% 2.14/1.29  CNF conversion       : 0.02
% 2.14/1.29  Main loop            : 0.22
% 2.14/1.29  Inferencing          : 0.08
% 2.14/1.29  Reduction            : 0.08
% 2.14/1.29  Demodulation         : 0.06
% 2.14/1.29  BG Simplification    : 0.02
% 2.14/1.29  Subsumption          : 0.03
% 2.14/1.29  Abstraction          : 0.01
% 2.14/1.29  MUC search           : 0.00
% 2.14/1.29  Cooper               : 0.00
% 2.14/1.29  Total                : 0.57
% 2.14/1.29  Index Insertion      : 0.00
% 2.14/1.29  Index Deletion       : 0.00
% 2.14/1.29  Index Matching       : 0.00
% 2.14/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

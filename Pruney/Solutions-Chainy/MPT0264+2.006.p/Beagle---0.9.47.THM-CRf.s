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
% DateTime   : Thu Dec  3 09:52:21 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_16,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(k2_tarski(A_28,B_29),k1_tarski(B_29)) = k1_tarski(A_28)
      | B_29 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_155,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(k2_tarski(A_34,B_35),k1_tarski(A_34)) = k1_tarski(B_35)
      | B_35 = A_34 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_18,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    r1_xboole_0(k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_1')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_65])).

tff(c_168,plain,
    ( r1_xboole_0(k1_tarski('#skF_2'),'#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_68])).

tff(c_190,plain,(
    r1_xboole_0(k1_tarski('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_168])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_18,C_19,B_20] :
      ( ~ r2_hidden(A_18,C_19)
      | ~ r1_xboole_0(k2_tarski(A_18,B_20),C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_7,C_19] :
      ( ~ r2_hidden(A_7,C_19)
      | ~ r1_xboole_0(k1_tarski(A_7),C_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_196,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_190,c_78])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.24  
% 1.86/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.24  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.86/1.24  
% 1.86/1.24  %Foreground sorts:
% 1.86/1.24  
% 1.86/1.24  
% 1.86/1.24  %Background operators:
% 1.86/1.24  
% 1.86/1.24  
% 1.86/1.24  %Foreground operators:
% 1.86/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.24  
% 1.86/1.25  tff(f_52, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 1.86/1.25  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.86/1.25  tff(f_38, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.86/1.25  tff(f_29, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 1.86/1.25  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.86/1.25  tff(f_43, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.86/1.25  tff(c_16, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.25  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.25  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.25  tff(c_106, plain, (![A_28, B_29]: (k4_xboole_0(k2_tarski(A_28, B_29), k1_tarski(B_29))=k1_tarski(A_28) | B_29=A_28)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.86/1.25  tff(c_155, plain, (![A_34, B_35]: (k4_xboole_0(k2_tarski(A_34, B_35), k1_tarski(A_34))=k1_tarski(B_35) | B_35=A_34)), inference(superposition, [status(thm), theory('equality')], [c_6, c_106])).
% 1.86/1.25  tff(c_18, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.25  tff(c_65, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, k3_xboole_0(A_16, B_17)), B_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.25  tff(c_68, plain, (r1_xboole_0(k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_1')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_65])).
% 1.86/1.25  tff(c_168, plain, (r1_xboole_0(k1_tarski('#skF_2'), '#skF_3') | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_155, c_68])).
% 1.86/1.25  tff(c_190, plain, (r1_xboole_0(k1_tarski('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_14, c_168])).
% 1.86/1.25  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.25  tff(c_69, plain, (![A_18, C_19, B_20]: (~r2_hidden(A_18, C_19) | ~r1_xboole_0(k2_tarski(A_18, B_20), C_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.25  tff(c_78, plain, (![A_7, C_19]: (~r2_hidden(A_7, C_19) | ~r1_xboole_0(k1_tarski(A_7), C_19))), inference(superposition, [status(thm), theory('equality')], [c_8, c_69])).
% 1.86/1.25  tff(c_196, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_190, c_78])).
% 1.86/1.25  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_196])).
% 1.86/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.25  
% 1.86/1.25  Inference rules
% 1.86/1.25  ----------------------
% 1.86/1.25  #Ref     : 0
% 1.86/1.25  #Sup     : 47
% 1.86/1.25  #Fact    : 0
% 1.86/1.25  #Define  : 0
% 1.86/1.25  #Split   : 0
% 1.86/1.25  #Chain   : 0
% 1.86/1.25  #Close   : 0
% 1.86/1.25  
% 1.86/1.25  Ordering : KBO
% 1.86/1.25  
% 1.86/1.25  Simplification rules
% 1.86/1.25  ----------------------
% 1.86/1.25  #Subsume      : 6
% 1.86/1.25  #Demod        : 2
% 1.86/1.25  #Tautology    : 24
% 1.86/1.25  #SimpNegUnit  : 1
% 1.86/1.25  #BackRed      : 1
% 1.86/1.25  
% 1.86/1.25  #Partial instantiations: 0
% 1.86/1.25  #Strategies tried      : 1
% 1.86/1.25  
% 1.86/1.25  Timing (in seconds)
% 1.86/1.25  ----------------------
% 1.86/1.26  Preprocessing        : 0.28
% 1.86/1.26  Parsing              : 0.15
% 1.86/1.26  CNF conversion       : 0.02
% 1.86/1.26  Main loop            : 0.15
% 1.86/1.26  Inferencing          : 0.06
% 1.86/1.26  Reduction            : 0.05
% 1.86/1.26  Demodulation         : 0.04
% 1.86/1.26  BG Simplification    : 0.01
% 1.86/1.26  Subsumption          : 0.02
% 1.86/1.26  Abstraction          : 0.01
% 1.86/1.26  MUC search           : 0.00
% 1.86/1.26  Cooper               : 0.00
% 1.86/1.26  Total                : 0.45
% 1.86/1.26  Index Insertion      : 0.00
% 1.86/1.26  Index Deletion       : 0.00
% 1.86/1.26  Index Matching       : 0.00
% 1.86/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

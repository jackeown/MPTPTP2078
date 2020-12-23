%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:05 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(k2_tarski(A_40,B_41),C_42)
      | ~ r2_hidden(B_41,C_42)
      | ~ r2_hidden(A_40,C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_174,plain,(
    ! [A_43,C_44] :
      ( r1_tarski(k1_tarski(A_43),C_44)
      | ~ r2_hidden(A_43,C_44)
      | ~ r2_hidden(A_43,C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_158])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [A_45,C_46] :
      ( k3_xboole_0(k1_tarski(A_45),C_46) = k1_tarski(A_45)
      | ~ r2_hidden(A_45,C_46) ) ),
    inference(resolution,[status(thm)],[c_174,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    ! [C_47,A_48] :
      ( k3_xboole_0(C_47,k1_tarski(A_48)) = k1_tarski(A_48)
      | ~ r2_hidden(A_48,C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_2])).

tff(c_20,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_234,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_20])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.87/1.17  
% 1.87/1.17  %Foreground sorts:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Background operators:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Foreground operators:
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.17  
% 1.87/1.18  tff(f_50, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 1.87/1.18  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.87/1.18  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.87/1.18  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.87/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.87/1.18  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.18  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.18  tff(c_158, plain, (![A_40, B_41, C_42]: (r1_tarski(k2_tarski(A_40, B_41), C_42) | ~r2_hidden(B_41, C_42) | ~r2_hidden(A_40, C_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.18  tff(c_174, plain, (![A_43, C_44]: (r1_tarski(k1_tarski(A_43), C_44) | ~r2_hidden(A_43, C_44) | ~r2_hidden(A_43, C_44))), inference(superposition, [status(thm), theory('equality')], [c_8, c_158])).
% 1.87/1.18  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.18  tff(c_183, plain, (![A_45, C_46]: (k3_xboole_0(k1_tarski(A_45), C_46)=k1_tarski(A_45) | ~r2_hidden(A_45, C_46))), inference(resolution, [status(thm)], [c_174, c_4])).
% 1.87/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.18  tff(c_212, plain, (![C_47, A_48]: (k3_xboole_0(C_47, k1_tarski(A_48))=k1_tarski(A_48) | ~r2_hidden(A_48, C_47))), inference(superposition, [status(thm), theory('equality')], [c_183, c_2])).
% 1.87/1.18  tff(c_20, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.18  tff(c_234, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_212, c_20])).
% 1.87/1.18  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_234])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 57
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 0
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 3
% 1.87/1.18  #Demod        : 5
% 1.87/1.18  #Tautology    : 32
% 1.87/1.18  #SimpNegUnit  : 0
% 1.87/1.18  #BackRed      : 0
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.18  Preprocessing        : 0.28
% 1.87/1.18  Parsing              : 0.15
% 1.87/1.18  CNF conversion       : 0.01
% 1.87/1.18  Main loop            : 0.15
% 1.87/1.18  Inferencing          : 0.06
% 1.87/1.18  Reduction            : 0.05
% 1.87/1.18  Demodulation         : 0.04
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.02
% 1.87/1.18  Abstraction          : 0.01
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.45
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

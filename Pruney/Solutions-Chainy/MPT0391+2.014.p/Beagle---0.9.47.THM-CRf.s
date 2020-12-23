%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:16 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  49 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_18,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_31])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_43,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_31])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_setfam_1(B_10),A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [B_10,A_9] :
      ( k3_xboole_0(k1_setfam_1(B_10),A_9) = k1_setfam_1(B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_26])).

tff(c_77,plain,(
    ! [A_24,B_25,C_26] : k3_xboole_0(k3_xboole_0(A_24,B_25),C_26) = k3_xboole_0(A_24,k3_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [B_30,A_31,C_32] :
      ( k3_xboole_0(k1_setfam_1(B_30),k3_xboole_0(A_31,C_32)) = k3_xboole_0(k1_setfam_1(B_30),C_32)
      | ~ r2_hidden(A_31,B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_77])).

tff(c_230,plain,(
    ! [B_30] :
      ( k3_xboole_0(k1_setfam_1(B_30),k1_xboole_0) = k3_xboole_0(k1_setfam_1(B_30),'#skF_3')
      | ~ r2_hidden('#skF_1',B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_182])).

tff(c_238,plain,(
    ! [B_33] :
      ( k3_xboole_0(k1_setfam_1(B_33),'#skF_3') = k1_xboole_0
      | ~ r2_hidden('#skF_1',B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_230])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k3_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    k3_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_14])).

tff(c_253,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_24])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n018.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 17:40:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.66/1.18  
% 1.66/1.18  %Foreground sorts:
% 1.66/1.18  
% 1.66/1.18  
% 1.66/1.18  %Background operators:
% 1.66/1.18  
% 1.66/1.18  
% 1.66/1.18  %Foreground operators:
% 1.66/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.66/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.66/1.18  
% 1.95/1.18  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 1.95/1.18  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.95/1.18  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.95/1.18  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.95/1.18  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.95/1.18  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.95/1.18  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.95/1.18  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.18  tff(c_31, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.18  tff(c_42, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_31])).
% 1.95/1.18  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.95/1.18  tff(c_43, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_31])).
% 1.95/1.18  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_setfam_1(B_10), A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.18  tff(c_26, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.18  tff(c_30, plain, (![B_10, A_9]: (k3_xboole_0(k1_setfam_1(B_10), A_9)=k1_setfam_1(B_10) | ~r2_hidden(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_26])).
% 1.95/1.18  tff(c_77, plain, (![A_24, B_25, C_26]: (k3_xboole_0(k3_xboole_0(A_24, B_25), C_26)=k3_xboole_0(A_24, k3_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.18  tff(c_182, plain, (![B_30, A_31, C_32]: (k3_xboole_0(k1_setfam_1(B_30), k3_xboole_0(A_31, C_32))=k3_xboole_0(k1_setfam_1(B_30), C_32) | ~r2_hidden(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_30, c_77])).
% 1.95/1.18  tff(c_230, plain, (![B_30]: (k3_xboole_0(k1_setfam_1(B_30), k1_xboole_0)=k3_xboole_0(k1_setfam_1(B_30), '#skF_3') | ~r2_hidden('#skF_1', B_30))), inference(superposition, [status(thm), theory('equality')], [c_43, c_182])).
% 1.95/1.18  tff(c_238, plain, (![B_33]: (k3_xboole_0(k1_setfam_1(B_33), '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_1', B_33))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_230])).
% 1.95/1.18  tff(c_20, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k3_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.18  tff(c_14, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.95/1.18  tff(c_24, plain, (k3_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_14])).
% 1.95/1.18  tff(c_253, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_238, c_24])).
% 1.95/1.18  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_253])).
% 1.95/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  Inference rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Ref     : 0
% 1.95/1.18  #Sup     : 60
% 1.95/1.19  #Fact    : 0
% 1.95/1.19  #Define  : 0
% 1.95/1.19  #Split   : 1
% 1.95/1.19  #Chain   : 0
% 1.95/1.19  #Close   : 0
% 1.95/1.19  
% 1.95/1.19  Ordering : KBO
% 1.95/1.19  
% 1.95/1.19  Simplification rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Subsume      : 2
% 1.95/1.19  #Demod        : 40
% 1.95/1.19  #Tautology    : 31
% 1.95/1.19  #SimpNegUnit  : 0
% 1.95/1.19  #BackRed      : 0
% 1.95/1.19  
% 1.95/1.19  #Partial instantiations: 0
% 1.95/1.19  #Strategies tried      : 1
% 1.95/1.19  
% 1.95/1.19  Timing (in seconds)
% 1.95/1.19  ----------------------
% 1.95/1.19  Preprocessing        : 0.25
% 1.95/1.19  Parsing              : 0.14
% 1.95/1.19  CNF conversion       : 0.02
% 1.95/1.19  Main loop            : 0.19
% 1.95/1.19  Inferencing          : 0.08
% 1.95/1.19  Reduction            : 0.06
% 1.95/1.19  Demodulation         : 0.05
% 1.95/1.19  BG Simplification    : 0.01
% 1.95/1.19  Subsumption          : 0.03
% 1.95/1.19  Abstraction          : 0.01
% 1.95/1.19  MUC search           : 0.00
% 1.95/1.19  Cooper               : 0.00
% 1.95/1.19  Total                : 0.47
% 1.95/1.19  Index Insertion      : 0.00
% 1.95/1.19  Index Deletion       : 0.00
% 1.95/1.19  Index Matching       : 0.00
% 1.95/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

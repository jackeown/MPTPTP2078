%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:19 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  32 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_18,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(k1_tarski(A_10),B_11) = B_11
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k1_tarski(A_34),k2_xboole_0(k1_tarski(B_35),C_36)) = k2_xboole_0(k2_tarski(A_34,B_35),C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_267,plain,(
    ! [A_42,A_43,B_44] :
      ( k2_xboole_0(k2_tarski(A_42,A_43),B_44) = k2_xboole_0(k1_tarski(A_42),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_167])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_283,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_14])).

tff(c_295,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_283])).

tff(c_300,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_295])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:30:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.03/1.29  
% 2.03/1.29  %Foreground sorts:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Background operators:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Foreground operators:
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.29  
% 2.03/1.30  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 2.03/1.30  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.03/1.30  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.03/1.30  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.03/1.30  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.30  tff(c_10, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), B_11)=B_11 | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.30  tff(c_16, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.30  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.30  tff(c_76, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k2_xboole_0(A_25, B_26), C_27)=k2_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.30  tff(c_167, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k1_tarski(A_34), k2_xboole_0(k1_tarski(B_35), C_36))=k2_xboole_0(k2_tarski(A_34, B_35), C_36))), inference(superposition, [status(thm), theory('equality')], [c_8, c_76])).
% 2.03/1.30  tff(c_267, plain, (![A_42, A_43, B_44]: (k2_xboole_0(k2_tarski(A_42, A_43), B_44)=k2_xboole_0(k1_tarski(A_42), B_44) | ~r2_hidden(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_10, c_167])).
% 2.03/1.30  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.30  tff(c_283, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2' | ~r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_267, c_14])).
% 2.03/1.30  tff(c_295, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_283])).
% 2.03/1.30  tff(c_300, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_295])).
% 2.03/1.30  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_300])).
% 2.03/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  Inference rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Ref     : 0
% 2.03/1.30  #Sup     : 71
% 2.03/1.30  #Fact    : 0
% 2.03/1.30  #Define  : 0
% 2.03/1.30  #Split   : 0
% 2.03/1.30  #Chain   : 0
% 2.03/1.30  #Close   : 0
% 2.03/1.30  
% 2.03/1.30  Ordering : KBO
% 2.03/1.30  
% 2.03/1.30  Simplification rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Subsume      : 2
% 2.03/1.30  #Demod        : 35
% 2.03/1.30  #Tautology    : 35
% 2.03/1.30  #SimpNegUnit  : 0
% 2.03/1.30  #BackRed      : 0
% 2.03/1.30  
% 2.03/1.30  #Partial instantiations: 0
% 2.03/1.30  #Strategies tried      : 1
% 2.03/1.30  
% 2.03/1.30  Timing (in seconds)
% 2.03/1.30  ----------------------
% 2.03/1.30  Preprocessing        : 0.27
% 2.03/1.30  Parsing              : 0.16
% 2.03/1.30  CNF conversion       : 0.01
% 2.03/1.30  Main loop            : 0.21
% 2.03/1.30  Inferencing          : 0.09
% 2.03/1.30  Reduction            : 0.07
% 2.03/1.30  Demodulation         : 0.05
% 2.03/1.31  BG Simplification    : 0.01
% 2.03/1.31  Subsumption          : 0.03
% 2.03/1.31  Abstraction          : 0.01
% 2.03/1.31  MUC search           : 0.00
% 2.03/1.31  Cooper               : 0.00
% 2.03/1.31  Total                : 0.50
% 2.03/1.31  Index Insertion      : 0.00
% 2.03/1.31  Index Deletion       : 0.00
% 2.03/1.31  Index Matching       : 0.00
% 2.03/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

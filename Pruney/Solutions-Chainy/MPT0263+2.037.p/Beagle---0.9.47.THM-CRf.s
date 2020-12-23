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
% DateTime   : Thu Dec  3 09:52:18 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  37 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
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

tff(c_78,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(k1_tarski(A_25),B_26)
      | r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_82,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_24])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(k2_tarski(A_42,B_43),C_44)
      | ~ r2_hidden(B_43,C_44)
      | ~ r2_hidden(A_42,C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_151,plain,(
    ! [A_45,C_46] :
      ( r1_tarski(k1_tarski(A_45),C_46)
      | ~ r2_hidden(A_45,C_46)
      | ~ r2_hidden(A_45,C_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_134])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_47,C_48] :
      ( k3_xboole_0(k1_tarski(A_47),C_48) = k1_tarski(A_47)
      | ~ r2_hidden(A_47,C_48) ) ),
    inference(resolution,[status(thm)],[c_151,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_186,plain,(
    ! [C_49,A_50] :
      ( k3_xboole_0(C_49,k1_tarski(A_50)) = k1_tarski(A_50)
      | ~ r2_hidden(A_50,C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_2])).

tff(c_22,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_25,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_199,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_25])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.83/1.18  
% 1.83/1.18  %Foreground sorts:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Background operators:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Foreground operators:
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.18  
% 1.83/1.19  tff(f_44, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.83/1.19  tff(f_55, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.83/1.19  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.83/1.19  tff(f_50, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.83/1.19  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.83/1.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.83/1.19  tff(c_78, plain, (![A_25, B_26]: (r1_xboole_0(k1_tarski(A_25), B_26) | r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.19  tff(c_24, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.19  tff(c_82, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_24])).
% 1.83/1.19  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.19  tff(c_134, plain, (![A_42, B_43, C_44]: (r1_tarski(k2_tarski(A_42, B_43), C_44) | ~r2_hidden(B_43, C_44) | ~r2_hidden(A_42, C_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.83/1.19  tff(c_151, plain, (![A_45, C_46]: (r1_tarski(k1_tarski(A_45), C_46) | ~r2_hidden(A_45, C_46) | ~r2_hidden(A_45, C_46))), inference(superposition, [status(thm), theory('equality')], [c_8, c_134])).
% 1.83/1.19  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.19  tff(c_160, plain, (![A_47, C_48]: (k3_xboole_0(k1_tarski(A_47), C_48)=k1_tarski(A_47) | ~r2_hidden(A_47, C_48))), inference(resolution, [status(thm)], [c_151, c_4])).
% 1.83/1.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.19  tff(c_186, plain, (![C_49, A_50]: (k3_xboole_0(C_49, k1_tarski(A_50))=k1_tarski(A_50) | ~r2_hidden(A_50, C_49))), inference(superposition, [status(thm), theory('equality')], [c_160, c_2])).
% 1.83/1.19  tff(c_22, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.19  tff(c_25, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 1.83/1.19  tff(c_199, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_186, c_25])).
% 1.83/1.19  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_199])).
% 1.83/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  Inference rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Ref     : 0
% 1.83/1.19  #Sup     : 49
% 1.83/1.19  #Fact    : 0
% 1.83/1.19  #Define  : 0
% 1.83/1.19  #Split   : 0
% 1.83/1.19  #Chain   : 0
% 1.83/1.19  #Close   : 0
% 1.83/1.19  
% 1.83/1.19  Ordering : KBO
% 1.83/1.19  
% 1.83/1.19  Simplification rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Subsume      : 1
% 1.83/1.19  #Demod        : 3
% 1.83/1.19  #Tautology    : 25
% 1.83/1.19  #SimpNegUnit  : 0
% 1.83/1.19  #BackRed      : 0
% 1.83/1.19  
% 1.83/1.19  #Partial instantiations: 0
% 1.83/1.19  #Strategies tried      : 1
% 1.83/1.19  
% 1.83/1.19  Timing (in seconds)
% 1.83/1.19  ----------------------
% 1.83/1.19  Preprocessing        : 0.27
% 1.83/1.19  Parsing              : 0.14
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.15
% 1.83/1.19  Inferencing          : 0.06
% 1.83/1.19  Reduction            : 0.04
% 1.83/1.19  Demodulation         : 0.03
% 1.83/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.02
% 1.83/1.19  Abstraction          : 0.01
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.44
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.20  Index Deletion       : 0.00
% 1.83/1.20  Index Matching       : 0.00
% 1.83/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

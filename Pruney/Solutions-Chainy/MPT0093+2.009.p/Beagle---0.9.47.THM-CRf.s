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
% DateTime   : Thu Dec  3 09:44:32 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_20,B_21] : k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = k2_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_78,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_95,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k4_xboole_0(A_23,B_24),k3_xboole_0(A_23,C_25)) = k4_xboole_0(A_23,k4_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [B_24] : k4_xboole_0('#skF_1',k4_xboole_0(B_24,'#skF_3')) = k2_xboole_0(k4_xboole_0('#skF_1',B_24),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_95])).

tff(c_119,plain,(
    ! [B_24] : k4_xboole_0('#skF_1',k4_xboole_0(B_24,'#skF_3')) = k4_xboole_0('#skF_1',B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_110])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_16])).

tff(c_178,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_34])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:04:45 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.17  
% 1.73/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.18  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.73/1.18  
% 1.73/1.18  %Foreground sorts:
% 1.73/1.18  
% 1.73/1.18  
% 1.73/1.18  %Background operators:
% 1.73/1.18  
% 1.73/1.18  
% 1.73/1.18  %Foreground operators:
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.73/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.18  
% 1.79/1.19  tff(f_46, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 1.79/1.19  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.79/1.19  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.79/1.19  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.79/1.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.79/1.19  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.79/1.19  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.19  tff(c_35, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.19  tff(c_43, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_35])).
% 1.79/1.19  tff(c_10, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.19  tff(c_62, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.19  tff(c_69, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=k2_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_10])).
% 1.79/1.19  tff(c_78, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_69])).
% 1.79/1.19  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.19  tff(c_48, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.19  tff(c_52, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_48])).
% 1.79/1.19  tff(c_95, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k4_xboole_0(A_23, B_24), k3_xboole_0(A_23, C_25))=k4_xboole_0(A_23, k4_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.19  tff(c_110, plain, (![B_24]: (k4_xboole_0('#skF_1', k4_xboole_0(B_24, '#skF_3'))=k2_xboole_0(k4_xboole_0('#skF_1', B_24), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_95])).
% 1.79/1.19  tff(c_119, plain, (![B_24]: (k4_xboole_0('#skF_1', k4_xboole_0(B_24, '#skF_3'))=k4_xboole_0('#skF_1', B_24))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_110])).
% 1.79/1.19  tff(c_30, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.19  tff(c_16, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.19  tff(c_34, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_16])).
% 1.79/1.19  tff(c_178, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_34])).
% 1.79/1.19  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_178])).
% 1.79/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.19  
% 1.79/1.19  Inference rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Ref     : 0
% 1.79/1.19  #Sup     : 39
% 1.79/1.19  #Fact    : 0
% 1.79/1.19  #Define  : 0
% 1.79/1.19  #Split   : 0
% 1.79/1.19  #Chain   : 0
% 1.79/1.19  #Close   : 0
% 1.79/1.19  
% 1.79/1.19  Ordering : KBO
% 1.79/1.19  
% 1.79/1.19  Simplification rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Subsume      : 0
% 1.79/1.19  #Demod        : 13
% 1.79/1.19  #Tautology    : 25
% 1.79/1.19  #SimpNegUnit  : 0
% 1.79/1.19  #BackRed      : 1
% 1.79/1.19  
% 1.79/1.19  #Partial instantiations: 0
% 1.79/1.19  #Strategies tried      : 1
% 1.79/1.19  
% 1.79/1.19  Timing (in seconds)
% 1.79/1.19  ----------------------
% 1.79/1.19  Preprocessing        : 0.25
% 1.79/1.19  Parsing              : 0.14
% 1.79/1.19  CNF conversion       : 0.02
% 1.79/1.19  Main loop            : 0.16
% 1.79/1.19  Inferencing          : 0.08
% 1.79/1.19  Reduction            : 0.05
% 1.79/1.19  Demodulation         : 0.04
% 1.79/1.19  BG Simplification    : 0.01
% 1.79/1.19  Subsumption          : 0.02
% 1.79/1.19  Abstraction          : 0.01
% 1.79/1.19  MUC search           : 0.00
% 1.79/1.19  Cooper               : 0.00
% 1.79/1.19  Total                : 0.44
% 1.79/1.19  Index Insertion      : 0.00
% 1.79/1.19  Index Deletion       : 0.00
% 1.79/1.19  Index Matching       : 0.00
% 1.79/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

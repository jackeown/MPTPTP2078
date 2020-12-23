%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:33 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  84 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_529,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_1'(A_65,B_66,C_67),A_65)
      | r2_hidden('#skF_2'(A_65,B_66,C_67),C_67)
      | k4_xboole_0(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_630,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66,A_65),A_65)
      | k4_xboole_0(A_65,B_66) = A_65 ) ),
    inference(resolution,[status(thm)],[c_529,c_16])).

tff(c_1276,plain,(
    ! [A_98,B_99,C_100] :
      ( r2_hidden('#skF_1'(A_98,B_99,C_100),A_98)
      | r2_hidden('#skF_2'(A_98,B_99,C_100),B_99)
      | ~ r2_hidden('#skF_2'(A_98,B_99,C_100),A_98)
      | k4_xboole_0(A_98,B_99) = C_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2634,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_2'(A_121,B_122,A_121),B_122)
      | ~ r2_hidden('#skF_2'(A_121,B_122,A_121),A_121)
      | k4_xboole_0(A_121,B_122) = A_121 ) ),
    inference(resolution,[status(thm)],[c_1276,c_10])).

tff(c_2648,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_2'(A_123,B_124,A_123),B_124)
      | k4_xboole_0(A_123,B_124) = A_123 ) ),
    inference(resolution,[status(thm)],[c_630,c_2634])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_83,plain,(
    ! [D_23,B_24,A_25] :
      ( ~ r2_hidden(D_23,B_24)
      | ~ r2_hidden(D_23,k4_xboole_0(A_25,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [D_23] :
      ( ~ r2_hidden(D_23,'#skF_4')
      | ~ r2_hidden(D_23,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_83])).

tff(c_2731,plain,(
    ! [A_125] :
      ( ~ r2_hidden('#skF_2'(A_125,'#skF_3',A_125),'#skF_4')
      | k4_xboole_0(A_125,'#skF_3') = A_125 ) ),
    inference(resolution,[status(thm)],[c_2648,c_86])).

tff(c_2738,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_630,c_2731])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] : k2_xboole_0(k4_xboole_0(A_9,C_11),k4_xboole_0(B_10,C_11)) = k4_xboole_0(k2_xboole_0(A_9,B_10),C_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2763,plain,(
    ! [B_10] : k4_xboole_0(k2_xboole_0('#skF_4',B_10),'#skF_3') = k2_xboole_0('#skF_4',k4_xboole_0(B_10,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2738,c_22])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5','#skF_4'),'#skF_3') != k2_xboole_0(k4_xboole_0('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') != k2_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_28])).

tff(c_2920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2763,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.86  
% 4.47/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.86  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.47/1.86  
% 4.47/1.86  %Foreground sorts:
% 4.47/1.86  
% 4.47/1.86  
% 4.47/1.86  %Background operators:
% 4.47/1.86  
% 4.47/1.86  
% 4.47/1.86  %Foreground operators:
% 4.47/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.47/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.47/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.47/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.47/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.47/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.47/1.86  
% 4.70/1.87  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.70/1.87  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 4.70/1.87  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.70/1.87  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 4.70/1.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.70/1.87  tff(c_529, plain, (![A_65, B_66, C_67]: (r2_hidden('#skF_1'(A_65, B_66, C_67), A_65) | r2_hidden('#skF_2'(A_65, B_66, C_67), C_67) | k4_xboole_0(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.70/1.87  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.70/1.87  tff(c_630, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66, A_65), A_65) | k4_xboole_0(A_65, B_66)=A_65)), inference(resolution, [status(thm)], [c_529, c_16])).
% 4.70/1.87  tff(c_1276, plain, (![A_98, B_99, C_100]: (r2_hidden('#skF_1'(A_98, B_99, C_100), A_98) | r2_hidden('#skF_2'(A_98, B_99, C_100), B_99) | ~r2_hidden('#skF_2'(A_98, B_99, C_100), A_98) | k4_xboole_0(A_98, B_99)=C_100)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.70/1.87  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.70/1.87  tff(c_2634, plain, (![A_121, B_122]: (r2_hidden('#skF_2'(A_121, B_122, A_121), B_122) | ~r2_hidden('#skF_2'(A_121, B_122, A_121), A_121) | k4_xboole_0(A_121, B_122)=A_121)), inference(resolution, [status(thm)], [c_1276, c_10])).
% 4.70/1.87  tff(c_2648, plain, (![A_123, B_124]: (r2_hidden('#skF_2'(A_123, B_124, A_123), B_124) | k4_xboole_0(A_123, B_124)=A_123)), inference(resolution, [status(thm)], [c_630, c_2634])).
% 4.70/1.87  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.70/1.87  tff(c_65, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.70/1.87  tff(c_69, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_65])).
% 4.70/1.87  tff(c_83, plain, (![D_23, B_24, A_25]: (~r2_hidden(D_23, B_24) | ~r2_hidden(D_23, k4_xboole_0(A_25, B_24)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.70/1.87  tff(c_86, plain, (![D_23]: (~r2_hidden(D_23, '#skF_4') | ~r2_hidden(D_23, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_83])).
% 4.70/1.87  tff(c_2731, plain, (![A_125]: (~r2_hidden('#skF_2'(A_125, '#skF_3', A_125), '#skF_4') | k4_xboole_0(A_125, '#skF_3')=A_125)), inference(resolution, [status(thm)], [c_2648, c_86])).
% 4.70/1.87  tff(c_2738, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_630, c_2731])).
% 4.70/1.87  tff(c_22, plain, (![A_9, C_11, B_10]: (k2_xboole_0(k4_xboole_0(A_9, C_11), k4_xboole_0(B_10, C_11))=k4_xboole_0(k2_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.70/1.87  tff(c_2763, plain, (![B_10]: (k4_xboole_0(k2_xboole_0('#skF_4', B_10), '#skF_3')=k2_xboole_0('#skF_4', k4_xboole_0(B_10, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2738, c_22])).
% 4.70/1.87  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.70/1.87  tff(c_28, plain, (k4_xboole_0(k2_xboole_0('#skF_5', '#skF_4'), '#skF_3')!=k2_xboole_0(k4_xboole_0('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.70/1.87  tff(c_31, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')!=k2_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_28])).
% 4.70/1.87  tff(c_2920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2763, c_31])).
% 4.70/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.87  
% 4.70/1.87  Inference rules
% 4.70/1.87  ----------------------
% 4.70/1.87  #Ref     : 0
% 4.70/1.87  #Sup     : 803
% 4.70/1.87  #Fact    : 0
% 4.70/1.87  #Define  : 0
% 4.70/1.87  #Split   : 0
% 4.70/1.87  #Chain   : 0
% 4.70/1.87  #Close   : 0
% 4.70/1.87  
% 4.70/1.87  Ordering : KBO
% 4.70/1.87  
% 4.70/1.87  Simplification rules
% 4.70/1.87  ----------------------
% 4.70/1.87  #Subsume      : 169
% 4.70/1.87  #Demod        : 126
% 4.70/1.87  #Tautology    : 94
% 4.70/1.87  #SimpNegUnit  : 0
% 4.70/1.87  #BackRed      : 1
% 4.70/1.87  
% 4.70/1.87  #Partial instantiations: 0
% 4.70/1.87  #Strategies tried      : 1
% 4.70/1.87  
% 4.70/1.87  Timing (in seconds)
% 4.70/1.87  ----------------------
% 4.70/1.88  Preprocessing        : 0.27
% 4.70/1.88  Parsing              : 0.14
% 4.70/1.88  CNF conversion       : 0.02
% 4.70/1.88  Main loop            : 0.81
% 4.70/1.88  Inferencing          : 0.26
% 4.70/1.88  Reduction            : 0.31
% 4.70/1.88  Demodulation         : 0.26
% 4.70/1.88  BG Simplification    : 0.04
% 4.70/1.88  Subsumption          : 0.15
% 4.70/1.88  Abstraction          : 0.05
% 4.70/1.88  MUC search           : 0.00
% 4.70/1.88  Cooper               : 0.00
% 4.70/1.88  Total                : 1.10
% 4.70/1.88  Index Insertion      : 0.00
% 4.70/1.88  Index Deletion       : 0.00
% 4.70/1.88  Index Matching       : 0.00
% 4.70/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------

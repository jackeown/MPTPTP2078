%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:34 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  45 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_33,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_xboole_0(A_19,B_20)
      | ~ r2_hidden(C_21,B_20)
      | ~ r2_hidden(C_21,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [C_22] :
      ( ~ r2_hidden(C_22,'#skF_3')
      | ~ r2_hidden(C_22,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_33])).

tff(c_51,plain,(
    ! [A_23] :
      ( ~ r2_hidden('#skF_1'(A_23,'#skF_2'),'#skF_3')
      | r1_xboole_0(A_23,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_56,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_56,c_10])).

tff(c_82,plain,(
    ! [A_28,C_29,B_30] : k2_xboole_0(k4_xboole_0(A_28,C_29),k4_xboole_0(B_30,C_29)) = k4_xboole_0(k2_xboole_0(A_28,B_30),C_29) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_28] : k4_xboole_0(k2_xboole_0(A_28,'#skF_3'),'#skF_2') = k2_xboole_0(k4_xboole_0(A_28,'#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_82])).

tff(c_14,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') != k2_xboole_0(k4_xboole_0('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:55:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.18  
% 1.61/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.18  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.61/1.18  
% 1.61/1.18  %Foreground sorts:
% 1.61/1.18  
% 1.61/1.18  
% 1.61/1.18  %Background operators:
% 1.61/1.18  
% 1.61/1.18  
% 1.61/1.18  %Foreground operators:
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.61/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.61/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.61/1.18  
% 1.82/1.19  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.82/1.19  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 1.82/1.19  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.82/1.19  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 1.82/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.19  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.19  tff(c_16, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.82/1.19  tff(c_33, plain, (![A_19, B_20, C_21]: (~r1_xboole_0(A_19, B_20) | ~r2_hidden(C_21, B_20) | ~r2_hidden(C_21, A_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.19  tff(c_40, plain, (![C_22]: (~r2_hidden(C_22, '#skF_3') | ~r2_hidden(C_22, '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_33])).
% 1.82/1.19  tff(c_51, plain, (![A_23]: (~r2_hidden('#skF_1'(A_23, '#skF_2'), '#skF_3') | r1_xboole_0(A_23, '#skF_2'))), inference(resolution, [status(thm)], [c_4, c_40])).
% 1.82/1.19  tff(c_56, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_51])).
% 1.82/1.19  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.82/1.19  tff(c_63, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_56, c_10])).
% 1.82/1.19  tff(c_82, plain, (![A_28, C_29, B_30]: (k2_xboole_0(k4_xboole_0(A_28, C_29), k4_xboole_0(B_30, C_29))=k4_xboole_0(k2_xboole_0(A_28, B_30), C_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.82/1.19  tff(c_94, plain, (![A_28]: (k4_xboole_0(k2_xboole_0(A_28, '#skF_3'), '#skF_2')=k2_xboole_0(k4_xboole_0(A_28, '#skF_2'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_82])).
% 1.82/1.19  tff(c_14, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')!=k2_xboole_0(k4_xboole_0('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.82/1.19  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_14])).
% 1.82/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  Inference rules
% 1.82/1.19  ----------------------
% 1.82/1.19  #Ref     : 0
% 1.82/1.19  #Sup     : 36
% 1.82/1.19  #Fact    : 0
% 1.82/1.19  #Define  : 0
% 1.82/1.19  #Split   : 0
% 1.82/1.19  #Chain   : 0
% 1.82/1.19  #Close   : 0
% 1.82/1.19  
% 1.82/1.19  Ordering : KBO
% 1.82/1.19  
% 1.82/1.19  Simplification rules
% 1.82/1.19  ----------------------
% 1.82/1.19  #Subsume      : 1
% 1.82/1.19  #Demod        : 6
% 1.82/1.19  #Tautology    : 16
% 1.82/1.19  #SimpNegUnit  : 0
% 1.82/1.19  #BackRed      : 1
% 1.82/1.19  
% 1.82/1.19  #Partial instantiations: 0
% 1.82/1.19  #Strategies tried      : 1
% 1.82/1.19  
% 1.82/1.19  Timing (in seconds)
% 1.82/1.19  ----------------------
% 1.82/1.19  Preprocessing        : 0.27
% 1.82/1.19  Parsing              : 0.15
% 1.82/1.19  CNF conversion       : 0.02
% 1.82/1.19  Main loop            : 0.14
% 1.82/1.19  Inferencing          : 0.06
% 1.82/1.19  Reduction            : 0.04
% 1.82/1.19  Demodulation         : 0.03
% 1.82/1.19  BG Simplification    : 0.01
% 1.82/1.19  Subsumption          : 0.03
% 1.85/1.19  Abstraction          : 0.01
% 1.85/1.19  MUC search           : 0.00
% 1.85/1.19  Cooper               : 0.00
% 1.85/1.19  Total                : 0.43
% 1.85/1.19  Index Insertion      : 0.00
% 1.85/1.19  Index Deletion       : 0.00
% 1.85/1.19  Index Matching       : 0.00
% 1.85/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

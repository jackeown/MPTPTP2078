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
% DateTime   : Thu Dec  3 09:57:15 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  68 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_20,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [B_26,C_27,A_28] :
      ( r1_tarski(k1_setfam_1(B_26),C_27)
      | ~ r1_tarski(A_28,C_27)
      | ~ r2_hidden(A_28,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    ! [B_26,B_2] :
      ( r1_tarski(k1_setfam_1(B_26),B_2)
      | ~ r2_hidden(B_2,B_26) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k4_xboole_0(B_7,C_8))
      | ~ r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_23,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,B_14)
      | ~ r1_tarski(A_13,k4_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    ! [B_18,C_19] : r1_tarski(k4_xboole_0(B_18,C_19),B_18) ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [B_45,C_46] :
      ( k4_xboole_0(B_45,C_46) = B_45
      | ~ r1_tarski(B_45,k4_xboole_0(B_45,C_46)) ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_120,plain,(
    ! [B_7,C_8] :
      ( k4_xboole_0(B_7,C_8) = B_7
      | ~ r1_xboole_0(B_7,C_8)
      | ~ r1_tarski(B_7,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_129,plain,(
    ! [B_47,C_48] :
      ( k4_xboole_0(B_47,C_48) = B_47
      | ~ r1_xboole_0(B_47,C_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_120])).

tff(c_141,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_129])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_189,plain,(
    ! [A_50] :
      ( r1_xboole_0(A_50,'#skF_3')
      | ~ r1_tarski(A_50,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_8])).

tff(c_16,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_197,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_189,c_16])).

tff(c_200,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_79,c_197])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.19  
% 1.83/1.19  %Foreground sorts:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Background operators:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Foreground operators:
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.83/1.19  
% 1.83/1.20  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 1.83/1.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.83/1.20  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 1.83/1.20  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 1.83/1.20  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.83/1.20  tff(c_20, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.20  tff(c_70, plain, (![B_26, C_27, A_28]: (r1_tarski(k1_setfam_1(B_26), C_27) | ~r1_tarski(A_28, C_27) | ~r2_hidden(A_28, B_26))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.83/1.20  tff(c_79, plain, (![B_26, B_2]: (r1_tarski(k1_setfam_1(B_26), B_2) | ~r2_hidden(B_2, B_26))), inference(resolution, [status(thm)], [c_6, c_70])).
% 1.83/1.20  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.20  tff(c_12, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k4_xboole_0(B_7, C_8)) | ~r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.20  tff(c_23, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, B_14) | ~r1_tarski(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.20  tff(c_36, plain, (![B_18, C_19]: (r1_tarski(k4_xboole_0(B_18, C_19), B_18))), inference(resolution, [status(thm)], [c_6, c_23])).
% 1.83/1.20  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.20  tff(c_116, plain, (![B_45, C_46]: (k4_xboole_0(B_45, C_46)=B_45 | ~r1_tarski(B_45, k4_xboole_0(B_45, C_46)))), inference(resolution, [status(thm)], [c_36, c_2])).
% 1.83/1.20  tff(c_120, plain, (![B_7, C_8]: (k4_xboole_0(B_7, C_8)=B_7 | ~r1_xboole_0(B_7, C_8) | ~r1_tarski(B_7, B_7))), inference(resolution, [status(thm)], [c_12, c_116])).
% 1.83/1.20  tff(c_129, plain, (![B_47, C_48]: (k4_xboole_0(B_47, C_48)=B_47 | ~r1_xboole_0(B_47, C_48))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_120])).
% 1.83/1.20  tff(c_141, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_18, c_129])).
% 1.83/1.20  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.20  tff(c_189, plain, (![A_50]: (r1_xboole_0(A_50, '#skF_3') | ~r1_tarski(A_50, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_8])).
% 1.83/1.20  tff(c_16, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.20  tff(c_197, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_189, c_16])).
% 1.83/1.20  tff(c_200, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_79, c_197])).
% 1.83/1.20  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_200])).
% 1.83/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  Inference rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Ref     : 0
% 1.83/1.20  #Sup     : 42
% 1.83/1.20  #Fact    : 0
% 1.83/1.20  #Define  : 0
% 1.83/1.20  #Split   : 0
% 1.83/1.20  #Chain   : 0
% 1.83/1.20  #Close   : 0
% 1.83/1.20  
% 1.83/1.20  Ordering : KBO
% 1.83/1.20  
% 1.83/1.20  Simplification rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Subsume      : 1
% 1.83/1.20  #Demod        : 10
% 1.83/1.20  #Tautology    : 13
% 1.83/1.20  #SimpNegUnit  : 0
% 1.83/1.20  #BackRed      : 0
% 1.83/1.20  
% 1.83/1.20  #Partial instantiations: 0
% 1.83/1.20  #Strategies tried      : 1
% 1.83/1.20  
% 1.83/1.20  Timing (in seconds)
% 1.83/1.20  ----------------------
% 1.83/1.20  Preprocessing        : 0.27
% 1.83/1.20  Parsing              : 0.15
% 1.83/1.20  CNF conversion       : 0.02
% 1.83/1.20  Main loop            : 0.17
% 1.83/1.20  Inferencing          : 0.07
% 1.83/1.20  Reduction            : 0.04
% 1.83/1.20  Demodulation         : 0.03
% 1.83/1.20  BG Simplification    : 0.01
% 1.83/1.20  Subsumption          : 0.04
% 1.83/1.20  Abstraction          : 0.01
% 1.83/1.20  MUC search           : 0.00
% 1.83/1.20  Cooper               : 0.00
% 1.83/1.20  Total                : 0.46
% 1.83/1.20  Index Insertion      : 0.00
% 1.83/1.21  Index Deletion       : 0.00
% 1.83/1.21  Index Matching       : 0.00
% 1.83/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

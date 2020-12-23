%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:29 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   37 (  71 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  86 expanded)
%              Number of equality atoms :   19 (  57 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(c_10,plain,(
    ! [B_13] : ~ r1_xboole_0(k1_tarski(B_13),k1_tarski(B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(k1_tarski(A_14),k1_tarski(B_15))
      | B_15 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k3_xboole_0(A_32,B_33),k3_xboole_0(A_32,C_34)) = k3_xboole_0(A_32,k2_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_160,plain,(
    ! [C_34] : k3_xboole_0(k1_tarski('#skF_1'),k2_xboole_0(k1_tarski('#skF_2'),C_34)) = k2_xboole_0(k1_tarski('#skF_1'),k3_xboole_0(k1_tarski('#skF_1'),C_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_136])).

tff(c_171,plain,(
    ! [C_35] : k3_xboole_0(k1_tarski('#skF_1'),k2_xboole_0(k1_tarski('#skF_2'),C_35)) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_160])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] :
      ( k3_xboole_0(A_9,k2_xboole_0(B_10,C_11)) = k3_xboole_0(A_9,C_11)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_191,plain,(
    ! [C_35] :
      ( k3_xboole_0(k1_tarski('#skF_1'),C_35) = k1_tarski('#skF_1')
      | ~ r1_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_8])).

tff(c_393,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_396,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_393])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_396])).

tff(c_401,plain,(
    ! [C_35] : k3_xboole_0(k1_tarski('#skF_1'),C_35) = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_414,plain,(
    ! [C_46] : k3_xboole_0(k1_tarski('#skF_1'),C_46) = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_xboole_0(k3_xboole_0(C_8,A_6),k3_xboole_0(C_8,B_7))
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_436,plain,(
    ! [B_7,C_46] :
      ( r1_xboole_0(k1_tarski('#skF_1'),k3_xboole_0(k1_tarski('#skF_1'),B_7))
      | ~ r1_xboole_0(C_46,B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_6])).

tff(c_459,plain,(
    ! [C_46,B_7] :
      ( r1_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1'))
      | ~ r1_xboole_0(C_46,B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_436])).

tff(c_460,plain,(
    ! [C_46,B_7] : ~ r1_xboole_0(C_46,B_7) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_459])).

tff(c_402,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:37 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  
% 2.07/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  %$ r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.07/1.27  
% 2.07/1.27  %Foreground sorts:
% 2.07/1.27  
% 2.07/1.27  
% 2.07/1.27  %Background operators:
% 2.07/1.27  
% 2.07/1.27  
% 2.07/1.27  %Foreground operators:
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.27  
% 2.07/1.28  tff(f_42, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.07/1.28  tff(f_52, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.07/1.28  tff(f_47, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.07/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.07/1.28  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.07/1.28  tff(f_37, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.07/1.28  tff(f_33, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 2.07/1.28  tff(c_10, plain, (![B_13]: (~r1_xboole_0(k1_tarski(B_13), k1_tarski(B_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.07/1.28  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.28  tff(c_12, plain, (![A_14, B_15]: (r1_xboole_0(k1_tarski(A_14), k1_tarski(B_15)) | B_15=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.28  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.28  tff(c_16, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.28  tff(c_136, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k3_xboole_0(A_32, C_34))=k3_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.28  tff(c_160, plain, (![C_34]: (k3_xboole_0(k1_tarski('#skF_1'), k2_xboole_0(k1_tarski('#skF_2'), C_34))=k2_xboole_0(k1_tarski('#skF_1'), k3_xboole_0(k1_tarski('#skF_1'), C_34)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_136])).
% 2.07/1.28  tff(c_171, plain, (![C_35]: (k3_xboole_0(k1_tarski('#skF_1'), k2_xboole_0(k1_tarski('#skF_2'), C_35))=k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_160])).
% 2.07/1.28  tff(c_8, plain, (![A_9, B_10, C_11]: (k3_xboole_0(A_9, k2_xboole_0(B_10, C_11))=k3_xboole_0(A_9, C_11) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.28  tff(c_191, plain, (![C_35]: (k3_xboole_0(k1_tarski('#skF_1'), C_35)=k1_tarski('#skF_1') | ~r1_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_171, c_8])).
% 2.07/1.28  tff(c_393, plain, (~r1_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_191])).
% 2.07/1.28  tff(c_396, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_12, c_393])).
% 2.07/1.28  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_396])).
% 2.07/1.28  tff(c_401, plain, (![C_35]: (k3_xboole_0(k1_tarski('#skF_1'), C_35)=k1_tarski('#skF_1'))), inference(splitRight, [status(thm)], [c_191])).
% 2.07/1.28  tff(c_414, plain, (![C_46]: (k3_xboole_0(k1_tarski('#skF_1'), C_46)=k1_tarski('#skF_1'))), inference(splitRight, [status(thm)], [c_191])).
% 2.07/1.28  tff(c_6, plain, (![C_8, A_6, B_7]: (r1_xboole_0(k3_xboole_0(C_8, A_6), k3_xboole_0(C_8, B_7)) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.28  tff(c_436, plain, (![B_7, C_46]: (r1_xboole_0(k1_tarski('#skF_1'), k3_xboole_0(k1_tarski('#skF_1'), B_7)) | ~r1_xboole_0(C_46, B_7))), inference(superposition, [status(thm), theory('equality')], [c_414, c_6])).
% 2.07/1.28  tff(c_459, plain, (![C_46, B_7]: (r1_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1')) | ~r1_xboole_0(C_46, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_436])).
% 2.07/1.28  tff(c_460, plain, (![C_46, B_7]: (~r1_xboole_0(C_46, B_7))), inference(negUnitSimplification, [status(thm)], [c_10, c_459])).
% 2.07/1.28  tff(c_402, plain, (r1_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_191])).
% 2.07/1.28  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_460, c_402])).
% 2.07/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  Inference rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Ref     : 0
% 2.07/1.28  #Sup     : 112
% 2.07/1.28  #Fact    : 0
% 2.07/1.28  #Define  : 0
% 2.07/1.28  #Split   : 1
% 2.07/1.28  #Chain   : 0
% 2.07/1.28  #Close   : 0
% 2.07/1.28  
% 2.07/1.28  Ordering : KBO
% 2.07/1.28  
% 2.07/1.28  Simplification rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Subsume      : 19
% 2.07/1.28  #Demod        : 55
% 2.07/1.28  #Tautology    : 56
% 2.07/1.28  #SimpNegUnit  : 14
% 2.07/1.28  #BackRed      : 6
% 2.07/1.28  
% 2.07/1.28  #Partial instantiations: 0
% 2.07/1.28  #Strategies tried      : 1
% 2.07/1.28  
% 2.07/1.28  Timing (in seconds)
% 2.07/1.28  ----------------------
% 2.07/1.29  Preprocessing        : 0.28
% 2.07/1.29  Parsing              : 0.15
% 2.07/1.29  CNF conversion       : 0.02
% 2.07/1.29  Main loop            : 0.24
% 2.07/1.29  Inferencing          : 0.09
% 2.07/1.29  Reduction            : 0.08
% 2.07/1.29  Demodulation         : 0.06
% 2.07/1.29  BG Simplification    : 0.01
% 2.07/1.29  Subsumption          : 0.05
% 2.07/1.29  Abstraction          : 0.01
% 2.07/1.29  MUC search           : 0.00
% 2.07/1.29  Cooper               : 0.00
% 2.07/1.29  Total                : 0.55
% 2.07/1.29  Index Insertion      : 0.00
% 2.07/1.29  Index Deletion       : 0.00
% 2.07/1.29  Index Matching       : 0.00
% 2.07/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

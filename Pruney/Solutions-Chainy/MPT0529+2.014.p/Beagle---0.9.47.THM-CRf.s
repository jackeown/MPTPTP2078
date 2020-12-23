%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:13 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski('#skF_1'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(B_4,C_5) = A_3
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_tarski('#skF_1'(A_19,B_20,C_21),A_19)
      | k3_xboole_0(B_20,C_21) = A_19
      | ~ r1_tarski(A_19,C_21)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_51,plain,(
    ! [B_4,C_5] :
      ( k3_xboole_0(B_4,C_5) = C_5
      | ~ r1_tarski(C_5,C_5)
      | ~ r1_tarski(C_5,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_55,plain,(
    ! [B_22,C_23] :
      ( k3_xboole_0(B_22,C_23) = C_23
      | ~ r1_tarski(C_23,B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_51])).

tff(c_67,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_14,plain,(
    ! [A_7,B_8,C_9] :
      ( k8_relat_1(k3_xboole_0(A_7,B_8),C_9) = k8_relat_1(A_7,k8_relat_1(B_8,C_9))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,(
    ! [C_27] :
      ( k8_relat_1('#skF_3',k8_relat_1('#skF_2',C_27)) = k8_relat_1('#skF_2',C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_14])).

tff(c_16,plain,(
    k8_relat_1('#skF_3',k8_relat_1('#skF_2','#skF_4')) != k8_relat_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_124,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_16])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:07:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.19  
% 1.73/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.19  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.73/1.19  
% 1.73/1.19  %Foreground sorts:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Background operators:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Foreground operators:
% 1.73/1.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.73/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.19  
% 1.73/1.20  tff(f_55, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.73/1.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.73/1.20  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 1.73/1.20  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 1.73/1.20  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.73/1.20  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.73/1.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.20  tff(c_10, plain, (![A_3, B_4, C_5]: (r1_tarski('#skF_1'(A_3, B_4, C_5), C_5) | k3_xboole_0(B_4, C_5)=A_3 | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.73/1.20  tff(c_47, plain, (![A_19, B_20, C_21]: (~r1_tarski('#skF_1'(A_19, B_20, C_21), A_19) | k3_xboole_0(B_20, C_21)=A_19 | ~r1_tarski(A_19, C_21) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.73/1.20  tff(c_51, plain, (![B_4, C_5]: (k3_xboole_0(B_4, C_5)=C_5 | ~r1_tarski(C_5, C_5) | ~r1_tarski(C_5, B_4))), inference(resolution, [status(thm)], [c_10, c_47])).
% 1.73/1.20  tff(c_55, plain, (![B_22, C_23]: (k3_xboole_0(B_22, C_23)=C_23 | ~r1_tarski(C_23, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_51])).
% 1.73/1.20  tff(c_67, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_18, c_55])).
% 1.73/1.20  tff(c_14, plain, (![A_7, B_8, C_9]: (k8_relat_1(k3_xboole_0(A_7, B_8), C_9)=k8_relat_1(A_7, k8_relat_1(B_8, C_9)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.20  tff(c_115, plain, (![C_27]: (k8_relat_1('#skF_3', k8_relat_1('#skF_2', C_27))=k8_relat_1('#skF_2', C_27) | ~v1_relat_1(C_27))), inference(superposition, [status(thm), theory('equality')], [c_67, c_14])).
% 1.73/1.20  tff(c_16, plain, (k8_relat_1('#skF_3', k8_relat_1('#skF_2', '#skF_4'))!=k8_relat_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.73/1.20  tff(c_124, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_115, c_16])).
% 1.73/1.20  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_124])).
% 1.73/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.20  
% 1.73/1.20  Inference rules
% 1.73/1.20  ----------------------
% 1.73/1.20  #Ref     : 0
% 1.73/1.20  #Sup     : 27
% 1.73/1.20  #Fact    : 0
% 1.73/1.20  #Define  : 0
% 1.73/1.20  #Split   : 1
% 1.73/1.20  #Chain   : 0
% 1.73/1.20  #Close   : 0
% 1.73/1.20  
% 1.73/1.20  Ordering : KBO
% 1.73/1.20  
% 1.73/1.20  Simplification rules
% 1.73/1.20  ----------------------
% 1.73/1.20  #Subsume      : 0
% 1.73/1.20  #Demod        : 4
% 1.73/1.20  #Tautology    : 14
% 1.73/1.20  #SimpNegUnit  : 0
% 1.73/1.20  #BackRed      : 0
% 1.73/1.20  
% 1.73/1.20  #Partial instantiations: 0
% 1.73/1.20  #Strategies tried      : 1
% 1.73/1.20  
% 1.73/1.20  Timing (in seconds)
% 1.73/1.20  ----------------------
% 1.73/1.20  Preprocessing        : 0.27
% 1.73/1.20  Parsing              : 0.15
% 1.73/1.20  CNF conversion       : 0.02
% 1.73/1.20  Main loop            : 0.14
% 1.73/1.20  Inferencing          : 0.06
% 1.73/1.21  Reduction            : 0.03
% 1.73/1.21  Demodulation         : 0.02
% 1.73/1.21  BG Simplification    : 0.01
% 1.73/1.21  Subsumption          : 0.03
% 1.73/1.21  Abstraction          : 0.01
% 1.73/1.21  MUC search           : 0.00
% 1.73/1.21  Cooper               : 0.00
% 1.73/1.21  Total                : 0.44
% 1.73/1.21  Index Insertion      : 0.00
% 1.73/1.21  Index Deletion       : 0.00
% 1.73/1.21  Index Matching       : 0.00
% 1.73/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

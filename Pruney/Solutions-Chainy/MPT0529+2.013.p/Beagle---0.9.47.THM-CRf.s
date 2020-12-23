%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:13 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   41 (  52 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,k3_xboole_0(B_6,C_7))
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_18,B_19,C_20] : r1_tarski(k2_xboole_0(k3_xboole_0(A_18,B_19),k3_xboole_0(A_18,C_20)),k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),k2_xboole_0(B_19,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_43])).

tff(c_60,plain,(
    ! [A_24,B_25] : r1_tarski(k3_xboole_0(A_24,B_25),B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_49])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(B_27,k3_xboole_0(A_26,B_27)) ) ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_69,plain,(
    ! [B_6,C_7] :
      ( k3_xboole_0(B_6,C_7) = C_7
      | ~ r1_tarski(C_7,C_7)
      | ~ r1_tarski(C_7,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_65])).

tff(c_73,plain,(
    ! [B_28,C_29] :
      ( k3_xboole_0(B_28,C_29) = C_29
      | ~ r1_tarski(C_29,B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_93,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_73])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( k8_relat_1(k3_xboole_0(A_11,B_12),C_13) = k8_relat_1(A_11,k8_relat_1(B_12,C_13))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_306,plain,(
    ! [C_42] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',C_42)) = k8_relat_1('#skF_1',C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_14])).

tff(c_16,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_312,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_16])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:26:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.99/1.21  
% 1.99/1.21  %Foreground sorts:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Background operators:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Foreground operators:
% 1.99/1.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.21  
% 1.99/1.22  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.99/1.22  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.99/1.22  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.99/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.99/1.22  tff(f_41, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.99/1.22  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 1.99/1.22  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.22  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.22  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.22  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, k3_xboole_0(B_6, C_7)) | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.22  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.22  tff(c_43, plain, (![A_18, B_19, C_20]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_18, B_19), k3_xboole_0(A_18, C_20)), k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.22  tff(c_49, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), k2_xboole_0(B_19, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_43])).
% 1.99/1.22  tff(c_60, plain, (![A_24, B_25]: (r1_tarski(k3_xboole_0(A_24, B_25), B_25))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_49])).
% 1.99/1.22  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.22  tff(c_65, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(B_27, k3_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_60, c_4])).
% 1.99/1.22  tff(c_69, plain, (![B_6, C_7]: (k3_xboole_0(B_6, C_7)=C_7 | ~r1_tarski(C_7, C_7) | ~r1_tarski(C_7, B_6))), inference(resolution, [status(thm)], [c_10, c_65])).
% 1.99/1.22  tff(c_73, plain, (![B_28, C_29]: (k3_xboole_0(B_28, C_29)=C_29 | ~r1_tarski(C_29, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_69])).
% 1.99/1.22  tff(c_93, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_18, c_73])).
% 1.99/1.22  tff(c_14, plain, (![A_11, B_12, C_13]: (k8_relat_1(k3_xboole_0(A_11, B_12), C_13)=k8_relat_1(A_11, k8_relat_1(B_12, C_13)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.22  tff(c_306, plain, (![C_42]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', C_42))=k8_relat_1('#skF_1', C_42) | ~v1_relat_1(C_42))), inference(superposition, [status(thm), theory('equality')], [c_93, c_14])).
% 1.99/1.22  tff(c_16, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.22  tff(c_312, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_306, c_16])).
% 1.99/1.22  tff(c_320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_312])).
% 1.99/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  Inference rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Ref     : 0
% 1.99/1.22  #Sup     : 72
% 1.99/1.22  #Fact    : 0
% 1.99/1.22  #Define  : 0
% 1.99/1.22  #Split   : 1
% 1.99/1.22  #Chain   : 0
% 1.99/1.22  #Close   : 0
% 1.99/1.22  
% 1.99/1.22  Ordering : KBO
% 1.99/1.22  
% 1.99/1.22  Simplification rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Subsume      : 0
% 1.99/1.22  #Demod        : 48
% 1.99/1.22  #Tautology    : 43
% 1.99/1.22  #SimpNegUnit  : 0
% 1.99/1.22  #BackRed      : 0
% 1.99/1.22  
% 1.99/1.22  #Partial instantiations: 0
% 1.99/1.22  #Strategies tried      : 1
% 1.99/1.22  
% 1.99/1.22  Timing (in seconds)
% 1.99/1.22  ----------------------
% 1.99/1.22  Preprocessing        : 0.27
% 1.99/1.22  Parsing              : 0.16
% 1.99/1.22  CNF conversion       : 0.02
% 1.99/1.22  Main loop            : 0.19
% 1.99/1.22  Inferencing          : 0.07
% 1.99/1.22  Reduction            : 0.06
% 1.99/1.22  Demodulation         : 0.05
% 1.99/1.22  BG Simplification    : 0.01
% 1.99/1.22  Subsumption          : 0.04
% 1.99/1.23  Abstraction          : 0.01
% 1.99/1.23  MUC search           : 0.00
% 1.99/1.23  Cooper               : 0.00
% 1.99/1.23  Total                : 0.49
% 1.99/1.23  Index Insertion      : 0.00
% 1.99/1.23  Index Deletion       : 0.00
% 1.99/1.23  Index Matching       : 0.00
% 1.99/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

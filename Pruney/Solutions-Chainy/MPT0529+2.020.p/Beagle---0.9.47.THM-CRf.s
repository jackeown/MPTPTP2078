%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:14 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  49 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_20,B_21)),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(k2_relat_1(k8_relat_1(A_24,B_25)),A_24) = A_24
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_32,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_26,B_27)),C_28)
      | ~ r1_tarski(A_26,C_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k8_relat_1(A_10,B_11) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    ! [C_36,A_37,B_38] :
      ( k8_relat_1(C_36,k8_relat_1(A_37,B_38)) = k8_relat_1(A_37,B_38)
      | ~ v1_relat_1(k8_relat_1(A_37,B_38))
      | ~ r1_tarski(A_37,C_36)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_54,c_10])).

tff(c_126,plain,(
    ! [C_39,A_40,B_41] :
      ( k8_relat_1(C_39,k8_relat_1(A_40,B_41)) = k8_relat_1(A_40,B_41)
      | ~ r1_tarski(A_40,C_39)
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_12,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_154,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_12])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 11:09:24 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.23  
% 1.93/1.23  %Foreground sorts:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Background operators:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Foreground operators:
% 1.93/1.23  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.23  
% 1.94/1.24  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.94/1.24  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.94/1.24  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 1.94/1.24  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.94/1.24  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.94/1.24  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.94/1.24  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.24  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.24  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.24  tff(c_32, plain, (![A_20, B_21]: (r1_tarski(k2_relat_1(k8_relat_1(A_20, B_21)), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.24  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.24  tff(c_42, plain, (![A_24, B_25]: (k2_xboole_0(k2_relat_1(k8_relat_1(A_24, B_25)), A_24)=A_24 | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_32, c_4])).
% 1.94/1.24  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.24  tff(c_54, plain, (![A_26, B_27, C_28]: (r1_tarski(k2_relat_1(k8_relat_1(A_26, B_27)), C_28) | ~r1_tarski(A_26, C_28) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2])).
% 1.94/1.24  tff(c_10, plain, (![A_10, B_11]: (k8_relat_1(A_10, B_11)=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.94/1.24  tff(c_120, plain, (![C_36, A_37, B_38]: (k8_relat_1(C_36, k8_relat_1(A_37, B_38))=k8_relat_1(A_37, B_38) | ~v1_relat_1(k8_relat_1(A_37, B_38)) | ~r1_tarski(A_37, C_36) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_54, c_10])).
% 1.94/1.24  tff(c_126, plain, (![C_39, A_40, B_41]: (k8_relat_1(C_39, k8_relat_1(A_40, B_41))=k8_relat_1(A_40, B_41) | ~r1_tarski(A_40, C_39) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_6, c_120])).
% 1.94/1.24  tff(c_12, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.24  tff(c_154, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_126, c_12])).
% 1.94/1.24  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_154])).
% 1.94/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  Inference rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Ref     : 0
% 1.94/1.24  #Sup     : 42
% 1.94/1.24  #Fact    : 0
% 1.94/1.24  #Define  : 0
% 1.94/1.24  #Split   : 0
% 1.94/1.24  #Chain   : 0
% 1.94/1.24  #Close   : 0
% 1.94/1.24  
% 1.94/1.24  Ordering : KBO
% 1.94/1.24  
% 1.94/1.24  Simplification rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Subsume      : 9
% 1.94/1.24  #Demod        : 2
% 1.94/1.24  #Tautology    : 15
% 1.94/1.24  #SimpNegUnit  : 0
% 1.94/1.24  #BackRed      : 0
% 1.94/1.24  
% 1.94/1.24  #Partial instantiations: 0
% 1.94/1.24  #Strategies tried      : 1
% 1.94/1.24  
% 1.94/1.24  Timing (in seconds)
% 1.94/1.24  ----------------------
% 1.94/1.25  Preprocessing        : 0.25
% 1.94/1.25  Parsing              : 0.14
% 1.94/1.25  CNF conversion       : 0.02
% 1.94/1.25  Main loop            : 0.21
% 1.94/1.25  Inferencing          : 0.11
% 1.94/1.25  Reduction            : 0.04
% 1.94/1.25  Demodulation         : 0.03
% 1.94/1.25  BG Simplification    : 0.01
% 1.94/1.25  Subsumption          : 0.03
% 1.94/1.25  Abstraction          : 0.01
% 1.94/1.25  MUC search           : 0.00
% 1.94/1.25  Cooper               : 0.00
% 1.94/1.25  Total                : 0.49
% 1.94/1.25  Index Insertion      : 0.00
% 1.94/1.25  Index Deletion       : 0.00
% 1.94/1.25  Index Matching       : 0.00
% 1.94/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

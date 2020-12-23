%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:50 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
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
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

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
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [B_20,A_21] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_20,A_21)),A_21)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [B_24,A_25] :
      ( k2_xboole_0(k1_relat_1(k7_relat_1(B_24,A_25)),A_25) = A_25
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_32,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [B_26,A_27,C_28] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_26,A_27)),C_28)
      | ~ r1_tarski(A_27,C_28)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    ! [B_36,A_37,C_38] :
      ( k7_relat_1(k7_relat_1(B_36,A_37),C_38) = k7_relat_1(B_36,A_37)
      | ~ v1_relat_1(k7_relat_1(B_36,A_37))
      | ~ r1_tarski(A_37,C_38)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_54,c_10])).

tff(c_126,plain,(
    ! [A_39,B_40,C_41] :
      ( k7_relat_1(k7_relat_1(A_39,B_40),C_41) = k7_relat_1(A_39,B_40)
      | ~ r1_tarski(B_40,C_41)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_12,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.16  
% 1.64/1.16  %Foreground sorts:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Background operators:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Foreground operators:
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.16  
% 1.64/1.17  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.64/1.17  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.64/1.17  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 1.64/1.17  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.64/1.17  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.64/1.17  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.64/1.17  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.17  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.17  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.17  tff(c_32, plain, (![B_20, A_21]: (r1_tarski(k1_relat_1(k7_relat_1(B_20, A_21)), A_21) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.17  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.17  tff(c_42, plain, (![B_24, A_25]: (k2_xboole_0(k1_relat_1(k7_relat_1(B_24, A_25)), A_25)=A_25 | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_32, c_4])).
% 1.64/1.17  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.17  tff(c_54, plain, (![B_26, A_27, C_28]: (r1_tarski(k1_relat_1(k7_relat_1(B_26, A_27)), C_28) | ~r1_tarski(A_27, C_28) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2])).
% 1.64/1.17  tff(c_10, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.17  tff(c_120, plain, (![B_36, A_37, C_38]: (k7_relat_1(k7_relat_1(B_36, A_37), C_38)=k7_relat_1(B_36, A_37) | ~v1_relat_1(k7_relat_1(B_36, A_37)) | ~r1_tarski(A_37, C_38) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_54, c_10])).
% 1.64/1.17  tff(c_126, plain, (![A_39, B_40, C_41]: (k7_relat_1(k7_relat_1(A_39, B_40), C_41)=k7_relat_1(A_39, B_40) | ~r1_tarski(B_40, C_41) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_6, c_120])).
% 1.64/1.17  tff(c_12, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.17  tff(c_154, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_126, c_12])).
% 1.64/1.17  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_154])).
% 1.64/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  Inference rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Ref     : 0
% 1.64/1.17  #Sup     : 42
% 1.64/1.17  #Fact    : 0
% 1.64/1.17  #Define  : 0
% 1.64/1.17  #Split   : 0
% 1.64/1.17  #Chain   : 0
% 1.64/1.17  #Close   : 0
% 1.64/1.17  
% 1.64/1.17  Ordering : KBO
% 1.64/1.17  
% 1.64/1.17  Simplification rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Subsume      : 9
% 1.64/1.17  #Demod        : 2
% 1.64/1.17  #Tautology    : 15
% 1.64/1.17  #SimpNegUnit  : 0
% 1.64/1.17  #BackRed      : 0
% 1.64/1.17  
% 1.64/1.17  #Partial instantiations: 0
% 1.64/1.17  #Strategies tried      : 1
% 1.64/1.17  
% 1.64/1.17  Timing (in seconds)
% 1.64/1.17  ----------------------
% 1.64/1.17  Preprocessing        : 0.26
% 1.64/1.17  Parsing              : 0.15
% 1.64/1.17  CNF conversion       : 0.02
% 1.64/1.17  Main loop            : 0.16
% 1.64/1.17  Inferencing          : 0.08
% 1.64/1.17  Reduction            : 0.04
% 1.64/1.17  Demodulation         : 0.03
% 1.64/1.17  BG Simplification    : 0.01
% 1.64/1.17  Subsumption          : 0.03
% 1.64/1.17  Abstraction          : 0.01
% 1.64/1.17  MUC search           : 0.00
% 1.64/1.17  Cooper               : 0.00
% 1.64/1.17  Total                : 0.45
% 1.64/1.17  Index Insertion      : 0.00
% 1.64/1.18  Index Deletion       : 0.00
% 1.64/1.18  Index Matching       : 0.00
% 1.64/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

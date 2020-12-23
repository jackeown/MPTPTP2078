%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:16 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  43 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k8_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_17])).

tff(c_39,plain,(
    ! [A_18,B_19,C_20] :
      ( k8_relat_1(k3_xboole_0(A_18,B_19),C_20) = k8_relat_1(A_18,k8_relat_1(B_19,C_20))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [C_21] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',C_21)) = k8_relat_1('#skF_1',C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_39])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k8_relat_1(A_5,B_6),B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [C_28] :
      ( r1_tarski(k8_relat_1('#skF_1',C_28),k8_relat_1('#skF_2',C_28))
      | ~ v1_relat_1(k8_relat_1('#skF_2',C_28))
      | ~ v1_relat_1(C_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_6])).

tff(c_10,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_113,c_10])).

tff(c_125,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_116])).

tff(c_129,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_125])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:22:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.15  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.81/1.15  
% 1.81/1.15  %Foreground sorts:
% 1.81/1.15  
% 1.81/1.15  
% 1.81/1.15  %Background operators:
% 1.81/1.15  
% 1.81/1.15  
% 1.81/1.15  %Foreground operators:
% 1.81/1.15  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.81/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.15  
% 1.81/1.15  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_relat_1)).
% 1.81/1.15  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.81/1.15  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.81/1.15  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 1.81/1.15  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.81/1.15  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.15  tff(c_4, plain, (![A_3, B_4]: (v1_relat_1(k8_relat_1(A_3, B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.15  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.15  tff(c_17, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.15  tff(c_25, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_12, c_17])).
% 1.81/1.15  tff(c_39, plain, (![A_18, B_19, C_20]: (k8_relat_1(k3_xboole_0(A_18, B_19), C_20)=k8_relat_1(A_18, k8_relat_1(B_19, C_20)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.15  tff(c_63, plain, (![C_21]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', C_21))=k8_relat_1('#skF_1', C_21) | ~v1_relat_1(C_21))), inference(superposition, [status(thm), theory('equality')], [c_25, c_39])).
% 1.81/1.15  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k8_relat_1(A_5, B_6), B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.81/1.15  tff(c_113, plain, (![C_28]: (r1_tarski(k8_relat_1('#skF_1', C_28), k8_relat_1('#skF_2', C_28)) | ~v1_relat_1(k8_relat_1('#skF_2', C_28)) | ~v1_relat_1(C_28))), inference(superposition, [status(thm), theory('equality')], [c_63, c_6])).
% 1.81/1.15  tff(c_10, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.15  tff(c_116, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_113, c_10])).
% 1.81/1.15  tff(c_125, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_116])).
% 1.81/1.15  tff(c_129, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_125])).
% 1.81/1.15  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_129])).
% 1.81/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.15  
% 1.81/1.15  Inference rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Ref     : 0
% 1.81/1.15  #Sup     : 31
% 1.81/1.15  #Fact    : 0
% 1.81/1.15  #Define  : 0
% 1.81/1.15  #Split   : 0
% 1.81/1.15  #Chain   : 0
% 1.81/1.15  #Close   : 0
% 1.81/1.15  
% 1.81/1.15  Ordering : KBO
% 1.81/1.15  
% 1.81/1.15  Simplification rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Subsume      : 3
% 1.81/1.15  #Demod        : 2
% 1.81/1.15  #Tautology    : 8
% 1.81/1.15  #SimpNegUnit  : 0
% 1.81/1.15  #BackRed      : 0
% 1.81/1.15  
% 1.81/1.15  #Partial instantiations: 0
% 1.81/1.15  #Strategies tried      : 1
% 1.81/1.15  
% 1.81/1.15  Timing (in seconds)
% 1.81/1.15  ----------------------
% 1.81/1.16  Preprocessing        : 0.26
% 1.81/1.16  Parsing              : 0.15
% 1.81/1.16  CNF conversion       : 0.02
% 1.81/1.16  Main loop            : 0.14
% 1.81/1.16  Inferencing          : 0.06
% 1.81/1.16  Reduction            : 0.03
% 1.81/1.16  Demodulation         : 0.03
% 1.81/1.16  BG Simplification    : 0.01
% 1.81/1.16  Subsumption          : 0.02
% 1.81/1.16  Abstraction          : 0.01
% 1.81/1.16  MUC search           : 0.00
% 1.81/1.16  Cooper               : 0.00
% 1.81/1.16  Total                : 0.42
% 1.81/1.16  Index Insertion      : 0.00
% 1.81/1.16  Index Deletion       : 0.00
% 1.81/1.16  Index Matching       : 0.00
% 1.81/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

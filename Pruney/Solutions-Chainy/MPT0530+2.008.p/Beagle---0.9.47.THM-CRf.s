%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:15 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  25 expanded)
%              Number of equality atoms :    8 (  10 expanded)
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

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8,c_11])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( k8_relat_1(k3_xboole_0(A_8,B_9),C_10) = k8_relat_1(A_8,k8_relat_1(B_9,C_10))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [C_11] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',C_11)) = k8_relat_1('#skF_1',C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_20])).

tff(c_6,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_46,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.13  
% 1.50/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.13  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.50/1.13  
% 1.50/1.13  %Foreground sorts:
% 1.50/1.13  
% 1.50/1.13  
% 1.50/1.13  %Background operators:
% 1.50/1.13  
% 1.50/1.13  
% 1.50/1.13  %Foreground operators:
% 1.50/1.13  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.50/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.50/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.50/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.50/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.50/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.50/1.13  
% 1.50/1.14  tff(f_40, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_relat_1)).
% 1.50/1.14  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.50/1.14  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 1.50/1.14  tff(c_10, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.50/1.14  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.50/1.14  tff(c_11, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.50/1.14  tff(c_15, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_8, c_11])).
% 1.50/1.14  tff(c_20, plain, (![A_8, B_9, C_10]: (k8_relat_1(k3_xboole_0(A_8, B_9), C_10)=k8_relat_1(A_8, k8_relat_1(B_9, C_10)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.50/1.14  tff(c_32, plain, (![C_11]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', C_11))=k8_relat_1('#skF_1', C_11) | ~v1_relat_1(C_11))), inference(superposition, [status(thm), theory('equality')], [c_15, c_20])).
% 1.50/1.14  tff(c_6, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.50/1.14  tff(c_38, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_6])).
% 1.50/1.14  tff(c_46, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_38])).
% 1.50/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.14  
% 1.50/1.14  Inference rules
% 1.50/1.14  ----------------------
% 1.50/1.14  #Ref     : 0
% 1.50/1.14  #Sup     : 9
% 1.50/1.14  #Fact    : 0
% 1.50/1.14  #Define  : 0
% 1.50/1.14  #Split   : 0
% 1.50/1.14  #Chain   : 0
% 1.50/1.14  #Close   : 0
% 1.50/1.14  
% 1.50/1.14  Ordering : KBO
% 1.50/1.14  
% 1.50/1.14  Simplification rules
% 1.50/1.14  ----------------------
% 1.50/1.14  #Subsume      : 0
% 1.50/1.14  #Demod        : 1
% 1.50/1.14  #Tautology    : 5
% 1.50/1.14  #SimpNegUnit  : 0
% 1.50/1.14  #BackRed      : 0
% 1.50/1.14  
% 1.50/1.14  #Partial instantiations: 0
% 1.50/1.14  #Strategies tried      : 1
% 1.50/1.14  
% 1.50/1.14  Timing (in seconds)
% 1.50/1.14  ----------------------
% 1.61/1.14  Preprocessing        : 0.26
% 1.61/1.14  Parsing              : 0.15
% 1.61/1.14  CNF conversion       : 0.01
% 1.61/1.14  Main loop            : 0.08
% 1.61/1.14  Inferencing          : 0.04
% 1.61/1.14  Reduction            : 0.02
% 1.61/1.14  Demodulation         : 0.01
% 1.61/1.14  BG Simplification    : 0.01
% 1.61/1.14  Subsumption          : 0.01
% 1.61/1.14  Abstraction          : 0.00
% 1.61/1.14  MUC search           : 0.00
% 1.61/1.14  Cooper               : 0.00
% 1.61/1.14  Total                : 0.35
% 1.61/1.14  Index Insertion      : 0.00
% 1.61/1.14  Index Deletion       : 0.00
% 1.61/1.14  Index Matching       : 0.00
% 1.61/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

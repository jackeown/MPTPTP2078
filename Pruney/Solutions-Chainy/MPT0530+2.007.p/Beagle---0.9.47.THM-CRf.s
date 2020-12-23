%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:15 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  31 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_29])).

tff(c_51,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_51])).

tff(c_72,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_147,plain,(
    ! [A_24,B_25,C_26] :
      ( k8_relat_1(k3_xboole_0(A_24,B_25),C_26) = k8_relat_1(A_24,k8_relat_1(B_25,C_26))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_163,plain,(
    ! [C_27] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',C_27)) = k8_relat_1('#skF_1',C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_147])).

tff(c_14,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_169,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_14])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.22  
% 1.85/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.22  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.85/1.22  
% 1.85/1.22  %Foreground sorts:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Background operators:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Foreground operators:
% 1.85/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.85/1.22  
% 1.85/1.23  tff(f_46, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_relat_1)).
% 1.85/1.23  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.85/1.23  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.85/1.23  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.85/1.23  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 1.85/1.23  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.23  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.23  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.23  tff(c_29, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.23  tff(c_37, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_29])).
% 1.85/1.23  tff(c_51, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.23  tff(c_66, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_37, c_51])).
% 1.85/1.23  tff(c_72, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_66])).
% 1.85/1.23  tff(c_147, plain, (![A_24, B_25, C_26]: (k8_relat_1(k3_xboole_0(A_24, B_25), C_26)=k8_relat_1(A_24, k8_relat_1(B_25, C_26)) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.85/1.23  tff(c_163, plain, (![C_27]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', C_27))=k8_relat_1('#skF_1', C_27) | ~v1_relat_1(C_27))), inference(superposition, [status(thm), theory('equality')], [c_72, c_147])).
% 1.85/1.23  tff(c_14, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.23  tff(c_169, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_163, c_14])).
% 1.85/1.23  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_169])).
% 1.85/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.23  
% 1.85/1.23  Inference rules
% 1.85/1.23  ----------------------
% 1.85/1.23  #Ref     : 0
% 1.85/1.23  #Sup     : 41
% 1.85/1.23  #Fact    : 0
% 1.85/1.23  #Define  : 0
% 1.85/1.23  #Split   : 0
% 1.85/1.23  #Chain   : 0
% 1.85/1.23  #Close   : 0
% 1.85/1.23  
% 1.85/1.23  Ordering : KBO
% 1.85/1.23  
% 1.85/1.23  Simplification rules
% 1.85/1.23  ----------------------
% 1.85/1.23  #Subsume      : 0
% 1.85/1.23  #Demod        : 13
% 1.85/1.23  #Tautology    : 29
% 1.85/1.23  #SimpNegUnit  : 0
% 1.85/1.23  #BackRed      : 0
% 1.85/1.23  
% 1.85/1.23  #Partial instantiations: 0
% 1.85/1.23  #Strategies tried      : 1
% 1.85/1.23  
% 1.85/1.23  Timing (in seconds)
% 1.85/1.23  ----------------------
% 1.85/1.24  Preprocessing        : 0.28
% 1.85/1.24  Parsing              : 0.16
% 1.85/1.24  CNF conversion       : 0.02
% 1.85/1.24  Main loop            : 0.14
% 1.85/1.24  Inferencing          : 0.06
% 1.85/1.24  Reduction            : 0.04
% 1.85/1.24  Demodulation         : 0.03
% 1.85/1.24  BG Simplification    : 0.01
% 1.85/1.24  Subsumption          : 0.02
% 1.85/1.24  Abstraction          : 0.01
% 1.85/1.24  MUC search           : 0.00
% 1.85/1.24  Cooper               : 0.00
% 1.85/1.24  Total                : 0.44
% 1.85/1.24  Index Insertion      : 0.00
% 1.85/1.24  Index Deletion       : 0.00
% 1.85/1.24  Index Matching       : 0.00
% 1.85/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

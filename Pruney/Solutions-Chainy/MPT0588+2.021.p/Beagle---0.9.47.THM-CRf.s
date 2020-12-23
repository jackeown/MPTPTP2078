%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:05 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  42 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [C_18,A_16,B_17] :
      ( k7_relat_1(k7_relat_1(C_18,A_16),B_17) = k7_relat_1(C_18,k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_20,A_19)),k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_86,plain,(
    ! [B_36,A_37] :
      ( k7_relat_1(B_36,A_37) = B_36
      | ~ r1_tarski(k1_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,(
    ! [B_45,A_46] :
      ( k7_relat_1(k7_relat_1(B_45,A_46),k1_relat_1(B_45)) = k7_relat_1(B_45,A_46)
      | ~ v1_relat_1(k7_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_16,c_86])).

tff(c_176,plain,(
    ! [C_50,A_51] :
      ( k7_relat_1(C_50,k3_xboole_0(A_51,k1_relat_1(C_50))) = k7_relat_1(C_50,A_51)
      | ~ v1_relat_1(k7_relat_1(C_50,A_51))
      | ~ v1_relat_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_121])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_23,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_198,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_23])).

tff(c_223,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_198])).

tff(c_227,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_223])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.92/1.19  
% 1.92/1.19  %Foreground sorts:
% 1.92/1.19  
% 1.92/1.19  
% 1.92/1.19  %Background operators:
% 1.92/1.19  
% 1.92/1.19  
% 1.92/1.19  %Foreground operators:
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.92/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.92/1.19  
% 1.92/1.20  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 1.92/1.20  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.92/1.20  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.92/1.20  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 1.92/1.20  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.92/1.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.92/1.20  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.92/1.20  tff(c_12, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.20  tff(c_14, plain, (![C_18, A_16, B_17]: (k7_relat_1(k7_relat_1(C_18, A_16), B_17)=k7_relat_1(C_18, k3_xboole_0(A_16, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.20  tff(c_16, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_20, A_19)), k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.20  tff(c_86, plain, (![B_36, A_37]: (k7_relat_1(B_36, A_37)=B_36 | ~r1_tarski(k1_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.20  tff(c_121, plain, (![B_45, A_46]: (k7_relat_1(k7_relat_1(B_45, A_46), k1_relat_1(B_45))=k7_relat_1(B_45, A_46) | ~v1_relat_1(k7_relat_1(B_45, A_46)) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_16, c_86])).
% 1.92/1.20  tff(c_176, plain, (![C_50, A_51]: (k7_relat_1(C_50, k3_xboole_0(A_51, k1_relat_1(C_50)))=k7_relat_1(C_50, A_51) | ~v1_relat_1(k7_relat_1(C_50, A_51)) | ~v1_relat_1(C_50) | ~v1_relat_1(C_50))), inference(superposition, [status(thm), theory('equality')], [c_14, c_121])).
% 1.92/1.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.20  tff(c_20, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.92/1.20  tff(c_23, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 1.92/1.20  tff(c_198, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_176, c_23])).
% 1.92/1.20  tff(c_223, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_198])).
% 1.92/1.20  tff(c_227, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_223])).
% 1.92/1.20  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_227])).
% 1.92/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  Inference rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Ref     : 0
% 1.92/1.20  #Sup     : 53
% 1.92/1.20  #Fact    : 0
% 1.92/1.20  #Define  : 0
% 1.92/1.20  #Split   : 0
% 1.92/1.20  #Chain   : 0
% 1.92/1.20  #Close   : 0
% 1.92/1.20  
% 1.92/1.20  Ordering : KBO
% 1.92/1.20  
% 1.92/1.20  Simplification rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Subsume      : 6
% 1.92/1.20  #Demod        : 3
% 1.92/1.20  #Tautology    : 22
% 1.92/1.20  #SimpNegUnit  : 0
% 1.92/1.20  #BackRed      : 0
% 1.92/1.20  
% 1.92/1.20  #Partial instantiations: 0
% 1.92/1.20  #Strategies tried      : 1
% 1.92/1.20  
% 1.92/1.20  Timing (in seconds)
% 1.92/1.20  ----------------------
% 1.92/1.20  Preprocessing        : 0.28
% 1.92/1.20  Parsing              : 0.16
% 1.92/1.20  CNF conversion       : 0.01
% 1.92/1.20  Main loop            : 0.16
% 1.92/1.20  Inferencing          : 0.06
% 1.92/1.20  Reduction            : 0.05
% 1.92/1.20  Demodulation         : 0.04
% 1.92/1.20  BG Simplification    : 0.01
% 1.92/1.20  Subsumption          : 0.03
% 1.92/1.20  Abstraction          : 0.01
% 1.92/1.20  MUC search           : 0.00
% 1.92/1.20  Cooper               : 0.00
% 1.92/1.20  Total                : 0.47
% 1.92/1.20  Index Insertion      : 0.00
% 1.92/1.20  Index Deletion       : 0.00
% 1.92/1.20  Index Matching       : 0.00
% 1.92/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:02:05 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
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
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_18,A_17)),k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [B_36,A_37] :
      ( k7_relat_1(B_36,A_37) = B_36
      | ~ r1_tarski(k1_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_177,plain,(
    ! [B_45,A_46] :
      ( k7_relat_1(k7_relat_1(B_45,A_46),k1_relat_1(B_45)) = k7_relat_1(B_45,A_46)
      | ~ v1_relat_1(k7_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_16,c_101])).

tff(c_14,plain,(
    ! [C_16,A_14,B_15] :
      ( k7_relat_1(k7_relat_1(C_16,A_14),B_15) = k7_relat_1(C_16,k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_833,plain,(
    ! [B_73,A_74] :
      ( k7_relat_1(B_73,k3_xboole_0(A_74,k1_relat_1(B_73))) = k7_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(k7_relat_1(B_73,A_74))
      | ~ v1_relat_1(B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_23,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_871,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_23])).

tff(c_897,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_871])).

tff(c_901,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_897])).

tff(c_905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_901])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.52  
% 3.28/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.52  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.28/1.52  
% 3.28/1.52  %Foreground sorts:
% 3.28/1.52  
% 3.28/1.52  
% 3.28/1.52  %Background operators:
% 3.28/1.52  
% 3.28/1.52  
% 3.28/1.52  %Foreground operators:
% 3.28/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.28/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.28/1.52  
% 3.28/1.53  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 3.28/1.53  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.28/1.53  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 3.28/1.53  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.28/1.53  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 3.28/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.28/1.53  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.53  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.53  tff(c_16, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(k7_relat_1(B_18, A_17)), k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.53  tff(c_101, plain, (![B_36, A_37]: (k7_relat_1(B_36, A_37)=B_36 | ~r1_tarski(k1_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.53  tff(c_177, plain, (![B_45, A_46]: (k7_relat_1(k7_relat_1(B_45, A_46), k1_relat_1(B_45))=k7_relat_1(B_45, A_46) | ~v1_relat_1(k7_relat_1(B_45, A_46)) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_16, c_101])).
% 3.28/1.53  tff(c_14, plain, (![C_16, A_14, B_15]: (k7_relat_1(k7_relat_1(C_16, A_14), B_15)=k7_relat_1(C_16, k3_xboole_0(A_14, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.53  tff(c_833, plain, (![B_73, A_74]: (k7_relat_1(B_73, k3_xboole_0(A_74, k1_relat_1(B_73)))=k7_relat_1(B_73, A_74) | ~v1_relat_1(B_73) | ~v1_relat_1(k7_relat_1(B_73, A_74)) | ~v1_relat_1(B_73))), inference(superposition, [status(thm), theory('equality')], [c_177, c_14])).
% 3.28/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.28/1.53  tff(c_20, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.53  tff(c_23, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 3.28/1.53  tff(c_871, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_833, c_23])).
% 3.28/1.53  tff(c_897, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_871])).
% 3.28/1.53  tff(c_901, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_897])).
% 3.28/1.53  tff(c_905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_901])).
% 3.28/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  Inference rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Ref     : 0
% 3.28/1.53  #Sup     : 231
% 3.28/1.53  #Fact    : 0
% 3.28/1.53  #Define  : 0
% 3.28/1.53  #Split   : 0
% 3.28/1.53  #Chain   : 0
% 3.28/1.53  #Close   : 0
% 3.28/1.53  
% 3.28/1.53  Ordering : KBO
% 3.28/1.53  
% 3.28/1.53  Simplification rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Subsume      : 24
% 3.28/1.53  #Demod        : 85
% 3.28/1.53  #Tautology    : 94
% 3.28/1.53  #SimpNegUnit  : 0
% 3.28/1.53  #BackRed      : 0
% 3.28/1.53  
% 3.28/1.53  #Partial instantiations: 0
% 3.28/1.53  #Strategies tried      : 1
% 3.28/1.53  
% 3.28/1.53  Timing (in seconds)
% 3.28/1.53  ----------------------
% 3.28/1.54  Preprocessing        : 0.30
% 3.28/1.54  Parsing              : 0.16
% 3.28/1.54  CNF conversion       : 0.02
% 3.28/1.54  Main loop            : 0.47
% 3.28/1.54  Inferencing          : 0.16
% 3.28/1.54  Reduction            : 0.20
% 3.28/1.54  Demodulation         : 0.17
% 3.28/1.54  BG Simplification    : 0.03
% 3.28/1.54  Subsumption          : 0.06
% 3.28/1.54  Abstraction          : 0.03
% 3.28/1.54  MUC search           : 0.00
% 3.28/1.54  Cooper               : 0.00
% 3.28/1.54  Total                : 0.79
% 3.28/1.54  Index Insertion      : 0.00
% 3.28/1.54  Index Deletion       : 0.00
% 3.28/1.54  Index Matching       : 0.00
% 3.28/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

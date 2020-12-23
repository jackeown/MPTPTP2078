%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:49 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  56 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_55,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(B_25,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [B_25,A_24] : k3_xboole_0(B_25,A_24) = k3_xboole_0(A_24,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_8])).

tff(c_146,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_31,A_32)),A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k3_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_200,plain,(
    ! [B_41,B_42,C_43] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_41,k3_xboole_0(B_42,C_43))),B_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_240,plain,(
    ! [B_44,B_45,A_46] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_44,k3_xboole_0(B_45,A_46))),A_46)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_200])).

tff(c_280,plain,(
    ! [B_47] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_47,'#skF_1')),'#skF_2')
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_240])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_372,plain,(
    ! [B_57] :
      ( k7_relat_1(k7_relat_1(B_57,'#skF_1'),'#skF_2') = k7_relat_1(B_57,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_57,'#skF_1'))
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_280,c_14])).

tff(c_382,plain,(
    ! [A_58] :
      ( k7_relat_1(k7_relat_1(A_58,'#skF_1'),'#skF_2') = k7_relat_1(A_58,'#skF_1')
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_10,c_372])).

tff(c_16,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_400,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_16])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.28  
% 2.09/1.28  %Foreground sorts:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Background operators:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Foreground operators:
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.09/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.28  
% 2.09/1.29  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 2.09/1.29  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.09/1.29  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.09/1.29  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.09/1.29  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.09/1.29  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.09/1.29  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.09/1.29  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.09/1.29  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.29  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.29  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.29  tff(c_55, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.29  tff(c_59, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_18, c_55])).
% 2.09/1.29  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.29  tff(c_60, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.29  tff(c_79, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(B_25, A_24))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 2.09/1.29  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.29  tff(c_85, plain, (![B_25, A_24]: (k3_xboole_0(B_25, A_24)=k3_xboole_0(A_24, B_25))), inference(superposition, [status(thm), theory('equality')], [c_79, c_8])).
% 2.09/1.29  tff(c_146, plain, (![B_31, A_32]: (r1_tarski(k1_relat_1(k7_relat_1(B_31, A_32)), A_32) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.29  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.29  tff(c_200, plain, (![B_41, B_42, C_43]: (r1_tarski(k1_relat_1(k7_relat_1(B_41, k3_xboole_0(B_42, C_43))), B_42) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_146, c_2])).
% 2.09/1.29  tff(c_240, plain, (![B_44, B_45, A_46]: (r1_tarski(k1_relat_1(k7_relat_1(B_44, k3_xboole_0(B_45, A_46))), A_46) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_85, c_200])).
% 2.09/1.29  tff(c_280, plain, (![B_47]: (r1_tarski(k1_relat_1(k7_relat_1(B_47, '#skF_1')), '#skF_2') | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_59, c_240])).
% 2.09/1.29  tff(c_14, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.29  tff(c_372, plain, (![B_57]: (k7_relat_1(k7_relat_1(B_57, '#skF_1'), '#skF_2')=k7_relat_1(B_57, '#skF_1') | ~v1_relat_1(k7_relat_1(B_57, '#skF_1')) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_280, c_14])).
% 2.09/1.29  tff(c_382, plain, (![A_58]: (k7_relat_1(k7_relat_1(A_58, '#skF_1'), '#skF_2')=k7_relat_1(A_58, '#skF_1') | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_10, c_372])).
% 2.09/1.29  tff(c_16, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.29  tff(c_400, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_382, c_16])).
% 2.09/1.29  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_400])).
% 2.09/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  Inference rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Ref     : 0
% 2.09/1.29  #Sup     : 95
% 2.09/1.29  #Fact    : 0
% 2.09/1.29  #Define  : 0
% 2.09/1.29  #Split   : 0
% 2.09/1.29  #Chain   : 0
% 2.09/1.29  #Close   : 0
% 2.09/1.29  
% 2.09/1.29  Ordering : KBO
% 2.09/1.29  
% 2.09/1.29  Simplification rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Subsume      : 19
% 2.09/1.29  #Demod        : 11
% 2.09/1.29  #Tautology    : 35
% 2.09/1.29  #SimpNegUnit  : 0
% 2.09/1.29  #BackRed      : 0
% 2.09/1.29  
% 2.09/1.29  #Partial instantiations: 0
% 2.09/1.29  #Strategies tried      : 1
% 2.09/1.29  
% 2.09/1.29  Timing (in seconds)
% 2.09/1.29  ----------------------
% 2.09/1.29  Preprocessing        : 0.28
% 2.09/1.29  Parsing              : 0.15
% 2.09/1.29  CNF conversion       : 0.02
% 2.09/1.29  Main loop            : 0.26
% 2.09/1.29  Inferencing          : 0.11
% 2.09/1.29  Reduction            : 0.08
% 2.09/1.29  Demodulation         : 0.06
% 2.09/1.29  BG Simplification    : 0.01
% 2.09/1.29  Subsumption          : 0.05
% 2.09/1.29  Abstraction          : 0.01
% 2.09/1.29  MUC search           : 0.00
% 2.09/1.29  Cooper               : 0.00
% 2.09/1.29  Total                : 0.56
% 2.09/1.29  Index Insertion      : 0.00
% 2.09/1.29  Index Deletion       : 0.00
% 2.09/1.29  Index Matching       : 0.00
% 2.09/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

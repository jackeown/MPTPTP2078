%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:13 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  47 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [B_22,A_23] :
      ( k3_xboole_0(k2_relat_1(B_22),A_23) = k2_relat_1(k8_relat_1(A_23,B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [B_26,B_27] :
      ( k3_xboole_0(B_26,k2_relat_1(B_27)) = k2_relat_1(k8_relat_1(B_26,B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [B_28,B_29,B_30] :
      ( r1_tarski(k2_relat_1(k8_relat_1(B_28,B_29)),B_30)
      | ~ r1_tarski(B_28,B_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_4])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k8_relat_1(A_10,B_11) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_229,plain,(
    ! [B_36,B_37,B_38] :
      ( k8_relat_1(B_36,k8_relat_1(B_37,B_38)) = k8_relat_1(B_37,B_38)
      | ~ v1_relat_1(k8_relat_1(B_37,B_38))
      | ~ r1_tarski(B_37,B_36)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_132,c_10])).

tff(c_233,plain,(
    ! [B_39,A_40,B_41] :
      ( k8_relat_1(B_39,k8_relat_1(A_40,B_41)) = k8_relat_1(A_40,B_41)
      | ~ r1_tarski(A_40,B_39)
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_229])).

tff(c_12,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_256,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_12])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.22  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.22  
% 2.07/1.22  %Foreground sorts:
% 2.07/1.22  
% 2.07/1.22  
% 2.07/1.22  %Background operators:
% 2.07/1.22  
% 2.07/1.22  
% 2.07/1.22  %Foreground operators:
% 2.07/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.07/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.22  
% 2.07/1.23  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 2.07/1.23  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.07/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.07/1.23  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 2.07/1.23  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.07/1.23  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.07/1.23  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.23  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.23  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.23  tff(c_65, plain, (![B_22, A_23]: (k3_xboole_0(k2_relat_1(B_22), A_23)=k2_relat_1(k8_relat_1(A_23, B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.23  tff(c_95, plain, (![B_26, B_27]: (k3_xboole_0(B_26, k2_relat_1(B_27))=k2_relat_1(k8_relat_1(B_26, B_27)) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_65])).
% 2.07/1.23  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.23  tff(c_132, plain, (![B_28, B_29, B_30]: (r1_tarski(k2_relat_1(k8_relat_1(B_28, B_29)), B_30) | ~r1_tarski(B_28, B_30) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_95, c_4])).
% 2.07/1.23  tff(c_10, plain, (![A_10, B_11]: (k8_relat_1(A_10, B_11)=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.23  tff(c_229, plain, (![B_36, B_37, B_38]: (k8_relat_1(B_36, k8_relat_1(B_37, B_38))=k8_relat_1(B_37, B_38) | ~v1_relat_1(k8_relat_1(B_37, B_38)) | ~r1_tarski(B_37, B_36) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_132, c_10])).
% 2.07/1.23  tff(c_233, plain, (![B_39, A_40, B_41]: (k8_relat_1(B_39, k8_relat_1(A_40, B_41))=k8_relat_1(A_40, B_41) | ~r1_tarski(A_40, B_39) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_6, c_229])).
% 2.07/1.23  tff(c_12, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.23  tff(c_256, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_233, c_12])).
% 2.07/1.23  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_256])).
% 2.07/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  Inference rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Ref     : 0
% 2.07/1.23  #Sup     : 69
% 2.07/1.23  #Fact    : 0
% 2.07/1.23  #Define  : 0
% 2.07/1.23  #Split   : 0
% 2.07/1.23  #Chain   : 0
% 2.07/1.23  #Close   : 0
% 2.07/1.23  
% 2.07/1.23  Ordering : KBO
% 2.07/1.23  
% 2.07/1.23  Simplification rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Subsume      : 18
% 2.07/1.23  #Demod        : 2
% 2.07/1.23  #Tautology    : 22
% 2.07/1.23  #SimpNegUnit  : 0
% 2.07/1.23  #BackRed      : 0
% 2.07/1.23  
% 2.07/1.23  #Partial instantiations: 0
% 2.07/1.23  #Strategies tried      : 1
% 2.07/1.23  
% 2.07/1.23  Timing (in seconds)
% 2.07/1.23  ----------------------
% 2.07/1.23  Preprocessing        : 0.28
% 2.07/1.23  Parsing              : 0.15
% 2.07/1.23  CNF conversion       : 0.02
% 2.10/1.23  Main loop            : 0.19
% 2.10/1.23  Inferencing          : 0.08
% 2.10/1.23  Reduction            : 0.05
% 2.10/1.23  Demodulation         : 0.04
% 2.10/1.23  BG Simplification    : 0.01
% 2.10/1.23  Subsumption          : 0.03
% 2.10/1.23  Abstraction          : 0.02
% 2.10/1.23  MUC search           : 0.00
% 2.10/1.23  Cooper               : 0.00
% 2.10/1.23  Total                : 0.49
% 2.10/1.23  Index Insertion      : 0.00
% 2.10/1.23  Index Deletion       : 0.00
% 2.10/1.23  Index Matching       : 0.00
% 2.10/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

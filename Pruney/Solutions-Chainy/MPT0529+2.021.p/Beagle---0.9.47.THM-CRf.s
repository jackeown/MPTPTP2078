%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:14 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  44 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(A_14,C_15)
      | ~ r1_tarski(B_16,C_15)
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,'#skF_2')
      | ~ r1_tarski(A_14,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_17])).

tff(c_39,plain,(
    ! [A_20,B_21] :
      ( k8_relat_1(A_20,B_21) = B_21
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,(
    ! [B_22] :
      ( k8_relat_1('#skF_2',B_22) = B_22
      | ~ v1_relat_1(B_22)
      | ~ r1_tarski(k2_relat_1(B_22),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_23,c_39])).

tff(c_133,plain,(
    ! [B_35] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_35)) = k8_relat_1('#skF_1',B_35)
      | ~ v1_relat_1(k8_relat_1('#skF_1',B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_143,plain,(
    ! [B_36] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_36)) = k8_relat_1('#skF_1',B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_10,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_161,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_10])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.51  
% 2.31/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.51  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.31/1.51  
% 2.31/1.51  %Foreground sorts:
% 2.31/1.51  
% 2.31/1.51  
% 2.31/1.51  %Background operators:
% 2.31/1.51  
% 2.31/1.51  
% 2.31/1.51  %Foreground operators:
% 2.31/1.51  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.31/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.51  
% 2.37/1.53  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 2.37/1.53  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.37/1.53  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.37/1.53  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.37/1.53  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.37/1.53  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.37/1.53  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k8_relat_1(A_4, B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.53  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.53  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.37/1.53  tff(c_17, plain, (![A_14, C_15, B_16]: (r1_tarski(A_14, C_15) | ~r1_tarski(B_16, C_15) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.53  tff(c_23, plain, (![A_14]: (r1_tarski(A_14, '#skF_2') | ~r1_tarski(A_14, '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_17])).
% 2.37/1.53  tff(c_39, plain, (![A_20, B_21]: (k8_relat_1(A_20, B_21)=B_21 | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.37/1.53  tff(c_49, plain, (![B_22]: (k8_relat_1('#skF_2', B_22)=B_22 | ~v1_relat_1(B_22) | ~r1_tarski(k2_relat_1(B_22), '#skF_1'))), inference(resolution, [status(thm)], [c_23, c_39])).
% 2.37/1.53  tff(c_133, plain, (![B_35]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_35))=k8_relat_1('#skF_1', B_35) | ~v1_relat_1(k8_relat_1('#skF_1', B_35)) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_6, c_49])).
% 2.37/1.53  tff(c_143, plain, (![B_36]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_36))=k8_relat_1('#skF_1', B_36) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.37/1.53  tff(c_10, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.37/1.53  tff(c_161, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_143, c_10])).
% 2.37/1.53  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_161])).
% 2.37/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.53  
% 2.37/1.53  Inference rules
% 2.37/1.53  ----------------------
% 2.37/1.53  #Ref     : 0
% 2.37/1.53  #Sup     : 41
% 2.37/1.53  #Fact    : 0
% 2.37/1.53  #Define  : 0
% 2.37/1.53  #Split   : 0
% 2.37/1.53  #Chain   : 0
% 2.37/1.53  #Close   : 0
% 2.37/1.53  
% 2.37/1.53  Ordering : KBO
% 2.37/1.53  
% 2.37/1.53  Simplification rules
% 2.37/1.53  ----------------------
% 2.37/1.53  #Subsume      : 10
% 2.37/1.53  #Demod        : 2
% 2.37/1.53  #Tautology    : 7
% 2.37/1.53  #SimpNegUnit  : 0
% 2.37/1.53  #BackRed      : 0
% 2.37/1.53  
% 2.37/1.53  #Partial instantiations: 0
% 2.37/1.53  #Strategies tried      : 1
% 2.37/1.53  
% 2.37/1.53  Timing (in seconds)
% 2.37/1.53  ----------------------
% 2.37/1.53  Preprocessing        : 0.41
% 2.37/1.53  Parsing              : 0.23
% 2.37/1.53  CNF conversion       : 0.03
% 2.37/1.53  Main loop            : 0.28
% 2.37/1.53  Inferencing          : 0.12
% 2.37/1.53  Reduction            : 0.06
% 2.37/1.53  Demodulation         : 0.05
% 2.37/1.53  BG Simplification    : 0.02
% 2.37/1.53  Subsumption          : 0.06
% 2.37/1.53  Abstraction          : 0.01
% 2.37/1.54  MUC search           : 0.00
% 2.37/1.54  Cooper               : 0.00
% 2.37/1.54  Total                : 0.73
% 2.37/1.54  Index Insertion      : 0.00
% 2.37/1.54  Index Deletion       : 0.00
% 2.37/1.54  Index Matching       : 0.00
% 2.37/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:50 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
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
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
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
    ! [B_20,A_21] :
      ( k7_relat_1(B_20,A_21) = B_20
      | ~ r1_tarski(k1_relat_1(B_20),A_21)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,(
    ! [B_22] :
      ( k7_relat_1(B_22,'#skF_2') = B_22
      | ~ v1_relat_1(B_22)
      | ~ r1_tarski(k1_relat_1(B_22),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_23,c_39])).

tff(c_133,plain,(
    ! [B_35] :
      ( k7_relat_1(k7_relat_1(B_35,'#skF_1'),'#skF_2') = k7_relat_1(B_35,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_35,'#skF_1'))
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_143,plain,(
    ! [A_36] :
      ( k7_relat_1(k7_relat_1(A_36,'#skF_1'),'#skF_2') = k7_relat_1(A_36,'#skF_1')
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_10,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_161,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_10])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.25  
% 2.00/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.25  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.25  
% 2.00/1.25  %Foreground sorts:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Background operators:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Foreground operators:
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.00/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.25  
% 2.00/1.26  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 2.00/1.26  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.00/1.26  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.00/1.26  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.00/1.26  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.00/1.26  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.26  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.26  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.00/1.26  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.26  tff(c_17, plain, (![A_14, C_15, B_16]: (r1_tarski(A_14, C_15) | ~r1_tarski(B_16, C_15) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.26  tff(c_23, plain, (![A_14]: (r1_tarski(A_14, '#skF_2') | ~r1_tarski(A_14, '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_17])).
% 2.00/1.26  tff(c_39, plain, (![B_20, A_21]: (k7_relat_1(B_20, A_21)=B_20 | ~r1_tarski(k1_relat_1(B_20), A_21) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.26  tff(c_49, plain, (![B_22]: (k7_relat_1(B_22, '#skF_2')=B_22 | ~v1_relat_1(B_22) | ~r1_tarski(k1_relat_1(B_22), '#skF_1'))), inference(resolution, [status(thm)], [c_23, c_39])).
% 2.00/1.26  tff(c_133, plain, (![B_35]: (k7_relat_1(k7_relat_1(B_35, '#skF_1'), '#skF_2')=k7_relat_1(B_35, '#skF_1') | ~v1_relat_1(k7_relat_1(B_35, '#skF_1')) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_6, c_49])).
% 2.00/1.26  tff(c_143, plain, (![A_36]: (k7_relat_1(k7_relat_1(A_36, '#skF_1'), '#skF_2')=k7_relat_1(A_36, '#skF_1') | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.00/1.26  tff(c_10, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.26  tff(c_161, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_143, c_10])).
% 2.00/1.26  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_161])).
% 2.00/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.26  
% 2.00/1.26  Inference rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Ref     : 0
% 2.00/1.26  #Sup     : 41
% 2.00/1.26  #Fact    : 0
% 2.00/1.26  #Define  : 0
% 2.00/1.26  #Split   : 0
% 2.00/1.26  #Chain   : 0
% 2.00/1.26  #Close   : 0
% 2.00/1.26  
% 2.00/1.26  Ordering : KBO
% 2.00/1.26  
% 2.00/1.26  Simplification rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Subsume      : 10
% 2.00/1.26  #Demod        : 2
% 2.00/1.26  #Tautology    : 7
% 2.00/1.26  #SimpNegUnit  : 0
% 2.00/1.26  #BackRed      : 0
% 2.00/1.26  
% 2.00/1.26  #Partial instantiations: 0
% 2.00/1.26  #Strategies tried      : 1
% 2.00/1.26  
% 2.00/1.26  Timing (in seconds)
% 2.00/1.26  ----------------------
% 2.00/1.26  Preprocessing        : 0.27
% 2.00/1.26  Parsing              : 0.15
% 2.00/1.26  CNF conversion       : 0.02
% 2.00/1.26  Main loop            : 0.18
% 2.00/1.26  Inferencing          : 0.08
% 2.00/1.26  Reduction            : 0.04
% 2.00/1.26  Demodulation         : 0.03
% 2.00/1.26  BG Simplification    : 0.01
% 2.00/1.26  Subsumption          : 0.04
% 2.00/1.26  Abstraction          : 0.01
% 2.00/1.27  MUC search           : 0.00
% 2.00/1.27  Cooper               : 0.00
% 2.00/1.27  Total                : 0.48
% 2.00/1.27  Index Insertion      : 0.00
% 2.00/1.27  Index Deletion       : 0.00
% 2.00/1.27  Index Matching       : 0.00
% 2.00/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

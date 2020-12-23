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
% DateTime   : Thu Dec  3 10:00:30 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   24 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  34 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_4,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_7] :
      ( k8_relat_1(k1_xboole_0,A_7) = k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_8,plain,(
    ! [B_3,A_2,C_4] :
      ( k8_relat_1(B_3,k8_relat_1(A_2,C_4)) = k8_relat_1(A_2,C_4)
      | ~ r1_tarski(A_2,B_3)
      | ~ v1_relat_1(C_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_37,plain,(
    ! [B_3] :
      ( k8_relat_1(k1_xboole_0,'#skF_1') = k8_relat_1(B_3,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_3)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8])).

tff(c_41,plain,(
    ! [B_3] : k8_relat_1(B_3,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_18,c_37])).

tff(c_12,plain,(
    k8_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:41:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.02  
% 1.50/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.02  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.50/1.02  
% 1.50/1.02  %Foreground sorts:
% 1.50/1.02  
% 1.50/1.02  
% 1.50/1.02  %Background operators:
% 1.50/1.02  
% 1.50/1.02  
% 1.50/1.02  %Foreground operators:
% 1.50/1.02  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.50/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.50/1.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.50/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.50/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.50/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.50/1.02  
% 1.50/1.03  tff(f_32, axiom, (?[A]: (~v1_xboole_0(A) & v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relat_1)).
% 1.50/1.03  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.50/1.03  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.50/1.03  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.50/1.03  tff(f_45, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.50/1.03  tff(c_4, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.50/1.03  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.50/1.03  tff(c_14, plain, (![A_7]: (k8_relat_1(k1_xboole_0, A_7)=k1_xboole_0 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.50/1.03  tff(c_18, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_14])).
% 1.50/1.03  tff(c_8, plain, (![B_3, A_2, C_4]: (k8_relat_1(B_3, k8_relat_1(A_2, C_4))=k8_relat_1(A_2, C_4) | ~r1_tarski(A_2, B_3) | ~v1_relat_1(C_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.50/1.03  tff(c_37, plain, (![B_3]: (k8_relat_1(k1_xboole_0, '#skF_1')=k8_relat_1(B_3, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_3) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_8])).
% 1.50/1.03  tff(c_41, plain, (![B_3]: (k8_relat_1(B_3, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_18, c_37])).
% 1.50/1.03  tff(c_12, plain, (k8_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.50/1.03  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_12])).
% 1.50/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.03  
% 1.50/1.03  Inference rules
% 1.50/1.03  ----------------------
% 1.50/1.03  #Ref     : 0
% 1.50/1.03  #Sup     : 8
% 1.50/1.03  #Fact    : 0
% 1.50/1.03  #Define  : 0
% 1.50/1.03  #Split   : 0
% 1.50/1.03  #Chain   : 0
% 1.50/1.03  #Close   : 0
% 1.50/1.03  
% 1.50/1.03  Ordering : KBO
% 1.50/1.03  
% 1.50/1.03  Simplification rules
% 1.50/1.03  ----------------------
% 1.50/1.03  #Subsume      : 0
% 1.50/1.03  #Demod        : 4
% 1.50/1.03  #Tautology    : 4
% 1.50/1.03  #SimpNegUnit  : 0
% 1.50/1.03  #BackRed      : 1
% 1.50/1.03  
% 1.50/1.03  #Partial instantiations: 0
% 1.50/1.03  #Strategies tried      : 1
% 1.50/1.03  
% 1.50/1.03  Timing (in seconds)
% 1.50/1.03  ----------------------
% 1.50/1.03  Preprocessing        : 0.26
% 1.50/1.04  Parsing              : 0.15
% 1.50/1.04  CNF conversion       : 0.01
% 1.50/1.04  Main loop            : 0.08
% 1.50/1.04  Inferencing          : 0.04
% 1.50/1.04  Reduction            : 0.02
% 1.50/1.04  Demodulation         : 0.02
% 1.50/1.04  BG Simplification    : 0.01
% 1.50/1.04  Subsumption          : 0.01
% 1.50/1.04  Abstraction          : 0.00
% 1.50/1.04  MUC search           : 0.00
% 1.50/1.04  Cooper               : 0.00
% 1.50/1.04  Total                : 0.36
% 1.50/1.04  Index Insertion      : 0.00
% 1.50/1.04  Index Deletion       : 0.00
% 1.50/1.04  Index Matching       : 0.00
% 1.50/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------

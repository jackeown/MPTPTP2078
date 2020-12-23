%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:25 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   31 (  47 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  56 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [A_8] :
      ( v1_relat_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31,plain,(
    ! [A_9] :
      ( k8_relat_1(k2_relat_1(A_9),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_31])).

tff(c_44,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40])).

tff(c_49,plain,(
    ! [B_10,A_11,C_12] :
      ( k8_relat_1(B_10,k8_relat_1(A_11,C_12)) = k8_relat_1(A_11,C_12)
      | ~ r1_tarski(A_11,B_10)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [B_10] :
      ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(B_10,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_10)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_49])).

tff(c_80,plain,(
    ! [B_10] : k8_relat_1(B_10,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4,c_44,c_68])).

tff(c_16,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.22  
% 1.77/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.22  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.83/1.22  
% 1.83/1.22  %Foreground sorts:
% 1.83/1.22  
% 1.83/1.22  
% 1.83/1.22  %Background operators:
% 1.83/1.22  
% 1.83/1.22  
% 1.83/1.22  %Foreground operators:
% 1.83/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.83/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.22  
% 1.85/1.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.85/1.23  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.85/1.23  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.85/1.23  tff(f_45, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.85/1.23  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 1.85/1.23  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 1.85/1.23  tff(f_48, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.85/1.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.85/1.23  tff(c_26, plain, (![A_8]: (v1_relat_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.23  tff(c_30, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.85/1.23  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.85/1.23  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.23  tff(c_31, plain, (![A_9]: (k8_relat_1(k2_relat_1(A_9), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.85/1.23  tff(c_40, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_31])).
% 1.85/1.23  tff(c_44, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40])).
% 1.85/1.23  tff(c_49, plain, (![B_10, A_11, C_12]: (k8_relat_1(B_10, k8_relat_1(A_11, C_12))=k8_relat_1(A_11, C_12) | ~r1_tarski(A_11, B_10) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.85/1.23  tff(c_68, plain, (![B_10]: (k8_relat_1(k1_xboole_0, k1_xboole_0)=k8_relat_1(B_10, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_10) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_49])).
% 1.85/1.23  tff(c_80, plain, (![B_10]: (k8_relat_1(B_10, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4, c_44, c_68])).
% 1.85/1.23  tff(c_16, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.85/1.23  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_16])).
% 1.85/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.23  
% 1.85/1.23  Inference rules
% 1.85/1.23  ----------------------
% 1.85/1.23  #Ref     : 0
% 1.85/1.23  #Sup     : 18
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
% 1.85/1.23  #Demod        : 6
% 1.85/1.23  #Tautology    : 13
% 1.85/1.23  #SimpNegUnit  : 0
% 1.85/1.23  #BackRed      : 1
% 1.85/1.23  
% 1.85/1.23  #Partial instantiations: 0
% 1.85/1.23  #Strategies tried      : 1
% 1.85/1.23  
% 1.85/1.23  Timing (in seconds)
% 1.85/1.23  ----------------------
% 1.85/1.23  Preprocessing        : 0.28
% 1.85/1.23  Parsing              : 0.16
% 1.85/1.23  CNF conversion       : 0.02
% 1.85/1.23  Main loop            : 0.11
% 1.85/1.23  Inferencing          : 0.05
% 1.85/1.23  Reduction            : 0.03
% 1.85/1.23  Demodulation         : 0.02
% 1.85/1.23  BG Simplification    : 0.01
% 1.85/1.23  Subsumption          : 0.01
% 1.85/1.23  Abstraction          : 0.01
% 1.85/1.23  MUC search           : 0.00
% 1.85/1.23  Cooper               : 0.00
% 1.85/1.23  Total                : 0.41
% 1.85/1.23  Index Insertion      : 0.00
% 1.85/1.23  Index Deletion       : 0.00
% 1.85/1.23  Index Matching       : 0.00
% 1.85/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

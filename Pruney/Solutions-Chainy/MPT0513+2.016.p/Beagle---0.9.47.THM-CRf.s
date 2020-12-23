%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:00 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
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
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_41,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

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
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_31,plain,(
    ! [A_9] :
      ( k7_relat_1(A_9,k1_relat_1(A_9)) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_31])).

tff(c_44,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40])).

tff(c_49,plain,(
    ! [C_10,A_11,B_12] :
      ( k7_relat_1(k7_relat_1(C_10,A_11),B_12) = k7_relat_1(C_10,A_11)
      | ~ r1_tarski(A_11,B_12)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [B_12] :
      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k1_xboole_0,B_12)
      | ~ r1_tarski(k1_xboole_0,B_12)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_49])).

tff(c_80,plain,(
    ! [B_12] : k7_relat_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4,c_44,c_68])).

tff(c_16,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.12  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.65/1.12  
% 1.65/1.12  %Foreground sorts:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Background operators:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Foreground operators:
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.65/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.65/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.12  
% 1.65/1.13  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.65/1.13  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.65/1.13  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.65/1.13  tff(f_41, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.65/1.13  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.65/1.13  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.65/1.13  tff(f_48, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.65/1.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.65/1.13  tff(c_26, plain, (![A_8]: (v1_relat_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.13  tff(c_30, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.65/1.13  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.65/1.13  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.13  tff(c_31, plain, (![A_9]: (k7_relat_1(A_9, k1_relat_1(A_9))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.13  tff(c_40, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_31])).
% 1.65/1.13  tff(c_44, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40])).
% 1.65/1.13  tff(c_49, plain, (![C_10, A_11, B_12]: (k7_relat_1(k7_relat_1(C_10, A_11), B_12)=k7_relat_1(C_10, A_11) | ~r1_tarski(A_11, B_12) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.13  tff(c_68, plain, (![B_12]: (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1(k1_xboole_0, B_12) | ~r1_tarski(k1_xboole_0, B_12) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_49])).
% 1.65/1.13  tff(c_80, plain, (![B_12]: (k7_relat_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4, c_44, c_68])).
% 1.65/1.13  tff(c_16, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.65/1.13  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_16])).
% 1.65/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  Inference rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Ref     : 0
% 1.65/1.13  #Sup     : 18
% 1.65/1.13  #Fact    : 0
% 1.65/1.13  #Define  : 0
% 1.65/1.13  #Split   : 0
% 1.65/1.13  #Chain   : 0
% 1.65/1.13  #Close   : 0
% 1.65/1.13  
% 1.65/1.13  Ordering : KBO
% 1.65/1.13  
% 1.65/1.13  Simplification rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Subsume      : 0
% 1.65/1.13  #Demod        : 6
% 1.65/1.13  #Tautology    : 13
% 1.65/1.13  #SimpNegUnit  : 0
% 1.65/1.13  #BackRed      : 1
% 1.65/1.13  
% 1.65/1.13  #Partial instantiations: 0
% 1.65/1.13  #Strategies tried      : 1
% 1.65/1.13  
% 1.65/1.13  Timing (in seconds)
% 1.65/1.13  ----------------------
% 1.65/1.14  Preprocessing        : 0.25
% 1.65/1.14  Parsing              : 0.14
% 1.65/1.14  CNF conversion       : 0.01
% 1.65/1.14  Main loop            : 0.10
% 1.65/1.14  Inferencing          : 0.05
% 1.65/1.14  Reduction            : 0.03
% 1.65/1.14  Demodulation         : 0.02
% 1.65/1.14  BG Simplification    : 0.01
% 1.65/1.14  Subsumption          : 0.01
% 1.65/1.14  Abstraction          : 0.01
% 1.65/1.14  MUC search           : 0.00
% 1.65/1.14  Cooper               : 0.00
% 1.65/1.14  Total                : 0.38
% 1.65/1.14  Index Insertion      : 0.00
% 1.65/1.14  Index Deletion       : 0.00
% 1.65/1.14  Index Matching       : 0.00
% 1.65/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

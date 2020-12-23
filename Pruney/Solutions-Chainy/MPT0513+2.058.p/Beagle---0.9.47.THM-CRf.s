%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:06 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_37,axiom,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_19,plain,(
    ! [A_5] :
      ( v1_relat_1(k4_relat_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_19])).

tff(c_24,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_32,plain,(
    ! [B_8,A_9] :
      ( r1_tarski(k7_relat_1(B_8,A_9),B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_36,plain,(
    ! [A_9] :
      ( k7_relat_1(k1_xboole_0,A_9) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_4])).

tff(c_39,plain,(
    ! [A_9] : k7_relat_1(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36])).

tff(c_14,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.05  
% 1.53/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.06  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_1
% 1.53/1.06  
% 1.53/1.06  %Foreground sorts:
% 1.53/1.06  
% 1.53/1.06  
% 1.53/1.06  %Background operators:
% 1.53/1.06  
% 1.53/1.06  
% 1.53/1.06  %Foreground operators:
% 1.53/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.53/1.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.53/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.53/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.53/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.53/1.06  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.53/1.06  
% 1.53/1.07  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.53/1.07  tff(f_37, axiom, (k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 1.53/1.07  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 1.53/1.07  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.53/1.07  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.53/1.07  tff(f_44, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.53/1.07  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.53/1.07  tff(c_10, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.53/1.07  tff(c_19, plain, (![A_5]: (v1_relat_1(k4_relat_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.53/1.07  tff(c_22, plain, (v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_19])).
% 1.53/1.07  tff(c_24, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 1.53/1.07  tff(c_32, plain, (![B_8, A_9]: (r1_tarski(k7_relat_1(B_8, A_9), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.53/1.07  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.53/1.07  tff(c_36, plain, (![A_9]: (k7_relat_1(k1_xboole_0, A_9)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_4])).
% 1.53/1.07  tff(c_39, plain, (![A_9]: (k7_relat_1(k1_xboole_0, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36])).
% 1.53/1.07  tff(c_14, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.53/1.07  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_14])).
% 1.53/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.07  
% 1.53/1.07  Inference rules
% 1.53/1.07  ----------------------
% 1.53/1.07  #Ref     : 0
% 1.53/1.07  #Sup     : 5
% 1.53/1.07  #Fact    : 0
% 1.53/1.07  #Define  : 0
% 1.53/1.07  #Split   : 0
% 1.53/1.07  #Chain   : 0
% 1.53/1.07  #Close   : 0
% 1.53/1.07  
% 1.53/1.07  Ordering : KBO
% 1.53/1.07  
% 1.53/1.07  Simplification rules
% 1.53/1.07  ----------------------
% 1.53/1.07  #Subsume      : 0
% 1.53/1.07  #Demod        : 5
% 1.53/1.07  #Tautology    : 3
% 1.53/1.07  #SimpNegUnit  : 0
% 1.53/1.07  #BackRed      : 1
% 1.53/1.07  
% 1.53/1.07  #Partial instantiations: 0
% 1.53/1.07  #Strategies tried      : 1
% 1.53/1.07  
% 1.53/1.07  Timing (in seconds)
% 1.53/1.07  ----------------------
% 1.53/1.07  Preprocessing        : 0.24
% 1.53/1.07  Parsing              : 0.14
% 1.53/1.07  CNF conversion       : 0.01
% 1.53/1.07  Main loop            : 0.07
% 1.53/1.07  Inferencing          : 0.03
% 1.53/1.07  Reduction            : 0.02
% 1.53/1.08  Demodulation         : 0.01
% 1.53/1.08  BG Simplification    : 0.01
% 1.53/1.08  Subsumption          : 0.01
% 1.53/1.08  Abstraction          : 0.00
% 1.53/1.08  MUC search           : 0.00
% 1.53/1.08  Cooper               : 0.00
% 1.53/1.08  Total                : 0.33
% 1.53/1.08  Index Insertion      : 0.00
% 1.53/1.08  Index Deletion       : 0.00
% 1.53/1.08  Index Matching       : 0.00
% 1.53/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------

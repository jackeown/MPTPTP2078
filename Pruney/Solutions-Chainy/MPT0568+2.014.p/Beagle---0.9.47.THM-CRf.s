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
% DateTime   : Thu Dec  3 10:01:22 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_36,axiom,(
    ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [A_9] :
      ( v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [B_15,A_16] :
      ( r1_tarski(k10_relat_1(B_15,A_16),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,(
    ! [A_16] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_16),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_54])).

tff(c_60,plain,(
    ! [A_17] : r1_tarski(k10_relat_1(k1_xboole_0,A_17),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_57])).

tff(c_37,plain,(
    ! [A_12,B_13] :
      ( r2_xboole_0(A_12,B_13)
      | B_13 = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_50,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_37,c_10])).

tff(c_64,plain,(
    ! [A_17] : k10_relat_1(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_50])).

tff(c_20,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  
% 1.62/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.13  %$ r2_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.62/1.13  
% 1.62/1.13  %Foreground sorts:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Background operators:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Foreground operators:
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.13  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.62/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.13  
% 1.73/1.14  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.73/1.14  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.73/1.14  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.73/1.14  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.73/1.14  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.73/1.14  tff(f_36, axiom, (![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_xboole_1)).
% 1.73/1.14  tff(f_50, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.73/1.14  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.14  tff(c_31, plain, (![A_9]: (v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.73/1.14  tff(c_35, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.73/1.14  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.73/1.14  tff(c_54, plain, (![B_15, A_16]: (r1_tarski(k10_relat_1(B_15, A_16), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.73/1.14  tff(c_57, plain, (![A_16]: (r1_tarski(k10_relat_1(k1_xboole_0, A_16), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_54])).
% 1.73/1.14  tff(c_60, plain, (![A_17]: (r1_tarski(k10_relat_1(k1_xboole_0, A_17), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_57])).
% 1.73/1.14  tff(c_37, plain, (![A_12, B_13]: (r2_xboole_0(A_12, B_13) | B_13=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.73/1.14  tff(c_10, plain, (![A_3]: (~r2_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.73/1.14  tff(c_50, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_37, c_10])).
% 1.73/1.14  tff(c_64, plain, (![A_17]: (k10_relat_1(k1_xboole_0, A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_50])).
% 1.73/1.14  tff(c_20, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.14  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_20])).
% 1.73/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.14  
% 1.73/1.14  Inference rules
% 1.73/1.14  ----------------------
% 1.73/1.14  #Ref     : 0
% 1.73/1.14  #Sup     : 10
% 1.73/1.14  #Fact    : 0
% 1.73/1.14  #Define  : 0
% 1.73/1.14  #Split   : 0
% 1.73/1.14  #Chain   : 0
% 1.73/1.14  #Close   : 0
% 1.73/1.14  
% 1.73/1.14  Ordering : KBO
% 1.73/1.14  
% 1.73/1.14  Simplification rules
% 1.73/1.14  ----------------------
% 1.73/1.14  #Subsume      : 0
% 1.73/1.14  #Demod        : 3
% 1.73/1.14  #Tautology    : 6
% 1.73/1.14  #SimpNegUnit  : 0
% 1.73/1.14  #BackRed      : 2
% 1.73/1.14  
% 1.73/1.14  #Partial instantiations: 0
% 1.73/1.14  #Strategies tried      : 1
% 1.73/1.14  
% 1.73/1.14  Timing (in seconds)
% 1.73/1.14  ----------------------
% 1.73/1.14  Preprocessing        : 0.27
% 1.73/1.14  Parsing              : 0.16
% 1.73/1.14  CNF conversion       : 0.02
% 1.73/1.14  Main loop            : 0.10
% 1.73/1.14  Inferencing          : 0.05
% 1.73/1.14  Reduction            : 0.03
% 1.73/1.14  Demodulation         : 0.02
% 1.73/1.14  BG Simplification    : 0.01
% 1.73/1.14  Subsumption          : 0.01
% 1.73/1.14  Abstraction          : 0.00
% 1.73/1.14  MUC search           : 0.00
% 1.73/1.14  Cooper               : 0.00
% 1.73/1.14  Total                : 0.39
% 1.73/1.14  Index Insertion      : 0.00
% 1.73/1.14  Index Deletion       : 0.00
% 1.73/1.14  Index Matching       : 0.00
% 1.73/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

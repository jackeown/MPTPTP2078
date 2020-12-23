%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:21 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_45,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    ! [A_9] :
      ( v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,(
    ! [B_10,A_11] :
      ( r1_tarski(k10_relat_1(B_10,A_11),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    ! [A_11] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_11),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_37])).

tff(c_56,plain,(
    ! [A_14] : r1_tarski(k10_relat_1(k1_xboole_0,A_14),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_14] :
      ( k10_relat_1(k1_xboole_0,A_14) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,A_14)) ) ),
    inference(resolution,[status(thm)],[c_56,c_4])).

tff(c_61,plain,(
    ! [A_14] : k10_relat_1(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_20,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.10  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.67/1.10  
% 1.67/1.10  %Foreground sorts:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Background operators:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Foreground operators:
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.10  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.67/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.10  
% 1.67/1.11  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.67/1.11  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.67/1.11  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.67/1.11  tff(f_45, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.67/1.11  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.67/1.11  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.67/1.11  tff(f_48, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.67/1.11  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.67/1.11  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.67/1.11  tff(c_32, plain, (![A_9]: (v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.11  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_32])).
% 1.67/1.11  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.67/1.11  tff(c_37, plain, (![B_10, A_11]: (r1_tarski(k10_relat_1(B_10, A_11), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.67/1.11  tff(c_40, plain, (![A_11]: (r1_tarski(k10_relat_1(k1_xboole_0, A_11), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_37])).
% 1.67/1.11  tff(c_56, plain, (![A_14]: (r1_tarski(k10_relat_1(k1_xboole_0, A_14), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40])).
% 1.67/1.11  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.67/1.11  tff(c_58, plain, (![A_14]: (k10_relat_1(k1_xboole_0, A_14)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k10_relat_1(k1_xboole_0, A_14)))), inference(resolution, [status(thm)], [c_56, c_4])).
% 1.67/1.11  tff(c_61, plain, (![A_14]: (k10_relat_1(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_58])).
% 1.67/1.11  tff(c_20, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.11  tff(c_66, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_20])).
% 1.67/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  Inference rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Ref     : 0
% 1.67/1.11  #Sup     : 10
% 1.67/1.11  #Fact    : 0
% 1.67/1.11  #Define  : 0
% 1.67/1.11  #Split   : 0
% 1.67/1.11  #Chain   : 0
% 1.67/1.11  #Close   : 0
% 1.67/1.11  
% 1.67/1.11  Ordering : KBO
% 1.67/1.11  
% 1.67/1.11  Simplification rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Subsume      : 0
% 1.67/1.11  #Demod        : 7
% 1.67/1.11  #Tautology    : 7
% 1.67/1.11  #SimpNegUnit  : 0
% 1.67/1.11  #BackRed      : 2
% 1.67/1.11  
% 1.67/1.11  #Partial instantiations: 0
% 1.67/1.11  #Strategies tried      : 1
% 1.67/1.11  
% 1.67/1.11  Timing (in seconds)
% 1.67/1.11  ----------------------
% 1.67/1.12  Preprocessing        : 0.26
% 1.67/1.12  Parsing              : 0.15
% 1.67/1.12  CNF conversion       : 0.01
% 1.67/1.12  Main loop            : 0.09
% 1.67/1.12  Inferencing          : 0.04
% 1.67/1.12  Reduction            : 0.03
% 1.67/1.12  Demodulation         : 0.02
% 1.67/1.12  BG Simplification    : 0.01
% 1.67/1.12  Subsumption          : 0.01
% 1.67/1.12  Abstraction          : 0.00
% 1.67/1.12  MUC search           : 0.00
% 1.67/1.12  Cooper               : 0.00
% 1.67/1.12  Total                : 0.37
% 1.67/1.12  Index Insertion      : 0.00
% 1.67/1.12  Index Deletion       : 0.00
% 1.67/1.12  Index Matching       : 0.00
% 1.67/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

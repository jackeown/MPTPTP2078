%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:22 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_41,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_14,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    ! [A_6] :
      ( k2_xboole_0(k1_relat_1(A_6),k2_relat_1(A_6)) = k3_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,
    ( k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_37])).

tff(c_53,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4,c_10,c_46])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:49:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.06  
% 1.49/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.06  %$ v1_xboole_0 > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0
% 1.49/1.06  
% 1.49/1.06  %Foreground sorts:
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  %Background operators:
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  %Foreground operators:
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.49/1.06  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.49/1.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.49/1.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.49/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.49/1.06  
% 1.49/1.07  tff(f_41, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 1.49/1.07  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.49/1.07  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.49/1.07  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.49/1.07  tff(f_39, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.49/1.07  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.49/1.07  tff(c_14, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.49/1.07  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.49/1.07  tff(c_32, plain, (![A_5]: (v1_relat_1(A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.49/1.07  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_32])).
% 1.49/1.07  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.49/1.07  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.49/1.07  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.49/1.07  tff(c_37, plain, (![A_6]: (k2_xboole_0(k1_relat_1(A_6), k2_relat_1(A_6))=k3_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.49/1.07  tff(c_46, plain, (k2_xboole_0(k1_xboole_0, k2_relat_1(k1_xboole_0))=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_37])).
% 1.49/1.07  tff(c_53, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4, c_10, c_46])).
% 1.49/1.07  tff(c_55, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_53])).
% 1.49/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.07  
% 1.49/1.07  Inference rules
% 1.49/1.07  ----------------------
% 1.49/1.07  #Ref     : 0
% 1.49/1.07  #Sup     : 11
% 1.49/1.07  #Fact    : 0
% 1.49/1.07  #Define  : 0
% 1.49/1.07  #Split   : 0
% 1.49/1.07  #Chain   : 0
% 1.49/1.07  #Close   : 0
% 1.49/1.07  
% 1.49/1.07  Ordering : KBO
% 1.49/1.07  
% 1.49/1.07  Simplification rules
% 1.49/1.07  ----------------------
% 1.49/1.07  #Subsume      : 0
% 1.49/1.07  #Demod        : 3
% 1.49/1.07  #Tautology    : 8
% 1.49/1.07  #SimpNegUnit  : 1
% 1.49/1.07  #BackRed      : 0
% 1.49/1.07  
% 1.49/1.07  #Partial instantiations: 0
% 1.49/1.07  #Strategies tried      : 1
% 1.49/1.07  
% 1.49/1.07  Timing (in seconds)
% 1.49/1.07  ----------------------
% 1.49/1.07  Preprocessing        : 0.25
% 1.49/1.07  Parsing              : 0.14
% 1.49/1.07  CNF conversion       : 0.01
% 1.49/1.07  Main loop            : 0.08
% 1.49/1.07  Inferencing          : 0.04
% 1.49/1.07  Reduction            : 0.02
% 1.49/1.07  Demodulation         : 0.02
% 1.49/1.07  BG Simplification    : 0.01
% 1.49/1.07  Subsumption          : 0.01
% 1.49/1.07  Abstraction          : 0.00
% 1.49/1.07  MUC search           : 0.00
% 1.49/1.07  Cooper               : 0.00
% 1.49/1.07  Total                : 0.35
% 1.49/1.07  Index Insertion      : 0.00
% 1.49/1.07  Index Deletion       : 0.00
% 1.49/1.07  Index Matching       : 0.00
% 1.49/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------

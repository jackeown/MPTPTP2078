%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:22 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   44 (  45 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_54,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_28,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_41,plain,(
    ! [A_21] :
      ( v1_relat_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_41])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_80,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,(
    ! [A_28] : k3_tarski(k1_tarski(A_28)) = k2_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_80])).

tff(c_16,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_22] : k3_tarski(k1_zfmisc_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    k3_tarski(k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_101,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_55])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_129,plain,(
    ! [A_32] :
      ( k2_xboole_0(k1_relat_1(A_32),k2_relat_1(A_32)) = k3_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_129])).

tff(c_145,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_101,c_26,c_138])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.13  
% 1.73/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.13  %$ v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0
% 1.73/1.13  
% 1.73/1.13  %Foreground sorts:
% 1.73/1.13  
% 1.73/1.13  
% 1.73/1.13  %Background operators:
% 1.73/1.13  
% 1.73/1.13  
% 1.73/1.13  %Foreground operators:
% 1.73/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.73/1.13  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.73/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.73/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.73/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.73/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.13  
% 1.73/1.14  tff(f_54, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 1.73/1.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.73/1.14  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.73/1.14  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.73/1.14  tff(f_38, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.73/1.14  tff(f_39, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 1.73/1.14  tff(f_41, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.73/1.14  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.73/1.14  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.73/1.14  tff(c_28, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.73/1.14  tff(c_41, plain, (![A_21]: (v1_relat_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.73/1.14  tff(c_45, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_41])).
% 1.73/1.14  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.73/1.14  tff(c_80, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.14  tff(c_92, plain, (![A_28]: (k3_tarski(k1_tarski(A_28))=k2_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_4, c_80])).
% 1.73/1.14  tff(c_16, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.73/1.14  tff(c_46, plain, (![A_22]: (k3_tarski(k1_zfmisc_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.73/1.14  tff(c_55, plain, (k3_tarski(k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16, c_46])).
% 1.73/1.14  tff(c_101, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92, c_55])).
% 1.73/1.14  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.73/1.14  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.73/1.14  tff(c_129, plain, (![A_32]: (k2_xboole_0(k1_relat_1(A_32), k2_relat_1(A_32))=k3_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.73/1.14  tff(c_138, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_129])).
% 1.73/1.14  tff(c_145, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_45, c_101, c_26, c_138])).
% 1.73/1.14  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_145])).
% 1.73/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.14  
% 1.73/1.14  Inference rules
% 1.73/1.14  ----------------------
% 1.73/1.14  #Ref     : 0
% 1.73/1.14  #Sup     : 33
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
% 1.73/1.14  #Demod        : 4
% 1.73/1.14  #Tautology    : 27
% 1.73/1.14  #SimpNegUnit  : 1
% 1.73/1.14  #BackRed      : 0
% 1.73/1.14  
% 1.73/1.14  #Partial instantiations: 0
% 1.73/1.14  #Strategies tried      : 1
% 1.73/1.14  
% 1.73/1.14  Timing (in seconds)
% 1.73/1.14  ----------------------
% 1.73/1.14  Preprocessing        : 0.29
% 1.73/1.14  Parsing              : 0.16
% 1.73/1.14  CNF conversion       : 0.01
% 1.73/1.14  Main loop            : 0.11
% 1.73/1.14  Inferencing          : 0.04
% 1.73/1.14  Reduction            : 0.04
% 1.73/1.14  Demodulation         : 0.03
% 1.73/1.14  BG Simplification    : 0.01
% 1.73/1.14  Subsumption          : 0.01
% 1.73/1.14  Abstraction          : 0.01
% 1.73/1.14  MUC search           : 0.00
% 1.73/1.14  Cooper               : 0.00
% 1.73/1.14  Total                : 0.42
% 1.73/1.14  Index Insertion      : 0.00
% 1.73/1.14  Index Deletion       : 0.00
% 1.73/1.14  Index Matching       : 0.00
% 1.73/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

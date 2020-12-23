%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:22 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   42 (  70 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  70 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_60,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_6,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_30,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    k3_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_30])).

tff(c_48,plain,(
    ! [A_36] :
      ( v1_relat_1(A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_61,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_28])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_26])).

tff(c_98,plain,(
    ! [A_43] :
      ( k2_xboole_0(k1_relat_1(A_43),k2_relat_1(A_43)) = k3_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,
    ( k2_xboole_0(k1_relat_1('#skF_1'),'#skF_1') = k3_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_98])).

tff(c_114,plain,(
    k3_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2,c_61,c_107])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.93/1.23  
% 1.93/1.23  %Foreground sorts:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Background operators:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Foreground operators:
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.93/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.23  
% 1.99/1.25  tff(f_33, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.99/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.99/1.25  tff(f_60, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 1.99/1.25  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.99/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.99/1.25  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.99/1.25  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.99/1.25  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.25  tff(c_53, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.25  tff(c_57, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_53])).
% 1.99/1.25  tff(c_30, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.25  tff(c_60, plain, (k3_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_30])).
% 1.99/1.25  tff(c_48, plain, (![A_36]: (v1_relat_1(A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.25  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_48])).
% 1.99/1.25  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.25  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.25  tff(c_61, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_28])).
% 1.99/1.25  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.25  tff(c_59, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_26])).
% 1.99/1.25  tff(c_98, plain, (![A_43]: (k2_xboole_0(k1_relat_1(A_43), k2_relat_1(A_43))=k3_relat_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.99/1.25  tff(c_107, plain, (k2_xboole_0(k1_relat_1('#skF_1'), '#skF_1')=k3_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_59, c_98])).
% 1.99/1.25  tff(c_114, plain, (k3_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2, c_61, c_107])).
% 1.99/1.25  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_114])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 23
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 0
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.25  
% 1.99/1.25  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 0
% 1.99/1.25  #Demod        : 10
% 1.99/1.25  #Tautology    : 19
% 1.99/1.25  #SimpNegUnit  : 1
% 1.99/1.25  #BackRed      : 4
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 1.99/1.25  Preprocessing        : 0.28
% 1.99/1.25  Parsing              : 0.15
% 1.99/1.25  CNF conversion       : 0.02
% 1.99/1.25  Main loop            : 0.13
% 1.99/1.25  Inferencing          : 0.05
% 1.99/1.25  Reduction            : 0.05
% 1.99/1.25  Demodulation         : 0.04
% 1.99/1.25  BG Simplification    : 0.01
% 1.99/1.25  Subsumption          : 0.02
% 1.99/1.25  Abstraction          : 0.01
% 1.99/1.25  MUC search           : 0.00
% 1.99/1.25  Cooper               : 0.00
% 1.99/1.25  Total                : 0.45
% 1.99/1.25  Index Insertion      : 0.00
% 1.99/1.25  Index Deletion       : 0.00
% 1.99/1.25  Index Matching       : 0.00
% 1.99/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

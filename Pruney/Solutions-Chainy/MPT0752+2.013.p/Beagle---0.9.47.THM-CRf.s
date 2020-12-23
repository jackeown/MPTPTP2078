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
% DateTime   : Thu Dec  3 10:06:28 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_31,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [A_4] :
      ( v5_ordinal1(A_4)
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,(
    ! [A_5] : v1_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_25,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_23])).

tff(c_28,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_28])).

tff(c_6,plain,(
    ! [B_2] : v5_relat_1(k1_xboole_0,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_16,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_33,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_30,c_18])).

tff(c_36,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_33])).

tff(c_40,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.17  
% 1.61/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.18  %$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.61/1.18  
% 1.61/1.18  %Foreground sorts:
% 1.61/1.18  
% 1.61/1.18  
% 1.61/1.18  %Background operators:
% 1.61/1.18  
% 1.61/1.18  
% 1.61/1.18  %Foreground operators:
% 1.61/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.18  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.61/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.61/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.61/1.18  
% 1.78/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.78/1.19  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.78/1.19  tff(f_31, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.78/1.19  tff(f_35, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.78/1.19  tff(f_30, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 1.78/1.19  tff(f_48, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.78/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.78/1.19  tff(c_14, plain, (![A_4]: (v5_ordinal1(A_4) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.78/1.19  tff(c_8, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.19  tff(c_23, plain, (![A_5]: (v1_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.19  tff(c_25, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_23])).
% 1.78/1.19  tff(c_28, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.19  tff(c_30, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_28])).
% 1.78/1.19  tff(c_6, plain, (![B_2]: (v5_relat_1(k1_xboole_0, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.78/1.19  tff(c_16, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_1') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.78/1.19  tff(c_18, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 1.78/1.19  tff(c_33, plain, (~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25, c_30, c_18])).
% 1.78/1.19  tff(c_36, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_33])).
% 1.78/1.19  tff(c_40, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 1.78/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.19  
% 1.78/1.19  Inference rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Ref     : 0
% 1.78/1.19  #Sup     : 5
% 1.78/1.19  #Fact    : 0
% 1.78/1.19  #Define  : 0
% 1.78/1.19  #Split   : 0
% 1.78/1.19  #Chain   : 0
% 1.78/1.19  #Close   : 0
% 1.78/1.19  
% 1.78/1.19  Ordering : KBO
% 1.78/1.19  
% 1.78/1.19  Simplification rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Subsume      : 0
% 1.78/1.19  #Demod        : 4
% 1.78/1.19  #Tautology    : 2
% 1.78/1.19  #SimpNegUnit  : 0
% 1.78/1.19  #BackRed      : 0
% 1.78/1.19  
% 1.78/1.19  #Partial instantiations: 0
% 1.78/1.19  #Strategies tried      : 1
% 1.78/1.19  
% 1.78/1.19  Timing (in seconds)
% 1.78/1.19  ----------------------
% 1.80/1.19  Preprocessing        : 0.29
% 1.80/1.19  Parsing              : 0.16
% 1.80/1.19  CNF conversion       : 0.02
% 1.80/1.19  Main loop            : 0.10
% 1.80/1.19  Inferencing          : 0.05
% 1.80/1.19  Reduction            : 0.03
% 1.80/1.19  Demodulation         : 0.02
% 1.80/1.19  BG Simplification    : 0.01
% 1.80/1.19  Subsumption          : 0.01
% 1.80/1.19  Abstraction          : 0.00
% 1.80/1.19  MUC search           : 0.00
% 1.80/1.19  Cooper               : 0.00
% 1.80/1.19  Total                : 0.42
% 1.80/1.19  Index Insertion      : 0.00
% 1.80/1.19  Index Deletion       : 0.00
% 1.80/1.19  Index Matching       : 0.00
% 1.80/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

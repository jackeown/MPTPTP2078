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
% DateTime   : Thu Dec  3 10:06:28 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  76 expanded)
%              Number of equality atoms :    5 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_38,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_33,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_31])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [B_11,A_12] :
      ( v5_relat_1(B_11,A_12)
      | ~ r1_tarski(k2_relat_1(B_11),A_12)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    ! [A_12] :
      ( v5_relat_1(k1_xboole_0,A_12)
      | ~ r1_tarski(k1_xboole_0,A_12)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_61,plain,(
    ! [A_12] : v5_relat_1(k1_xboole_0,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_4,c_59])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_45,plain,(
    ! [A_9] :
      ( v5_ordinal1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_7] : v1_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_22,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,
    ( ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_33,c_22])).

tff(c_44,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_48,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_45,c_44])).

tff(c_52,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_53,plain,(
    ~ v5_relat_1(k1_xboole_0,'#skF_1') ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.18  
% 1.71/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.18  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.71/1.18  
% 1.71/1.18  %Foreground sorts:
% 1.71/1.18  
% 1.71/1.18  
% 1.71/1.18  %Background operators:
% 1.71/1.18  
% 1.71/1.18  
% 1.71/1.18  %Foreground operators:
% 1.71/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.18  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.71/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.71/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.18  
% 1.71/1.19  tff(f_38, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.71/1.19  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.71/1.19  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.71/1.19  tff(f_37, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.71/1.19  tff(f_34, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.71/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.71/1.19  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.71/1.19  tff(f_55, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.71/1.19  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.71/1.19  tff(c_31, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.19  tff(c_33, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_31])).
% 1.71/1.19  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.71/1.19  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.19  tff(c_56, plain, (![B_11, A_12]: (v5_relat_1(B_11, A_12) | ~r1_tarski(k2_relat_1(B_11), A_12) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.71/1.19  tff(c_59, plain, (![A_12]: (v5_relat_1(k1_xboole_0, A_12) | ~r1_tarski(k1_xboole_0, A_12) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_56])).
% 1.71/1.19  tff(c_61, plain, (![A_12]: (v5_relat_1(k1_xboole_0, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_4, c_59])).
% 1.71/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.71/1.19  tff(c_45, plain, (![A_9]: (v5_ordinal1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.19  tff(c_28, plain, (![A_7]: (v1_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.19  tff(c_30, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_28])).
% 1.71/1.19  tff(c_22, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_1') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.71/1.19  tff(c_43, plain, (~v5_relat_1(k1_xboole_0, '#skF_1') | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_33, c_22])).
% 1.71/1.19  tff(c_44, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_43])).
% 1.71/1.19  tff(c_48, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_44])).
% 1.71/1.19  tff(c_52, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 1.71/1.19  tff(c_53, plain, (~v5_relat_1(k1_xboole_0, '#skF_1')), inference(splitRight, [status(thm)], [c_43])).
% 1.71/1.19  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_53])).
% 1.71/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.19  
% 1.71/1.19  Inference rules
% 1.71/1.19  ----------------------
% 1.71/1.19  #Ref     : 0
% 1.71/1.19  #Sup     : 10
% 1.71/1.19  #Fact    : 0
% 1.71/1.19  #Define  : 0
% 1.71/1.19  #Split   : 1
% 1.71/1.19  #Chain   : 0
% 1.71/1.19  #Close   : 0
% 1.71/1.19  
% 1.71/1.19  Ordering : KBO
% 1.71/1.19  
% 1.71/1.19  Simplification rules
% 1.71/1.19  ----------------------
% 1.71/1.19  #Subsume      : 0
% 1.71/1.19  #Demod        : 6
% 1.71/1.19  #Tautology    : 6
% 1.71/1.19  #SimpNegUnit  : 0
% 1.71/1.19  #BackRed      : 1
% 1.71/1.19  
% 1.71/1.19  #Partial instantiations: 0
% 1.71/1.19  #Strategies tried      : 1
% 1.71/1.19  
% 1.71/1.19  Timing (in seconds)
% 1.71/1.19  ----------------------
% 1.71/1.20  Preprocessing        : 0.28
% 1.71/1.20  Parsing              : 0.16
% 1.71/1.20  CNF conversion       : 0.02
% 1.71/1.20  Main loop            : 0.11
% 1.71/1.20  Inferencing          : 0.04
% 1.71/1.20  Reduction            : 0.03
% 1.71/1.20  Demodulation         : 0.03
% 1.71/1.20  BG Simplification    : 0.01
% 1.71/1.20  Subsumption          : 0.02
% 1.71/1.20  Abstraction          : 0.00
% 1.71/1.20  MUC search           : 0.00
% 1.71/1.20  Cooper               : 0.00
% 1.71/1.20  Total                : 0.42
% 1.71/1.20  Index Insertion      : 0.00
% 1.71/1.20  Index Deletion       : 0.00
% 1.71/1.20  Index Matching       : 0.00
% 1.71/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

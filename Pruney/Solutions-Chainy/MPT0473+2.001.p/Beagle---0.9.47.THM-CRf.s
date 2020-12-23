%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:27 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   39 (  54 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  86 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k1_relat_1(A) = k1_xboole_0
        <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_16,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_39,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_22,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_22])).

tff(c_175,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k2_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_181,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_175])).

tff(c_191,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_181])).

tff(c_29,plain,(
    ! [A_7] :
      ( v1_xboole_0(k1_relat_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_33,plain,(
    ! [A_7] :
      ( k1_relat_1(A_7) = k1_xboole_0
      | ~ v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_29,c_4])).

tff(c_197,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191,c_33])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_197])).

tff(c_208,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_209,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_294,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_relat_1(A_18))
      | ~ v1_relat_1(A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_303,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_294])).

tff(c_312,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_303])).

tff(c_34,plain,(
    ! [A_8] :
      ( v1_xboole_0(k2_relat_1(A_8))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) = k1_xboole_0
      | ~ v1_xboole_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_34,c_4])).

tff(c_319,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_312,c_38])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.19  
% 1.73/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.19  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.73/1.19  
% 1.73/1.19  %Foreground sorts:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Background operators:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Foreground operators:
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.19  
% 1.90/1.20  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 1.90/1.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.90/1.20  tff(f_54, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.90/1.20  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 1.90/1.20  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.90/1.20  tff(f_46, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 1.90/1.20  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 1.90/1.20  tff(c_16, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_relat_1('#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.20  tff(c_39, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16])).
% 1.90/1.20  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.90/1.20  tff(c_22, plain, (k1_relat_1('#skF_1')=k1_xboole_0 | k2_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.20  tff(c_62, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_39, c_22])).
% 1.90/1.20  tff(c_175, plain, (![A_14]: (~v1_xboole_0(k2_relat_1(A_14)) | ~v1_relat_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.20  tff(c_181, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_62, c_175])).
% 1.90/1.20  tff(c_191, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_181])).
% 1.90/1.20  tff(c_29, plain, (![A_7]: (v1_xboole_0(k1_relat_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.20  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.90/1.20  tff(c_33, plain, (![A_7]: (k1_relat_1(A_7)=k1_xboole_0 | ~v1_xboole_0(A_7))), inference(resolution, [status(thm)], [c_29, c_4])).
% 1.90/1.20  tff(c_197, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_191, c_33])).
% 1.90/1.20  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_197])).
% 1.90/1.20  tff(c_208, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 1.90/1.20  tff(c_209, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 1.90/1.20  tff(c_294, plain, (![A_18]: (~v1_xboole_0(k1_relat_1(A_18)) | ~v1_relat_1(A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.20  tff(c_303, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_209, c_294])).
% 1.90/1.20  tff(c_312, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_303])).
% 1.90/1.20  tff(c_34, plain, (![A_8]: (v1_xboole_0(k2_relat_1(A_8)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.20  tff(c_38, plain, (![A_8]: (k2_relat_1(A_8)=k1_xboole_0 | ~v1_xboole_0(A_8))), inference(resolution, [status(thm)], [c_34, c_4])).
% 1.90/1.20  tff(c_319, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_312, c_38])).
% 1.90/1.20  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_319])).
% 1.90/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  Inference rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Ref     : 0
% 1.90/1.20  #Sup     : 73
% 1.90/1.20  #Fact    : 0
% 1.90/1.20  #Define  : 0
% 1.90/1.20  #Split   : 1
% 1.90/1.20  #Chain   : 0
% 1.90/1.20  #Close   : 0
% 1.90/1.20  
% 1.90/1.20  Ordering : KBO
% 1.90/1.20  
% 1.90/1.20  Simplification rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Subsume      : 2
% 1.90/1.20  #Demod        : 44
% 1.90/1.20  #Tautology    : 53
% 1.90/1.20  #SimpNegUnit  : 4
% 1.90/1.20  #BackRed      : 0
% 1.90/1.20  
% 1.90/1.20  #Partial instantiations: 0
% 1.90/1.20  #Strategies tried      : 1
% 1.90/1.20  
% 1.90/1.20  Timing (in seconds)
% 1.90/1.20  ----------------------
% 1.90/1.20  Preprocessing        : 0.26
% 1.90/1.20  Parsing              : 0.15
% 1.90/1.20  CNF conversion       : 0.01
% 1.90/1.20  Main loop            : 0.18
% 1.90/1.20  Inferencing          : 0.07
% 1.90/1.20  Reduction            : 0.05
% 1.90/1.20  Demodulation         : 0.04
% 1.90/1.20  BG Simplification    : 0.01
% 1.90/1.20  Subsumption          : 0.04
% 1.90/1.20  Abstraction          : 0.01
% 1.90/1.20  MUC search           : 0.00
% 1.90/1.20  Cooper               : 0.00
% 1.90/1.20  Total                : 0.47
% 1.90/1.20  Index Insertion      : 0.00
% 1.90/1.20  Index Deletion       : 0.00
% 1.90/1.20  Index Matching       : 0.00
% 1.90/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

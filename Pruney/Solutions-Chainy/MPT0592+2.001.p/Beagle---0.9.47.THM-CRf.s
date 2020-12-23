%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:09 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   29 (  39 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  66 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( ( k1_relat_1(A) = k1_xboole_0
                & k1_relat_1(B) = k1_xboole_0 )
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_33,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k1_relat_1(A_6))
      | ~ v1_relat_1(A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_33])).

tff(c_41,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_36])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_47,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_41,c_6])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_33])).

tff(c_43,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_39])).

tff(c_51,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_43,c_6])).

tff(c_61,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_51])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:09:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.06  
% 1.60/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.07  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.07  
% 1.60/1.07  %Foreground sorts:
% 1.60/1.07  
% 1.60/1.07  
% 1.60/1.07  %Background operators:
% 1.60/1.07  
% 1.60/1.07  
% 1.60/1.07  %Foreground operators:
% 1.60/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.60/1.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.07  
% 1.60/1.07  tff(f_54, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k1_relat_1(A) = k1_xboole_0) & (k1_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t196_relat_1)).
% 1.60/1.07  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.60/1.07  tff(f_42, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 1.60/1.07  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 1.60/1.07  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.07  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.07  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.60/1.07  tff(c_14, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.07  tff(c_33, plain, (![A_6]: (~v1_xboole_0(k1_relat_1(A_6)) | ~v1_relat_1(A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.07  tff(c_36, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_33])).
% 1.60/1.07  tff(c_41, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_36])).
% 1.60/1.07  tff(c_6, plain, (![A_2]: (k1_xboole_0=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.60/1.07  tff(c_47, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_41, c_6])).
% 1.60/1.07  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.07  tff(c_12, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.07  tff(c_39, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_33])).
% 1.60/1.07  tff(c_43, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_39])).
% 1.60/1.07  tff(c_51, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_43, c_6])).
% 1.60/1.07  tff(c_61, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_51])).
% 1.60/1.07  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_61])).
% 1.60/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.07  
% 1.60/1.07  Inference rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Ref     : 0
% 1.60/1.07  #Sup     : 11
% 1.60/1.07  #Fact    : 0
% 1.60/1.07  #Define  : 0
% 1.60/1.07  #Split   : 0
% 1.60/1.07  #Chain   : 0
% 1.60/1.07  #Close   : 0
% 1.60/1.07  
% 1.60/1.07  Ordering : KBO
% 1.60/1.07  
% 1.60/1.07  Simplification rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Subsume      : 1
% 1.60/1.07  #Demod        : 10
% 1.60/1.07  #Tautology    : 8
% 1.60/1.07  #SimpNegUnit  : 1
% 1.60/1.07  #BackRed      : 4
% 1.60/1.07  
% 1.60/1.07  #Partial instantiations: 0
% 1.60/1.07  #Strategies tried      : 1
% 1.60/1.07  
% 1.60/1.07  Timing (in seconds)
% 1.60/1.07  ----------------------
% 1.63/1.08  Preprocessing        : 0.25
% 1.63/1.08  Parsing              : 0.14
% 1.63/1.08  CNF conversion       : 0.01
% 1.63/1.08  Main loop            : 0.08
% 1.63/1.08  Inferencing          : 0.03
% 1.63/1.08  Reduction            : 0.02
% 1.63/1.08  Demodulation         : 0.02
% 1.63/1.08  BG Simplification    : 0.01
% 1.63/1.08  Subsumption          : 0.01
% 1.63/1.08  Abstraction          : 0.00
% 1.63/1.08  MUC search           : 0.00
% 1.63/1.08  Cooper               : 0.00
% 1.63/1.08  Total                : 0.35
% 1.63/1.08  Index Insertion      : 0.00
% 1.63/1.08  Index Deletion       : 0.00
% 1.63/1.08  Index Matching       : 0.00
% 1.63/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
